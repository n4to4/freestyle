/*
 * Copyright 2017 47 Degrees, LLC. <http://www.47deg.com>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package freestyle

import cats.{ Applicative, Monad }
import scala.annotation.{compileTimeOnly, StaticAnnotation}
import scala.language.experimental.macros
import scala.reflect.macros.blackbox
import scala.reflect.internal._

trait EffectLike[F[_]] {
  final type OpSeq[A] = FreeS[F, A]
  final type OpPar[A] = FreeS.Par[F, A]
}

@compileTimeOnly("enable macro paradise to expand @free macro annotations")
class free extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro free.impl
}

object free {

  private[this] val onlyTraitMessage =
    "The `@free` macro annotation can only be applied to either a trait or an abstract class that has no companion"

  def impl(c: blackbox.Context)(annottees: c.Expr[Any]*): c.universe.Tree = {
    import c.universe._
    import internal.reificationSupport._

    def fail(msg: String) = c.abort(c.enclosingPosition, msg)

    def gen(): Tree = annottees match {
      case List(Expr(effectTrait: ClassDef)) =>
        if (effectTrait.mods.hasFlag(Flag.TRAIT | Flag.ABSTRACT))
          q"""
            ${mkEffectTrait(effectTrait.duplicate)}
            ${mkEffectObject(effectTrait.duplicate)}
          """
        else fail(s"Invaled @free usage. $onlyTraitMessage")
      case _ => fail(s"Invalid @free usage. $onlyTraitMessage")
    }

    // OP is the name of the Root trait of the Effect ADT
    lazy val OP = TypeName("Op")
    // MM Is the target of the Handler's natural Transformation
    lazy val MM = freshTypeName("MM$")
    // LL is the target of the Lifter's Injection
    lazy val LL = freshTypeName("LL$")
    // AA is the type parameter inside Op, used to avoid
    lazy val AA = freshTypeName("AA$")
    lazy val FF = freshTypeName("FF$")

    def isRequestDef(tree: Tree): Boolean = tree match {
      case q"$mods def $name[..$tparams](...$paramss): OpSeq[..$args]" => true
      case q"$mods def $name[..$tparams](...$paramss): OpPar[..$args]" => true
      case _ => false
    }

    def mkEffectTrait(cls: ClassDef): ClassDef = {

//      def reqsToFreeS( tree: Tree) : Tree = tree match {
//        case DefDef(mods, name, tparams, vparams, tyRes, body) =>
//          val ntyRes = tyRes match {
//            case tq"OpSeq[..$args]" => tq"FreeS    [$FF, ..$args]"
//            case tq"OpPar[..$args]" => tq"FreeS.Par[$FF, ..$args]"
//            case tt => tt
//          }
//          DefDef(mods, name, tparams, vparams, ntyRes, body)
//
//        case x => x
//      }

      val ffTParam: TypeDef = {
        val wildcard = TypeDef(Modifiers(Flag.PARAM), typeNames.WILDCARD, List(), TypeBoundsTree(EmptyTree, EmptyTree))
        TypeDef(Modifiers(Flag.PARAM), FF, List(wildcard), TypeBoundsTree(EmptyTree, EmptyTree))
      }
      val ClassDef(mods, name, tparams, Template(parents, self, body)) = cls

      val ntparams = ffTParam :: tparams
      val nparents = parents :+ tq"freestyle.EffectLike[$FF]"

      ClassDef(mods, name, ntparams, Template(nparents, self, body))
    }

    class Request(reqDef: DefDef) {

      import reqDef.tparams

      val reqImpl = TermName(reqDef.name.toTermName.encodedName.toString)

      // Name of the Request ADT Class
      private[this] val Req: TypeName = TypeName(reqDef.name.toTypeName.encodedName.toString.capitalize + "OP")
      private[this] val Res = reqDef.tpt.asInstanceOf[AppliedTypeTree].args.last

      val params: List[ValDef] = reqDef.vparamss.flatten

      def handlerCase: CaseDef  = {
        val ReqC = Req.toTermName
        if (params.isEmpty)
          cq"$ReqC() => $reqImpl"
        else {
          // filter: !v.mods.hasFlag(Flag.IMPLICIT)
          val ffs = params.map( v => q"l.${v.name}")
          val uss = params.map( v => pq"_")
          cq"l @ $ReqC(..$uss) => $reqImpl(..$ffs)"
        }

      }

      def handlerDef: DefDef =
        if (params.isEmpty)
          q"protected[this] def $reqImpl[..$tparams]: $MM[$Res]"
        else
          q"protected[this] def $reqImpl[..$tparams](..$params): $MM[$Res]"


      def mkRequestClass(effTTs: List[TypeDef]): ClassDef = {
        // Note: Effect trait type params are added to the request case class because its args may contain them
        val TTs = effTTs ++ tparams
        if (params.isEmpty)
          q"case class $Req[..$TTs]() extends $OP[$Res]"
        else
          q"case class $Req[..$TTs](..$params) extends $OP[$Res]"
      }

      def raiser: DefDef = {
        val injected = {
          /*filter: if !v.mods.hasFlag(Flag.IMPLICIT)*/
          val args = params.map(_.name)
          val ReqC = Req.toTermName
          q"FreeS.inject[$OP, $LL]( $ReqC[..${tparams.map(_.name)} ](..$args) )"
        }

        val tpt = reqDef.tpt.asInstanceOf[AppliedTypeTree]
        val (liftType, impl) = tpt match {
          case tq"OpSeq[$aa]" => (tpt, q"FreeS.liftPar($injected)" )
          case tq"OpPar[$aa]" => (tpt, injected )
          case _ =>
            fail(s"unknown abstract type found in @free container: $tpt : raw: ${showRaw(tpt)}")
        }

        q"override def ${reqDef.name}[..$tparams](...${reqDef.vparamss}): $liftType = $impl"
      }
    }

    def mkEffectObject(effectTrait: ClassDef) : ModuleDef= {

      val requests: List[Request] = effectTrait.impl.
        filter( t => isRequestDef(t)).
        map( p => new Request(p.asInstanceOf[DefDef]))

      val Eff: TypeName = effectTrait.name
      val TTs = effectTrait.tparams
      val tns = TTs.map(_.name)
      // For Macro Hygiene: we want no function param to shadow those from the @free triat
      val xx = freshTermName("xx$")

      q"""
        object ${Eff.toTermName} {

          import cats.arrow.FunctionK
          import cats.free.Inject
          import freestyle.FreeS

          sealed trait $OP[$AA] extends scala.Product with java.io.Serializable
          ..${requests.map( _.mkRequestClass(TTs))}

          trait Handler[$MM[_], ..$TTs] extends FunctionK[$OP, $MM] {
            ..${requests.map( _.handlerDef )}

            override def apply[$AA]($xx: $OP[$AA]): $MM[$AA] = $xx match {
              case ..${requests.map(_.handlerCase )}
            }
          }

          class To[$LL[_], ..$TTs](implicit $xx: Inject[$OP, $LL]) extends $Eff[$LL, ..$tns] {
              ..${requests.map(_.raiser)}
          }

          implicit def to[$LL[_], ..$TTs](implicit $xx: Inject[$OP, $LL]):
              To[$LL, ..$tns] = new To[$LL, ..$tns]

          def apply[$LL[_], ..$TTs](implicit $xx: $Eff[$LL, ..$tns]): $Eff[$LL, ..$tns] = $xx

        }
      """
    }

    gen()
  }
}
