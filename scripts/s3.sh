# Based on https://gist.github.com/chrismdp/6c6b6c825b07f680e710

S3KEY=${AWS_ACCESS_KEY}
S3SECRET=${AWS_SECRET_KEY}  # pass these in
S3BUCKET=${AWS_S3_BUCKET}

thepath=$1

function putS3
{
  path=$1
  file=$2
  aws_path=$3
  date=$(date +"%a, %d %b %Y %T %z")
  acl="x-amz-acl:public-read"
  content_type='application/x-compressed-tar'
  string="PUT\n\n$content_type\n$date\n$acl\n/${S3BUCKET}${aws_path}$file"
  signature=$(echo -en "${string}" | openssl sha1 -hmac "${S3SECRET}" -binary | base64)
  curl -X PUT -T "$path/$file" \
    -H "Host: ${S3BUCKET}.s3.amazonaws.com" \
    -H "Date: $date" \
    -H "Content-Type: $content_type" \
    -H "$acl" \
    -H "Authorization: AWS ${S3KEY}:$signature" \
    "https://${S3BUCKET}.s3.amazonaws.com${aws_path}$file"
}

for file in "$thepath"/*; do
  putS3 "$thepath" "${file##*/}" "/debug/heapdump/"
done

