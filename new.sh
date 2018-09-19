#!/bin/bash
if [ "x$1" = "x" ]; then
	echo "Please specify filename"
	exit 1
fi
if [ "x$2" = "x" ]; then
	echo "Please specify title"
	exit 1
fi
d=`date +"%Y-%M-%d"`
name="$d-$1.markdown"
fullpath="./content/_posts/$name"
echo "---" >>"$fullpath"
echo "layout: post" >>"$fullpath"
echo "title: \"$2\"" >>"$fullpath"
echo "date: $date 08:00:00 +0200" >>"$fullpath"
echo "---" >>"$fullpath"
echo "$fullpath created"
