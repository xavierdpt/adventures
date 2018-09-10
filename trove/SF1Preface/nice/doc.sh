#!/bin/bash
if [ ! -d output ]; then mkdir output ; fi
touch output/something
rm output/*
cd output
cp ../nice.v . -f
coqc nice.v
coqdoc nice.v --html -s  --no-index
