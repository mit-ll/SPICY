#!/bin/zsh

sed -i '/Massachusetts/d' src/**/*(.) protocols/**/*(.) _CoqProject LICENSE.md README.md Makefile
sed -i '/MIT Proprietary/d' src/**/*(.) protocols/**/*(.) _CoqProject LICENSE.md README.md Makefile
