#!/bin/bash

make -f .CoqMakefile.d src/ModelCheck/RealWorldStepLemmas.vo -Bnd | make2graph | dot -Tpdf -o deps.pdf

# ( echo "digraph interval_deps {" ;
#   echo "node [shape=ellipse, style=filled, URL=\"html/Interval.\N.html\", color=black];";
# #  ( cd src; coqdep -R . Interval $VFILES ) |
#   ( coqdep -f _CoqProject ) |
#     sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' |
#     while read src dst; do
#       color=$(echo "$src" | sed -e 's,Real.*,turquoise,;s,Interval[.].*,plum,;s,Integral.*,lightcoral,;s,Poly.*,yellow,;s,Float.*,cornflowerblue,;s,Eval.*,green,;s,[A-Z].*,white,')
#       echo "\"$src\" [fillcolor=$color];"
#       for d in $dst; do
#         echo "\"$src\" -> \"${d%.vo}\" ;"
#       done
#     done;
#   echo "}" ) | tred > deps.dot
# dot -T png deps.dot > deps.png
# dot -T cmap deps.dot | sed -e 's,>$,/>,' > deps.map
