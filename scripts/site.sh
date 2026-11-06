#!/bin/sh
# The GitHub Pages site of unit-informath (docs/, published from main):
# the proof pages, the informal document and the slides, made from Unit's
# sag/gcddomain.  Needs ../unit, ../informath built, and INFORMATH_ROOT.
#
#   INFORMATH_ROOT=../informath sh scripts/site.sh

set -e
cd "$(dirname "$0")/.."
mkdir -p out docs

# Unit -> Dedukti
"$(cabal list-bin unit2dk)" ../unit/sag/gcddomain/All.seg -dkgf=out/gcddomain.dkgf > out/gcddomain.dk 2> out/gcddomain.log
tail -1 out/gcddomain.log

# the informal document
python3 scripts/informal_doc.py out/gcddomain.dk out/gcddomain.dkgf gcddomain-view.dkgf out/gcddomain-doc.tex
(cd out && pdflatex -interaction=nonstopmode gcddomain-doc.tex > /dev/null && pdflatex -interaction=nonstopmode gcddomain-doc.tex > /dev/null) || true

# the proof pages
P=Theory.GcdDomain.Divisibility
G=Theory.GcdDomain.Gcd
python3 scripts/proof_sample.py out/gcddomain.dk out/gcddomain.dkgf gcddomain-view.dkgf ../unit/sag/gcddomain \
  out/proofs.html $P.div-refl $P.div-of-zero $P.div-trans $G.euclid -text-auto=../unit/doc/gcddomain.tex
T=Theory.Gauss.Direct.Tail
O=Theory.Gauss.Direct.PrimStep.One
S=Theory.Gauss.Direct.PrimStep
python3 scripts/proof_sample.py out/gcddomain.dk out/gcddomain.dkgf gcddomain-view.dkgf ../unit/sag/gcddomain \
  out/proofs-gauss.html $T.eq $T.dx $T.dxy $T.result $O.ht $O.tc $O.ct $O.result $S.cpA $S.db $S.result \
  -text-auto=../unit/doc/gcddomain.tex

cp out/proofs.html out/proofs-gauss.html out/gcddomain-doc.pdf doc/unit-informath-slides.pdf docs/
rm -rf scripts/__pycache__
echo "-> docs/: index.html $(cd docs && ls | grep -v index.html | tr '\n' ' ')"
