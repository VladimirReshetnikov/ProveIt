# Theta lifts and the zeros of Dirichlet L-functions

This archive contains an English mathematical exposition of the proof of Levent Alpöge with Claude. It combines the explanatory guide in ProveIt with Ye Yu's natural-language account and ties the argument to a fixed revision of the readable Lean package.

## Read or rebuild

Open **dirichlet_zeros.pdf**. The PDF has a linked contents page, links between equations and sections, and links to the cited source modules. Section 8 combines the three arithmetic theorems. Sections 9–11 give the analytic deduction.

The master file is **dirichlet_zeros.tex**. The eight other TeX files are the editable chapters and appendices. Keep them in the same directory and run a standard TeX Live installation with

    latexmk -pdf -interaction=nonstopmode -halt-on-error dirichlet_zeros.tex

Three runs of pdflatex also suffice. The diagram is drawn directly by the TeX source.

## Reproduce the checks

**check_examples.py** checks the progression selector, finite Fourier path count, elliptic-curve derivatives, rational projector, and exceptional-prime exponent with exact arithmetic. It needs only Python 3.

    python3 check_examples.py

**source-map.tsv** lists 225 declaration locations in 97 Lean files. Each row has a mathematical role, declaration name, source-relative path, line number, Git blob hash and immutable URL. The script below verifies the actual bytes and the declaration lines against a local checkout.

    git clone --filter=blob:none --no-checkout https://github.com/VladimirReshetnikov/ProveIt.git ProveIt
    git -C ProveIt sparse-checkout init --cone
    git -C ProveIt sparse-checkout set Analysis/GeneralizedRiemannHypothesis/Lean/grh
    git -C ProveIt checkout --detach 7a5bb1e051e4bad127bafe90abbea19764778e32
    python3 check_sources.py ProveIt/Analysis/GeneralizedRiemannHypothesis/Lean/grh

**changes-from-checked-tree.tsv** lists the 20 paths whose contents differ between the independently checked upstream readable package at 72fead10 and the current ProveIt package used here. Column one is Git's modification flag. Column two is the path from the package root. The local source-map and arithmetic checks have a different purpose from building Lean and replaying exported proofs.

To build that pinned ProveIt Lean package in an environment with the Lean v4.35.0 toolchain and dependencies available, run the following in its grh directory.

    lake exe cache get
    lake build
    lake env lean scripts/PrintAxioms.lean
    lake env leanchecker Main

## Sources and attribution

- ProveIt guide and Lean package at commit **7a5bb1e051e4bad127bafe90abbea19764778e32**. The package tree is **9603e445408c4ff6915133cafd89102bcfd2d991**.
- Ye Yu's English outline and correspondence at **5edf43ce39c068fec64e0cc122e9cbdcec343b24** in sdyy1990/riemann-hypothesis. The outline credits Gemini assistance. Its license notice is included.
- Sutherland's public build and independent checking record concerns lsernau/grh-lean at **72fead102f663d5c7a407964a13dc0cf9d977207**, whose grh subtree is **2e133df63d7f4da6b3059c4195324f8e9187ba73**. See <https://math.mit.edu/~drew/shortgrh/>.
- The original mathematical proof is credited to Levent Alpöge with Claude. The readable edition credits Claude with its Lean text and documentation. The PDF gives full source links. Original project notices are in attribution/.
