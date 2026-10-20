# K223 research article

The editable article is `report.tex`; the verified compiled version is `report.pdf`.
The article contains 11 Letter-size pages, including references.

Build with a standard TeX Live installation:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Alternatively run `sh build.sh`. The wrapper also supports the original research
container's optional format and font locations. A custom format directory can be
specified through `K223_TEXFORMATS`; ordinary installations need no override.

Required packages are geometry, fontenc, lmodern, amsmath, amssymb, amsthm,
booktabs, array, hyperref, and xcolor. No generated figure files are required.

The machine and certificate replay are separate from typesetting. From the
parent packet root, run:

    python3 -B portable/reproduce.py --full --output-dir OUT

OUT must be a new or empty directory outside the immutable `portable/` subtree.
