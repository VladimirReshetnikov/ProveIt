# Concise axiomatizations of iPRA — the unified article

`concise_ipra.pdf` (503 pages) merges the written mathematics of every
research package that was delivered to this directory, with the material
deduplicated: each definition, rule inventory, theorem and proof is stated
once, in one notation. Statements that the packages leave unproved are
collected in the "Further questions" section that closes each chapter.

| File | Content |
| --- | --- |
| `concise_ipra.tex` | main file; `\input`s the preamble and the chapters |
| `preamble.tex` | the only packages and macros the chapters use |
| `chapters/ch00_front.tex` | title, abstract, introduction, conventions |
| `chapters/ch01_base.tex` … `ch11_cert.tex` | the eleven chapters |
| `chapters/appendix_packages.tex` | each package with the chapters that draw on it |

Chapters and their label prefixes: `base` the base theories and the bridge;
`kern` refinements of the eight rules; `guard` guards and public languages;
`comp` computation, equality and normal forms; `claus` clause calculi;
`disch` discharge of a witness and restricted equality rules; `wit`
introduction without a supplied witness; `seed` recursors with a built-in
seed; `ctr` canonical and counter-aware recursors; `obs` obstructions;
`cert` certificates and checkers. Every `\label` carries the prefix of its
chapter. Shared material has one owner: the structural properties of the
native core belong to `base`, the rule Eval and normal forms to `comp`,
clause calculi to `claus`, guards and the selector criterion to `guard`,
term languages of other recursors to `ctr`; other chapters cite them.

New proposals that arrive in `docs/incoming/` are integrated into the
chapter where they belong, not filed as separate reports; their Python
artifacts are stored apart from the article.

Build from this directory, three passes (the table of contents and the
cross-references settle on the third):

    lualatex -interaction=nonstopmode concise_ipra.tex
    lualatex -interaction=nonstopmode concise_ipra.tex
    lualatex -interaction=nonstopmode concise_ipra.tex
