# Coarse Classes Without Least Turing Representatives

Research draft prepared for Vladimir Reshetnikov, 18 September 2026.

## Start here

Read `coarse_degree_attack.pdf` (20 pages). Its editable source is
`coarse_degree_attack.tex`. The original supplied report is retained, unchanged,
in `input/turing_degrees_unified.tex`.

The selected target is **C1**: must every nonuniform coarse-equivalence class
contain a representative of least Turing degree?

**Answer: no.** The report gives a complete conventional proof and then develops
stronger exact-pair and prescribed-core results. This is not presented as a newly
resolved literature-open problem: the base negative answer already follows from
older published cone-avoidance results. The publication priority of the stronger
formulations has not been established.

## Mathematical results

Write C_X for the binary coarse descriptions of X, L(Y) for the sets Turing
computable from Y, and K_X for the intersection of L(D) over all D in C_X.

1. For every X there is a density-zero modification D of X such that
   L(X) intersect L(D) = K_X. More generally, with any fixed Y in place of the
   first X, a dense G-delta subset of C_X has the prescribed common lower cone
   L(Y) intersect K_X.
2. An explicitly defined complete c.e. set X, of degree 0', has K_X equal to the
   computable sets but has no computable coarse description. The exact partner
   D forms a Turing minimal pair with X, in the same *uniform* coarse class.
   Therefore neither the uniform nor the nonuniform class has a least Turing
   representative. Necessarily D is not computable from 0'.
3. Every C_X contains a Cantor family of pairwise Turing-incomparable members
   whose distinct pairs have common lower cone exactly K_X.
4. For every oracle A, an explicitly specified A-c.e. set Y_A has degree A',
   has K_(Y_A) = L(A), and has no representative of degree at most deg(A).
   Its uniform and nonuniform coarse classes have no least representative,
   although deg(A) is their greatest common lower bound. A Cantor family in
   the class has pairwise Turing meet deg(A).
5. A nonuniform coarse class of a binary target has a least Turing
   representative exactly when it is equivalent to a dyadic block coarsening
   I(A) of some set A. A principal core alone is not sufficient.

The arguments allow total natural-number-valued representatives as in C1.
They do **not** settle the effective-dense question C2 and do **not** establish
absence of minimal representatives.

## Files

- `coarse_degree_attack.tex` and `.pdf`: full article, proofs, and references.
- `checks/check_finite_lemmas.py`: executable exact-arithmetic finite checks.
- `checks/results.json` and `checks/results.txt`: recorded test output.
- `proof_audit.md`: the delicate proof obligations and evidence boundaries.
- `sources.md`: primary sources, theorem locations, and the status correction.
- `build.sh`: three-pass LaTeX build with a check for unresolved references.
- `input/turing_degrees_unified.tex`: the unchanged user-supplied source.

## Reproduce

From this directory:

```sh
python3 checks/check_finite_lemmas.py --output checks/results.json
./build.sh
```

The Python script needs only the standard library (Python 3.10 or later).
The build needs `pdflatex` and the ordinary packages named in the TeX preamble
(e.g. TeX Live). No external figures, proprietary assets, or font files are
included. Temporary build products go into `_build/`.

The recorded run passed **504,457 finite checks** using exact rational and
integer arithmetic. These cover finite density norms, triangle inequalities,
splicing, dyadic counts, majority bounds, and the gated enumeration on a declared
finite toy program family. The toy family is not a universal enumeration.

**These are not formal proofs of the infinite theorems.** No Lean verification,
external mathematical review, or first-publication certification is claimed.
The category-selected exact partners and perfect families are not asserted to
be effectively computable. Their existence is justified by the written proofs.

## Historical attribution

Gerdes's 2025 Question 7 contains the least-representative question. HJKS's
*Coarse Reducibility and Algorithmic Randomness* (JSL 2016), especially Theorems
3.7 and 4.3, gives earlier facts that imply the negative coarse answer. The
article re-proves the compactness consequence by a local recovery argument.
The Cantor-set step is attributed to Mycielski, with the needed special case
proved in the appendix. See `sources.md` for exact references.
