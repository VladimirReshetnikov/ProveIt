# Cyclic symmetry at the ultraexacting boundary

An exact finite-label criterion, a sharp transversal obstruction, and an
I0-equiconsistent positive enrichment.

Prepared for Vladimir Reshetnikov, 18 September 2026.

## Contents

- `Cyclic_Symmetry_Ultraexacting.pdf` — the complete research continuation.
- `Cyclic_Symmetry_Ultraexacting.tex` — self-contained LaTeX source, including
  its bibliography. No separate image assets or bibliography database are needed.
- `finite_symmetry_audit.py` — reproducible finite combinatorial checks, using
  the Python standard library only.
- `audit_results.json` — recorded structured audit results.
- `audit_log.txt` — the same recorded run in console-output form.
- `Makefile` — commands for rebuilding the PDF and rerunning the audit.

The source uses the supplied reports' `newpxtext` / `newpxmath` typography,
page geometry, theorem style, and Forest/Olive/Muted/Sage/Pale palette.
No separate font binaries are distributed.

## Main mathematical contributions

1. **Exact finite-label classification.** For an ultraexacting cardinal lambda,
   a subgroup Gamma of S_m, and a finite nonempty Gamma-set F, an equivariant,
   finite-modification-invariant rule on ordered tuples of distinct cofinal
   omega-subsets modulo finite difference exists in OD_(V_lambda) if and only if
   each individual element of Gamma fixes a label in F. The sufficiency proof
   uses a single parameter of rank below omega + 10 and works in ZFC at every
   uncountable cardinal of countable cofinality. The central lemma proves that
   stabilizers of admissible incidence words modulo shifted tails are cyclic.

2. **A positive five-label example.** For S_3, the disjoint union of the natural
   three-point action and the two-point sign action supports a rule which either
   distinguishes a member of an unordered triple or chooses a cyclic orientation.
   Neither pure operation is OD_(V_lambda) at an ultraexacting cardinal. Five is
   the minimum number of labels for an S_3 action passing all elementwise
   fixed-point tests without possessing a global fixed point. Both output types
   occur on at least lambda triples for every low-rank-definable mixed rule.

3. **A sharp representative-transversal obstruction.** Every complete
   T subset D_lambda in OD_(V_lambda) has at least lambda equivalence classes q
   with |T intersect q| = lambda. Thus it is impossible for all fibres to be
   nonempty and individually smaller than lambda, even with no uniform bound
   below lambda. Countable fibres are excluded. The fibre-width threshold lambda
   is exact. A local version forbids a preserving rank embedding even without
   a definability assumption on T.

4. **Consistency calibration.** Known HOD-coding forcing makes the positive
   mixed rule ordinal definable while preserving ultraexactingness. The new
   positive and negative conclusions, together with V_lambda subset HOD, form
   a theory equiconsistent with ZFC + I0. The base I0/ultraexacting equiconsistency
   is an imported theorem, not a new theorem proved from scratch here.

The additional coherent-relabelling corollary explains why multiple increasing
maps cannot realize a noncyclic permutation group modulo finite change on one
common tuple. Different permutations in the embedding obstruction may require
different tuples.

## External inputs and status

The large-cardinal imports are from Aguilera, Bagaria, Goldberg, and Luecke,
*Large cardinals beyond HOD*, arXiv:2509.10254v1:

- Theorem 3.1: ordinal-definable predicate characterization of ultraexactingness.
- Proposition 3.9: HOD coding preserving ultraexactingness.
- Theorem 4.5: equiconsistency with I0.

The proofs also use the local Kunen inconsistency. An explicit reference for
that formulation is Hamkins, Kirmayer, and Perlmutter, *Generalizations of the
Kunen inconsistency*, arXiv:1106.1951v2, page 3, footnote 1. The bibliography
identifies both supplied reports separately.

These inputs were checked against the public primary sources. The new arguments
are conventional mathematical proofs, with explicit rank-domain, parameter,
finite-shift, and singular-cardinal checks. They have not been refereed or
formally verified in Lean or another proof assistant. The finite computation
is supplementary: it does not prove the infinite-word theorem or establish
large-cardinal consistency.

Novelty is claimed only relative to the supplied reports. No exhaustive
literature-wide priority claim is made. No standard large-cardinal axiom is
shown inconsistent. The report does not settle the cover-exacting problem above
a strongly compact cardinal, or the question about countable families of
finite-subset selectors. Families of representative transversals are a
different object. Without the additional coding hypothesis, the positive
construction is only asserted to belong to OD_(V_lambda), not necessarily OD.

## Build the PDF

A reasonably complete TeX Live or MiKTeX installation with the packages named
in the preamble is sufficient. The source was built with pdfLaTeX via latexmk.

```sh
make pdf
```

Equivalent command:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error Cyclic_Symmetry_Ultraexacting.tex
```

Without latexmk, run `pdflatex -interaction=nonstopmode -halt-on-error` on the
source three times so that the contents and cross-references settle.

## Reproduce the finite audit

Python 3.10 or later is recommended. Do not use Python's `-O` flag: the audit
intentionally uses assertions and rejects optimized execution.

```sh
python3 finite_symmetry_audit.py --max-period 5 --output audit_results.json
```

The recorded run passed. Deterministic counts for `--max-period 5` are:

- 19,607 raw period words; 17,484 admissible words.
- 3,619 distinct admissible tail patterns.
- 21,714 equivariance checks and 17,478 rotation checks.
- 5,912 permutation-realization checks, for all permutations of 2 through 7 labels.
- Tested stabilizer orders: 1 (3,588 patterns), 2 (27), 3 (4), all cyclic.

The elapsed time field depends on the machine. The command `make audit` also
updates `audit_log.txt`. Increasing `--max-period` increases the exhaustive
search cost rapidly; the supported range is 1 through 7.

The finite program uses lexicographic selection among finite periodic patterns.
It does not implement a well-order of arbitrary reals or an effective infinite
version of the set-theoretic construction.
