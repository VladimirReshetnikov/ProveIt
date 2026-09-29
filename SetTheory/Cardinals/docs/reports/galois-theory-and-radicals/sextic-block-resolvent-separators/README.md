# Finite Separators and Discriminant Factorizations for Sextic Block Resolvents

**A sharp 196-point guarantee and a bounded replacement for ProveIt's separating-invariant search**

A research report of ProveIt's research-report collection, dated 28 September
2026, built from one manuscript ("Prepared for Vladimir Reshetnikov"). It
continues the formal project `Algebra/PolynomialFormulas` (the Lean/Rocq
sextic radical-solvability decision), but it is not part of that
development.

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| 01 | batches 40–41 intake, batch 41, manuscript 03 | `ProveIt_Finite_Sextic_Separators` (main file `article.tex`, 24-page Letter PDF, 11 files) | `e2b1f016a` | `9754e8360` | `eaf787d50` | the whole article, Sections 1–17 and Appendices A–B |

The pin is the full commit `e2b1f016a94102663f12b970e6dd434229f90d01` (the
article's `\snapshot` macro). `Algebra/PolynomialFormulas` has no commit
between the pin and the placement commit, so every repository statement of
the article was checked against the tree it describes.

**Status: AI-assisted, unrefereed, not formalized.** No statement of this
report has a Lean or Rocq proof; that it sits next to a formal project
confers no formal status on it.

```
article.tex                     the report, standalone LaTeX with an internal bibliography
article.pdf                     the compiled report, 28 pages, US Letter (unnumbered title page,
                                contents page 1, text pages 2–27)
README.md                       this guide
code/verify.py                  exact checks (SymPy 1.14.0 for four symbolic identities; the rest
                                integer arithmetic): counts, discriminant identities, symmetry,
                                the 462-subset sample, fixed-parameter counterexamples
code/sharpness_certificate.py   standard-library generator and checker of the modular Bézout
                                certificate for the roots (1, 4, 10, 23, 51, 109)
code/build.sh                   the delivered PDF build script (does not work from code/; see below)
data/verification.json          recorded output of verify.py
data/sharpness_certificate.json recorded certificate: E mod 1000003 (degree 195) and cofactors A, B
data/environment.json           the delivery's record of its software versions and runs
data/requirements.txt           the pin sympy==1.14.0
```

Every file under `code/` and `data/` is byte-identical to the delivery. The
delivered `README.md` and PDF are not shipped: this README replaces the
first, and `article.pdf` is a build of the written text. The delivered
checksum file `SHA256SUMS` (10 of 10 verified at placement) is not shipped.
The delivery's layout was flat with a `checks/` directory; the mapping is
`build.sh` → `code/build.sh`, `requirements.txt` → `data/requirements.txt`,
and `checks/X` → `data/X` for its three JSON files.

## Labels and numbering

Every label in `article.tex` carries the prefix `sbr:`. The 73 delivered
labels keep their names after the prefix; the write added four,
`sbr:sec:notation`, `sbr:sec:provenance`, `sbr:sec:formal` and
`sbr:sec:nonclaims` (77 in total). Every theorem, equation and section
number is that of the delivered 24-page PDF: the write adds unnumbered
`[write]` notes, one footnote, subsections 1.3–1.6 at the end of Section 1,
and three bibliography entries, and the `.aux` numbers of all 73 delivered
labels were compared with a build of the delivered text. Two corrections of
form: the title page's vertical spacing was tightened to fit its provenance
line, and the environments sharing the theorem counter use alias counters
(`aliascnt`), because in the delivered build every `\cref` to a lemma,
proposition or corollary printed "theorem".

## Setting and notation

`f` is a sextic with distinct roots `α_1, …, α_6` in a characteristic-zero
field; `P` ranges over the 15 pair partitions (matchings), `T` over the 10
triple partitions. The complete descriptors are
`D_B(u, v) = ∏_{B ∈ 𝓑} (v − p_B(u))` with `p_B(u) = ∏_{i ∈ B} (u − α_i)`.
On the curve `(u, v) = (t, 2t²)` they become
`D_P = K_2(t) − 2t² h_P(t)` and `D_T = K_3(t) − 2t² k_T(t)`, with
`h_P = A_P t² + B_P t − C_P` and `k_T = a_T t − b_T`.

Section 1.3 of the article tabulates every overloaded letter. The readings
most likely to mislead:

- **Lean's coordinate order.** Lean's parameter is a pair `x : Fin 2 → ℕ`;
  in `bivariateDescriptor`, `X 0` is the block variable `v` and `X 1` the
  root variable `u`. True: `x(0) = 2t²`, `x(1) = t`. False: the reverse.
  Checked at the write against the definitions and by a separate script.
- **Code versus parameter.** Lean's `Nat.find` runs over `Primcodable`
  codes decoded by `parameterAt`, not over `t`; 196 bounds `t`.
- **196 versus `N_int`.** 196 is sharp for arbitrary sets of distinct
  nonzero complex test values; for the initial integer interval only
  `8 ≤ N_int ≤ 196` is proved.
- `p_B` is a block's root polynomial, `p_b = α_i α_j` a pair product, `p`
  the prime 1000003. `R_{2,f}`, `R_{3,f}` are resolvents, `R = 1 + H` a
  root bound; neither is the sibling report's `R_{p,k,f}`, and `h_P` is not
  its `h_A(u)`. In Lemma 5.1 the letters `a, …, f` are root values. Degrees
  30, 120, 45, 195 are degrees in `t`; 30, 240, 90, 360 are homogeneous
  degrees in roots and `t`.

No symbol was renamed and no normalization changed.

## What the report claims

Theorem numbers are those of `article.pdf` (and of the delivered PDF).

- **Propositions 3.1, 3.2 (compression).** Pair descriptors are determined
  by the quadratic `h_P(t)`, triple descriptors by the linear `k_T(t)`, and
  the curve `(t, 2t²)` transports them affinely (common multiplier `−2t²`).
- **Lemmas 4.1, 5.1, 5.2.** Of the 105 pairs of matchings, 45 share a block
  and differ by a scalar times `q_e(t) = t² + s_e t − p_e`; 60 are
  block-disjoint. The 45 pairs of triple partitions correspond to pairs of
  disjoint root pairs, with linear factor `ℓ_{e,e'}`.
- **Proposition 6.2 (exact failure test).** `Q_f`, `U_f`, `L_f` are
  symmetric with integer coefficients, of `t`-degrees 30, ≤ 120, ≤ 45, and
  `E_f(t) = Q_f U_f L_f (t) ≠ 0` iff both `P ↦ h_P(t)` and `T ↦ k_T(t)` are
  injective (sign argument, Lemma 6.1).
- **Theorem 7.1.** `disc_Z R_{2,f} = disc(f)^6 Q_f^6 U_f^2` and
  `disc_Z R_{3,f} = disc(f)^3 L_f^2` as polynomial identities;
  Corollary 7.2 on square classes.
- **Theorem 8.4 (generic three-factor theorem).** Over
  `Q(e_1, …, e_6)`, `Q`, `U`, `L` are irreducible of exact `t`-degrees 30,
  120, 45, pairwise nonassociate; `E` is squarefree of degree 195 with
  nonzero constant term.
- **Theorem 9.1.** Among any 196 distinct nonzero test values, in
  particular `1, …, 196`, one separates both families and both original
  descriptors on the curve (151 suffice for pairs alone, 46 for triples).
- **Theorem 9.2 (sharpness).** Some split integer sextics have exactly 195
  distinct nonzero bad complex parameters; the roots
  `(1, 4, 10, 23, 51, 109)` are a certified example (Section 9.1, modular
  Bézout identity modulo 1000003).
- **Proposition 9.3.** `8 ≤ N_int ≤ 196`, the lower bound from the roots
  `(−3, 0, 1, 2, 3, 4)`. **Proposition 9.4.** No single positive integer
  separates the pair family of every split sextic.
- **Theorem 10.3.** For an irreducible rational sextic and a simultaneous
  separator `t`, `f` is solvable by radicals iff one of the two specialized
  resolvents has a rational root (classical criterion, reproved).
- **Theorem 11.1.** A bounded coefficient-only procedure (monicization,
  bounded factor boxes, the quintic branch, a scan of `t = 1, …, 196`,
  bounded integer-root tests) has a primitive-recursive realization and
  decides all-roots radical solvability of integer sextics.
- **Theorem 12.1.** `t_* = 4^15 6^165 (1 + H)^360 + 2` separates without
  any search.
- **Section 14** (a plan for three new Lean modules), **Proposition 15.1**
  (Kronecker-curve separation, standard), and **Section 16**: twelve
  research questions (16.1–16.12).

## What the report does not claim

The article's Section 1.6 collects these. In brief:

- **Not formalized.** No statement is formalized, and no `sbr:` label has a
  Lean or Rocq counterpart. The modules proposed in Section 14
  (`SexticCompressedDescriptors.lean`, `SexticCollisionFactors.lean`,
  `SexticBoundedSeparatingSearch.lean`) do not exist.
- **The source's own non-claims.** Unrefereed; not run in Lean or Rocq; no
  repository rebuild or modification; no benchmark against production
  Galois software. Decidability of radical solvability, even in polynomial
  time (Landau–Miller 1985), and the sextic block criterion are classical;
  the contributions are relative to the inspected repository and consulted
  sources, without an exhaustive priority search. The Python files are an
  exact verifier and a root-level prototype, not a coefficient-only solver
  and not an extraction of a formal proof; the expanded universal
  coefficient tables are specified, not supplied. 196 is sharp for
  arbitrary complex test sets only; `N_int` is bracketed, not determined.
  The fixed-parameter counterexamples are reducible. Theorem 11.1 is a
  mathematical realization, not a changed Lean function or an accepted
  `Primrec` proof, and claims no polynomial bit complexity. The height
  separator is not a practical method. Proposition 15.1 is standard.
- **Review.** AI-assisted and unrefereed. At the write, both scripts were
  rerun on a copy and reproduced the recorded outputs exactly (modulo line
  endings); a separate script (not shipped) checked the Lean coordinate
  convention on 300 random integer root tuples at `t = 1, …, 11` (no
  disagreement), the first separator 8 of `(−3, 0, 1, 2, 3, 4)`, and, over
  the integers, that `E_f` for `(1, 4, 10, 23, 51, 109)` has degree 195, a
  nonzero constant term and `gcd(E_f, E_f') = 1`. That is not an
  independent proof review.

## Relation to the formal project `Algebra/PolynomialFormulas`

Nothing in the project is refuted or changed. The project has formalized
**none** of this report's statements. What it does prove, in namespace
`LeanProofs.PolynomialFormulas`, under
`Algebra/PolynomialFormulas/Lean/PolynomialFormulas/` (article Section 1.5):

- `SexticSeparatingInvariants.lean`: `rootPolynomial_injective` (l.115),
  `pairDescriptor_injective` / `tripleDescriptor_injective` (l.422, 428)
  — together Lemma 2.1; `bivariateDescriptor` (l.618),
  `pairBivariateDescriptor_injective` / `tripleBivariateDescriptor_injective`
  (l.668, 677); `pairDescriptorValue` / `tripleDescriptorValue` (l.790,
  794); `exists_nat_eval_injective` (l.1048, via `exists_nat_eval_ne_zero`,
  l.1019, the combinatorial Nullstellensatz);
  `exists_pairDescriptor_separating_evaluation` /
  `exists_tripleDescriptor_separating_evaluation` (l.1074, 1083);
  `exists_pairDescriptorValue_injective` /
  `exists_tripleDescriptorValue_injective` (l.1092, 1102). All purely
  existential: no bound is stated, and the point is not on a curve.
- `SexticSeparatingSearch.lean` — **not cited by the manuscript**:
  `pairSeparatesB` / `tripleSeparatesB` (l.536, 539), the unbounded
  searches `pairSeparatingCode` / `tripleSeparatingCode` (l.604, 608;
  `Nat.find` at l.606, 610) over codes decoded by `parameterAt` (l.517),
  `pairSeparatingParameter` / `tripleSeparatingParameter` (l.612, 616) and
  their `_injective` correctness theorems (l.620, 629). This is the search
  the report bounds.
- `SexticIrreducibleDecision.lean`: the guarded total searches
  `pairTotalCode` / `tripleTotalCode` (l.87, 90; `Nat.find` at l.88, 91)
  and `pairTotalCode_computable` (l.101). The manuscript cites this file
  as where the `Nat.find` happens.
- `SexticRadicalDecision.lean`: `sexticRadicalDecision_correct` (l.34),
  `allRootsRadical_computablePred` (l.49),
  `has_verified_sextic_radical_turing_machine` (l.56); its docstring
  (l.8–9) disclaims primitive recursiveness because of the unbounded search.
- Rocq: the `Coq/SexticMuRec*.v` route also selects the parameters "by
  genuine unbounded minimization" (`Algebra/PolynomialFormulas/README.md:240-243`);
  the manuscript mentions it only in passing.

**Formalization target, not a claim.** A Lean proof of Theorem 9.1 for the
root tuple of an irreducible monic sextic, with the affine relations (3.3),
(3.6) and the convention `x = (2t², t)`, would bound the Lean search:
`pairSeparatingCode` would be at most the largest `encodeParameter` of the
points `(2t², t)`, `t ≤ 151` (`t ≤ 46` for triples), or the search could be
replaced by a fixed scan of `t = 1, …, 196`. That bounds the parameter
selector only. Two further unbounded searches remain: `linearTotalCode`
(`SexticReducibleDecision.lean:72`, `Nat.find` at l.73), which the
manuscript notes, and `elementaryCode` (`SexticSparseSymmetricSearch.lean:634`,
`Nat.find` at l.637), the elementary-symmetric certificate search behind
`elementarySparse` (l.671), `pairElementarySparse` /
`tripleElementarySparse` (l.1133, 1138) and `pairCollisionElementary` /
`tripleCollisionElementary` (`SexticSeparatingSearch.lean:282, 286`), which
the manuscript does not mention.

## Relation to neighbouring reports

[`specialization-safe-radical-solvers`](../specialization-safe-radical-solvers/README.md)
(batch 36), the other report in this category, is a sibling: its
separating repair (Theorem 7.2) compresses `k`-subsets of the roots of a
prime-degree polynomial by `h_A(u)` with an unsharpened bound (1191 values
for septic triples), and its Research question 14.3 asks for a smaller
number for `(n, k) = (7, 3)` by counting collision orbits. This report does
that kind of orbit count for sextic block partitions and reaches a sharp
bound; it answers no question of that report, and neither manuscript
cites the other. A dated `[write]` note in that report (after its
Theorem 7.2) points here. No other report of the
collection shares a theorem with this one.

## Building

From a scratch copy of this directory (keeps auxiliary files out of the
repository):

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (`newtx`, `tcolorbox`, `cleveref`, `aliascnt`), no external
bibliography or figures. The committed build: 28 pages, 0 errors, 0
undefined references or citations, 0 multiply defined labels, 0 duplicate
destinations, 0 overfull or underfull boxes. Do not use `code/build.sh`: it
changes to its own directory (`code/`), which has no `article.tex`.

## Rerunning the checks

The scripts write into a directory `checks/` next to the `code/` directory
that contains them (`Path(__file__).resolve().parents[1] / 'checks'`), so
in place they would create a stray `checks/` in the report directory. Run
them on a copy:

```
mkdir <tmp> && cp -r code <tmp>/ && cd <tmp>
uv run --no-project --with sympy==1.14.0 python code/verify.py
py code/sharpness_certificate.py
```

Compare `<tmp>/checks/verification.json` and
`<tmp>/checks/sharpness_certificate.json` with the files of the same names
in `data/` after removing carriage returns (on Windows `write_text` emits
CRLF). At the write both commands exited 0 in about 6 s together, and both
files matched their shipped counterparts modulo CR. `sharpness_certificate.py`
imports `verify.py` from its own directory (without importing SymPy or
running its checks), so keep the two together. Do not run Python with
`-O`: the checks are `assert` statements.

## Discrepancies and delivery names

- The delivered text uses the delivery layout: Section 9.1 and the
  Appendix B ledger name `checks/…` (with a `[write]` footnote and an
  inline `[write]` remark respectively), and Appendix A describes an archive with the PDF, a README and a
  checksum file and runs `./build.sh` and `python code/verify.py` from the
  package directory (a `[write]` note there gives the shipped layout).
- `code/build.sh` runs `pdflatex` three times in `.build/` after `cd`-ing
  to its own directory, which is `code/` here; it fails there.
- `code/verify.py` (l.183) and `code/sharpness_certificate.py` (l.115)
  write to `parents[1]/checks/`, a directory that is `data/` in the shipped
  layout; they never write into `data/` itself.
- `data/environment.json` records the delivery's run (Python 3.13.5, SymPy
  1.14.0, report date 2026-09-28) and names the commands
  `python code/verify.py` and `python code/sharpness_certificate.py`; it
  is not regenerated by the scripts.
- The delivered README asked for `python -m pip install -r
  requirements.txt`; here the file is `data/requirements.txt`, and the
  `uv --with sympy==1.14.0` form above needs no install.
- The manuscript's bibliography key `repo-search` points to
  `SexticIrreducibleDecision.lean`; the file with the separating search
  itself, `SexticSeparatingSearch.lean`, is cited only by a `[write]`
  entry.
