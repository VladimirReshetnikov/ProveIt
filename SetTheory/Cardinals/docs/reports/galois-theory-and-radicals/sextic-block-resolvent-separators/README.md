# Finite Separators and Discriminant Factorizations for Sextic Block Resolvents

**A sharp 196-point guarantee and a bounded replacement for ProveIt's separating-invariant search; Part II: radical-solvability tests without separating sextic resolvents**

A research report of ProveIt's research-report collection, dated 28–29
September 2026, built from two manuscripts, both "Prepared for Vladimir
Reshetnikov". Part I is the original report. Part II shows that the Boolean
radical-solvability decision for an irreducible sextic needs no separating
parameter at all: one triple test at any parameter, or matching tests at
three distinct parameters, decide it. The report continues the formal
project `Algebra/PolynomialFormulas` (the Lean/Rocq sextic
radical-solvability decision), but it is not part of that development.

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| 01 | batches 40–41 intake, batch 41, manuscript 03 | `ProveIt_Finite_Sextic_Separators` (main file `article.tex`, 24-page Letter PDF, 11 files) | `e2b1f016a` | `9754e8360` | `eaf787d50` | Part I: Sections 1–17 and Appendices A–B |
| 02 | batch 57, manuscript 03 (*Three Plus One: Radical-Solvability Tests Without Separating Sextic Resolvents*, 29 September 2026, 22-page Letter PDF, 11 files) | `ProveIt_Three_Plus_One_Resolvents` (inner directory of the same name, main file `article.tex`) | `e47ed8547` | `6ad01e9c8` | `70b39943a` (prefix `02-three-plus-one-`) | Part II: Sections 19–31 and Appendices C–E (Section 18 is the write's) |

Source 01's pin is the full commit `e2b1f016a94102663f12b970e6dd434229f90d01`
(the article's `\snapshot` macro). `Algebra/PolynomialFormulas` has no commit
between that pin and its placement commit, so every repository statement of
Part I was checked against the tree it describes.

Source 02's pin is `e47ed8547bd021f9bd85bdcf767c94a2fcb41001`, the arrival
commit of batch 56. There Part I's `article.tex` had the blob `3f52dc51`,
unchanged at placement, so the manuscript's "predecessor report" is Part I
as printed (before the dated notes of this write). The five Lean files it
cites (`SexticRadicalDecision.lean`, `SexticSeparatingSearch.lean`,
`SexticSparseSymmetricSearch.lean`, `SexticSeparatingInvariants.lean`,
`SexticReducibleDecision.lean`) have the same blobs at both pins and at the
placement commit; every blob named in `data/02-three-plus-one-sources.json`
resolves to that content, except the SymPy test-seed file, which is external
to ProveIt and was not checked. The manuscript did not see the other
batch-57 deliveries.

**Status: AI-assisted, unrefereed, not formalized.** No statement of either
part has a Lean or Rocq proof; that the report sits next to a formal project
confers no formal status on it.

```
article.tex                                the report, standalone LaTeX with an internal bibliography
article.pdf                                the compiled report, 54 pages, US Letter (unnumbered title
                                           page, contents pages 1–2, Part I pages 3–27, Part II
                                           pages 28–51, references pages 51–53)
README.md                                  this guide
code/verify.py                             Part I: exact checks (SymPy 1.14.0 for four symbolic
                                           identities; the rest integer arithmetic): counts,
                                           discriminant identities, symmetry, the 462-subset sample,
                                           fixed-parameter counterexamples
code/sharpness_certificate.py              Part I: standard-library generator and checker of the
                                           modular Bézout certificate for the roots (1, 4, 10, 23, 51, 109)
code/build.sh                              Part I: the delivered PDF build script (does not work
                                           from code/; see below)
code/02-three-plus-one-sextic_resolvents.py  Part II: exact coefficient-only evaluator of both
                                           resolvents and the decision function (SymPy)
code/02-three-plus-one-verify.py           Part II: verifier (symbolic identities, split-root
                                           comparisons, 48 irreducible inputs against SymPy's
                                           Galois classifier); see "Rerunning" before running it
code/02-three-plus-one-build.sh            Part II: the delivered PDF build script (does not work
                                           from code/)
data/verification.json                     Part I: recorded output of code/verify.py
data/sharpness_certificate.json            Part I: recorded certificate: E mod 1000003 (degree 195)
                                           and cofactors A, B
data/environment.json                      Part I: the delivery's record of its software versions and runs
data/requirements.txt                      Part I: the pin sympy==1.14.0
data/02-three-plus-one-requirements.txt    Part II: the pin sympy==1.14.0 (same bytes as Part I's)
data/02-three-plus-one-sources.json        Part II: repository pin, Git blobs of the inspected
                                           sources, SymPy seed file, primary literature
data/02-three-plus-one-verification.json   Part II: recorded output of its verifier (Python 3.13.5,
                                           SymPy 1.14.0, elapsed_seconds 38.643, all_checks_passed)
data/02-three-plus-one-verification.log    Part II: recorded console transcript (51 lines)
```

Every file under `code/` and `data/` is byte-identical to its delivery.
The delivered READMEs and PDFs are not shipped: this README replaces them,
and `article.pdf` is a build of the written text. Neither delivered checksum
file `SHA256SUMS` is shipped (10 of 10 verified at each placement). Source
02's LaTeX source is not shipped either; it is printed as Part II. Each
source's unshipped files survive in its arrival commit (`9754e8360` for
source 01, `6ad01e9c8` for source 02). Delivery names:

- Source 01 (flat layout with a `checks/` directory): `build.sh` →
  `code/build.sh`, `requirements.txt` → `data/requirements.txt`, and
  `checks/X` → `data/X` for its three JSON files.
- Source 02: `code/sextic_resolvents.py` →
  `code/02-three-plus-one-sextic_resolvents.py`, `code/verify.py` →
  `code/02-three-plus-one-verify.py`, `build.sh` →
  `code/02-three-plus-one-build.sh`, `requirements.txt` →
  `data/02-three-plus-one-requirements.txt`, and `data/X` →
  `data/02-three-plus-one-X` for `sources.json`, `verification.json` and
  `verification.log`. **Its delivered names `code/verify.py`,
  `data/verification.json` and `requirements.txt` collide with Part I's
  files here** (see "Rerunning").

## Labels and numbering

Part I's labels carry the prefix `sbr:`, Part II's the prefix `tpo:`.

- `sbr:` (77, unchanged): the 73 delivered labels of source 01 plus the four
  added at its write, `sbr:sec:notation`, `sbr:sec:provenance`,
  `sbr:sec:formal`, `sbr:sec:nonclaims`. Every theorem, equation and section
  number of Part I is that of the delivered 24-page PDF; at this write the
  `.aux` numbers of all 77 were compared with a build of the committed text
  and none changed.
- `tpo:` (70, new): source 02's 61 delivered labels under the prefix; five
  for the write's Section 18 (`tpo:sec:write`, `tpo:sec:provenance`,
  `tpo:sec:notation`, `tpo:sec:formal`, `tpo:sec:nonclaims`); three on Part
  I's Research questions 16.3, 16.7, 16.8 (`tpo:q:sbr-irreducible`,
  `tpo:q:sbr-circuits`, `tpo:q:sbr-primrec`), which were unlabelled; and
  `tpo:q:smaller` on Part II's Question 30.6. 147 labels in total.

The manuscript's Section `n` is Section `n + 18`, its Appendices A–C are
Appendices C–E, and its theorem and equation numbers follow (its Theorem 1.1
is Theorem 19.1, its equation (1.1) is (19.1)). Its one table, Table 1
there, is Table 4 here, because the report's three earlier longtables share
the table counter.

Corrections of form. At source 01's write: the title page's spacing was
tightened, and the environments sharing the theorem counter use alias
counters (`aliascnt`), because in the delivered build every `\cref` to a
lemma, proposition or corollary printed "theorem". At this write: the
manuscript's macros `\M`, `\T`, `\pin` are `\tpoM`, `\tpoT`, `\tpopin`, and
its `\E` is Part I's `\Edges` (same printed symbols); its four unused
operator declarations were dropped; `listings` was loaded for its two code
listings.

## Setting and notation

`f` is a sextic with distinct roots `α_1, …, α_6` in a characteristic-zero
field; `P` ranges over the 15 pair partitions (matchings), `T` over the 10
triple partitions. The complete descriptors are
`D_B(u, v) = ∏_{B ∈ 𝓑} (v − p_B(u))` with `p_B(u) = ∏_{i ∈ B} (u − α_i)`.
On the curve `(u, v) = (t, 2t²)` they become
`D_P = K_2(t) − 2t² h_P(t)` and `D_T = K_3(t) − 2t² k_T(t)`, with
`h_P = A_P t² + B_P t − C_P` and `k_T = a_T t − b_T`.

Section 1.3 of the article tabulates Part I's overloaded letters, and
Section 18.2 Part II's. The readings most likely to mislead:

- **Lean's coordinate order.** Lean's parameter is a pair `x : Fin 2 → ℕ`;
  in `bivariateDescriptor`, `X 0` is the block variable `v` and `X 1` the
  root variable `u`. True: `x(0) = 2t²`, `x(1) = t`. False: the reverse.
  Checked at source 01's write against the definitions and by a separate
  script.
- **Code versus parameter.** Lean's `Nat.find` runs over `Primcodable`
  codes decoded by `parameterAt`, not over `t`; 196 bounds `t`.
- **196 versus `N_int`.** 196 is sharp for arbitrary sets of distinct
  nonzero complex test values; for the initial integer interval only
  `8 ≤ N_int ≤ 196` is proved.
- **Argument order of the resolvents.** Part I writes `R_{2,f}(Z, t)`,
  `R_{3,f}(Z, t)`; Part II writes the same polynomials `R_{2,f}(t, Z)`,
  `R_{3,f}(t, Z)`, parameter first. In Part II's Table 4, `R_3(1)` means
  `R_{3,f}(1, Z)`.
- **Fields.** Part II's `K` is the base field over which `f` is irreducible
  and does not contain the roots; `L` is its splitting field (Part I calls it
  `M`), not Part I's triple collision factor `L_f`. Part II's `𝓔` is the
  edge set of `K_6` (Part I's `𝓔` too), not the obstruction `E_f`.
- **Edge-disjoint = block-disjoint.** A matching's blocks are edges, so
  Part II's edge-disjoint matchings are Part I's block-disjoint ones. A
  *pentad* (five pairwise edge-disjoint matchings, a one-factorization of
  `K_6`) is new in Part II; `𝓑_f` there is a set of parameters, not a
  partition.
- **Matrices.** In Part II Section 26, `C, S, P, Q, H, U, V, D, F` are
  matrices or the scalar `f(u)`, not `C_P`, a matching `P`, `Q_f`, the
  height `H`, `U_f`, the variables `u, v`, or descriptors. `H` and
  `R = 1 + H` of Part II Section 27 agree with Part I Section 11.
- `p_B` is a block's root polynomial, `p_b = α_i α_j` a pair product, `p`
  the prime 1000003. `R_{2,f}`, `R_{3,f}` are resolvents, `R = 1 + H` a
  root bound; neither is the sibling report's `R_{p,k,f}`, and `h_P` is not
  its `h_A(u)`. In Lemma 5.1 the letters `a, …, f` are root values. Degrees
  30, 120, 45, 195 are degrees in `t`; 30, 240, 90, 360 are homogeneous
  degrees in roots and `t`.

No symbol was renamed in print and no normalization changed.

## What the report claims

Theorem numbers are those of `article.pdf` (for Part I also those of the
delivered PDF).

**Part I.**

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
  resolvents has a rational root (classical criterion, reproved). Part II's
  Theorem 19.1 removes the separation hypothesis for the decision (a dated
  note after Theorem 10.3 says so).
- **Theorem 11.1.** A bounded coefficient-only procedure (monicization,
  bounded factor boxes, the quintic branch, a scan of `t = 1, …, 196`,
  bounded integer-root tests) has a primitive-recursive realization and
  decides all-roots radical solvability of integer sextics.
- **Theorem 12.1.** `t_* = 4^15 6^165 (1 + H)^360 + 2` separates without
  any search.
- **Section 14** (a plan for three new Lean modules), **Proposition 15.1**
  (Kronecker-curve separation, standard), and **Section 16**: twelve
  research questions (16.1–16.12). Question 16.3 is answered for the
  decision (not for separation) by Part II, and 16.7 and 16.8 are partly
  addressed; dated notes after them say how.

**Part II** (irreducible `f` over a characteristic-zero field `K`, Galois
group `G`).

- **Theorem 19.1 (three plus one).** For any distinct `t_1, t_2, t_3 ∈ K`
  and any `u ∈ K`, `f` is solvable by radicals iff `R_{3,f}(u, Z)` has a
  root in `K`, or each `R_{2,f}(t_j, Z)` has one; over `Q`, `u = 1`,
  `t = 1, 2, 3` work for every irreducible sextic. Repeated resolvent roots
  are allowed.
- **Lemma 21.2.** A transitive subgroup of `S_6` preserving a regular graph
  of degree 1–4 is solvable, so a nonsolvable transitive group is
  edge-transitive. **Lemma 22.1, Theorem 22.2.** If `G` is nonsolvable, the
  shifted pair products are distinct and the ten values `k_T(u)` are
  distinct at every `u ∈ K`, with no root of `R_{3,f}(u, Z)` in `K`.
- **Lemma 23.2, Lemma 23.4, Theorem 23.5.** In the nonsolvable case no
  `q_e(t)` vanishes at `t ∈ K`; there are exactly six pentads, each matching
  in two, any two meeting in one; a base-field root of `R_{2,f}(t, Z)` has
  as fiber a `G`-invariant pentad, multiplicity exactly five, is the only
  such root, and `G` fixes at most one pentad. **Lemma 23.6, Corollary
  23.7.** Pentad sums are `e_2`, `3e_3`, `e_4`, so such a root equals
  `μ_f(t) = (e_2 t² + 3e_3 t − e_4)/5`.
- **Theorem 24.1.** The false-positive parameters are the zeros in `K` of a
  canonical `J_f ∈ K[t]` of degree ≤ 2 (empty without an invariant pentad),
  so there are at most two.
- **Proposition 25.1 (orbit budget)**, early-exit certificates (Section
  25.1).
- **Theorems 26.1, 26.2.** `det(Z I_45 − B_2(t)) = R_{2,f}(t, Z)^3` for
  every separable monic sextic and every `t`, and
  `det(Z I_20 − B_3(u)) = R_{3,f}(u, Z)^2` when `f(u) ≠ 0`, from compound
  matrices of the companion matrix; exact cube and square roots by a
  triangular recurrence (Section 26.4).
- **Proposition 27.1.** The criterion for monic irreducible integer sextics
  has a primitive-recursive realization (explicit root boxes
  `|h_P(t)| ≤ 66R⁴`, `|k_T(1)| ≤ 8R³`), and irreducibility can be checked by
  a bounded search.
- **Section 28**: exact checks, including all sixteen transitive group
  types in three coordinate variants each (22 triple-positive,
  14 matching-positive, 12 negative, all agreeing with SymPy's classifier);
  **Section 29**: source map and formalization order; **Section 30**: ten
  research questions (30.1–30.10).
- Reproved from Part I and printed again, with notes: Lemma 20.1 (= Lemma
  2.1), Proposition 20.2 (= Propositions 3.1–3.2), Lemma 21.1 (= Lemma 10.1
  with Proposition 10.2), Lemma 23.1 (= Lemma 4.1).

## What the report does not claim

The article's Sections 1.6 and 18.4 collect these. In brief:

- **Not formalized.** No statement is formalized, and no `sbr:` or `tpo:`
  label has a Lean or Rocq counterpart. The modules proposed in Section 14
  (`SexticCompressedDescriptors.lean`, `SexticCollisionFactors.lean`,
  `SexticBoundedSeparatingSearch.lean`) do not exist.
- **Source 01's non-claims.** Unrefereed; not run in Lean or Rocq; no
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
- **Source 02's non-claims.** Unrefereed, not formalized, repository not
  modified or rebuilt; proofs are written proofs, not imported Lean
  theorems; priority not certified and novelty not inferred from absence in
  the repository. General and polynomial-time decidability are classical,
  and Proposition 27.1 is not a new decidability result, claims no bit
  complexity and no speed advantage; its boxes are a coarse termination
  bound. **No claim that three matching tests are optimal**, and no example
  shows that two or one must fail; the *and* between the matching tests
  cannot be replaced by *or*. **No false positive is exhibited or claimed to
  exist**: `|𝓑_f| ≤ 2` is an upper bound, not a maximum. **Part I's
  196-point separation bound is neither improved nor contradicted**: Part II
  solves a weaker decision problem under a stronger irreducibility
  hypothesis, which is essential. The triple test is safe but not complete.
  The implementation is an exact rational prototype, not a verified
  extraction; it rejects reducible input, does not implement the
  multiplicity shortcut, and the reducible extension (with a quintic
  criterion) is not included. The checks are finite; the classifier shares
  SymPy's arithmetic; 48 examples are not exhaustive and contain no
  nonsolvable false positive; no benchmark; the running time is an
  environment observation. Its questions are open within the article only.
- **Review.** AI-assisted and unrefereed. At source 01's write both of its
  scripts were rerun on a copy and reproduced the recorded outputs exactly
  (modulo line endings); a separate script (not shipped) checked the Lean
  coordinate convention on 300 random integer root tuples at
  `t = 1, …, 11` (no disagreement), the first separator 8 of
  `(−3, 0, 1, 2, 3, 4)`, and, over the integers, that `E_f` for
  `(1, 4, 10, 23, 51, 109)` has degree 195, a nonzero constant term and
  `gcd(E_f, E_f') = 1`. At this write Part II's verifier was rerun on a copy
  (below), and at placement a separate script (not shipped) recomputed the
  pentad incidences, the pentad sums symbolically, the 45 shared-edge
  factorizations and the descriptor expansion, and found numerically (60
  digits, not a proof) no invariant pentad for the `A_6` seed and exactly one
  for the `PSL_2(5)` and `PGL_2(5)` seeds, consistent with `J_f = 1` there.
  None of that is an independent proof review.
- **An editorial consequence.** Section 18.4 notes, as the write's own
  observation (in neither manuscript), that for a nonsolvable irreducible
  sextic and `t ∈ K`, Part II's Theorem 22.2 and Lemma 23.2 give
  `L_f(t) ≠ 0` and `Q_f(t) ≠ 0`, so `E_f(t) = 0` iff `U_f(t) = 0`. It does
  not settle Question 16.3.

## Relation to the formal project `Algebra/PolynomialFormulas`

Nothing in the project is refuted or changed. The project has formalized
**none** of this report's statements, in either part. What it does prove,
in namespace `LeanProofs.PolynomialFormulas`, under
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
- `SexticSeparatingSearch.lean` — **not cited by source 01; cited by
  source 02**: `pairSeparatesB` / `tripleSeparatesB` (l.536, 539), the
  unbounded searches `pairSeparatingCode` / `tripleSeparatingCode` (l.604,
  608; `Nat.find` at l.606, 610) over codes decoded by `parameterAt`
  (l.517), `pairSeparatingParameter` / `tripleSeparatingParameter` (l.612,
  616) and their `_injective` correctness theorems (l.620, 629). This is the
  search Part I bounds and Part II bypasses on paper.
- `SexticIrreducibleDecision.lean`: the guarded total searches
  `pairTotalCode` / `tripleTotalCode` (l.87, 90; `Nat.find` at l.88, 91)
  and `pairTotalCode_computable` (l.101). Source 01 cites this file as
  where the `Nat.find` happens; source 02 does not cite it.
- `SexticRadicalDecision.lean`: `sexticRadicalDecision_correct` (l.34),
  `allRootsRadical_computablePred` (l.49),
  `has_verified_sextic_radical_turing_machine` (l.56); its docstring
  (l.8–9) disclaims primitive recursiveness because of the unbounded search.
- Rocq: the `Coq/SexticMuRec*.v` route also selects the parameters "by
  genuine unbounded minimization" (`Algebra/PolynomialFormulas/README.md:240-243`);
  source 01 mentions it only in passing, source 02 not at all.

**Formalization targets, not claims.** A Lean proof of Theorem 9.1 for the
root tuple of an irreducible monic sextic, with the affine relations (3.3),
(3.6) and the convention `x = (2t², t)`, would bound the Lean search:
`pairSeparatingCode` would be at most the largest `encodeParameter` of the
points `(2t², t)`, `t ≤ 151` (`t ≤ 46` for triples), or the search could be
replaced by a fixed scan of `t = 1, …, 196`. That bounds the parameter
selector only. Two further unbounded searches remain: `linearTotalCode`
(`SexticReducibleDecision.lean:72`, `Nat.find` at l.73), which source 01
notes, and `elementaryCode` (`SexticSparseSymmetricSearch.lean:634`,
`Nat.find` at l.637), the elementary-symmetric certificate search behind
`elementarySparse` (l.671), `pairElementarySparse` /
`tripleElementarySparse` (l.1133, 1138) and `pairCollisionElementary` /
`tripleCollisionElementary` (`SexticSeparatingSearch.lean:282, 286`), which
source 01 does not mention. Part II needs no separating parameter at all on
the irreducible branch: a Lean proof of its Theorems 22.2, 23.5, 24.1 and
19.1 against the existing descriptor definitions would let that branch test
the fixed points `x = (2t², t)`, `t = 1, 2, 3`, instead of calling
`pairSeparatingCode` / `tripleSeparatingCode` (or `pairTotalCode` /
`tripleTotalCode`). `elementaryCode` would remain unless Part II's matrix
Theorems 26.1–26.2 were also formalized as the coefficient evaluator, and
`linearTotalCode` remains on the reducible branch in any case. Part II's
Proposition 27.1 is a written argument, not a `Primrec` proof.

## Relation to neighbouring reports

[`specialization-safe-radical-solvers`](../specialization-safe-radical-solvers/README.md)
(batch 36, with a Part II from batch 52), the other report in this
category, is a sibling: its separating repair (Theorem 7.2) compresses
`k`-subsets of the roots of a prime-degree polynomial by `h_A(u)` with an
unsharpened bound (1191 values for septic triples), and its Research
question 14.3 asks for a smaller number for `(n, k) = (7, 3)` by counting
collision orbits. Part I here does that kind of orbit count for sextic
block partitions and reaches a sharp bound; Part II's Proposition 25.1 is a
general orbit-collapse budget of the same kind, and its pentad argument
shows that classifying invariant fibers can beat it. Neither part answers a
question of that report, and none of the manuscripts cites the other
report. A dated `[write]` note in that report (after its Theorem 7.2)
points here. No other report of the collection shares a theorem with this
one.

## Building

From a scratch copy of this directory (keeps auxiliary files out of the
repository):

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (`newtx`, `tcolorbox`, `cleveref`, `aliascnt`, `listings`), no
external bibliography or figures. The committed build: 54 pages, 0 errors, 0
undefined references or citations, 0 multiply defined labels, 0 duplicate
destinations, 0 overfull or underfull boxes, no Type 3 fonts. Do not use
`code/build.sh` or `code/02-three-plus-one-build.sh`: each changes to its
own directory (`code/`), which has no `article.tex`.

## Rerunning the checks

Run every script on a copy, never in the report directory.

**Part I.** Its scripts write into a directory `checks/` next to the
`code/` directory that contains them (`Path(__file__).resolve().parents[1] / 'checks'`),
so in place they would create a stray `checks/` in the report directory:

```
mkdir <tmp> && cp -r code <tmp>/ && cd <tmp>
uv run --no-project --with sympy==1.14.0 python code/verify.py
py code/sharpness_certificate.py
```

(`cp -r code` also copies Part II's scripts; these commands do not run them.)

Compare `<tmp>/checks/verification.json` and
`<tmp>/checks/sharpness_certificate.json` with the files of the same names
in `data/` after removing carriage returns (on Windows `write_text` emits
CRLF). At source 01's write both commands exited 0 in about 6 s together,
and both files matched their shipped counterparts modulo CR.
`sharpness_certificate.py` imports `verify.py` from its own directory
(without importing SymPy or running its checks), so keep the two together.
Do not run Python with `-O`: the checks are `assert` statements.

**Part II — do not run its verifier in place.**
`code/02-three-plus-one-verify.py` imports `sextic_resolvents` under the
delivered name (l.13) and always writes
`Path(__file__).resolve().parents[1]/'data'/'verification.json'`
(l.226–227). Under its shipped name the import fails before anything is
written; but a copy that restores the delivered names inside this directory
would **overwrite Part I's `data/verification.json`** (and `code/verify.py`
itself is Part I's). Restore the names only in a scratch directory:

```sh
W=/path/to/scratch; mkdir -p "$W/02/code" "$W/02/data"
cp code/02-three-plus-one-verify.py "$W/02/code/verify.py"
cp code/02-three-plus-one-sextic_resolvents.py "$W/02/code/sextic_resolvents.py"
cd "$W/02" && uv run --no-project --with sympy==1.14.0 python code/verify.py
```

Compare `$W/02/data/verification.json` with
`data/02-three-plus-one-verification.json` after removing carriage returns,
and the console with `data/02-three-plus-one-verification.log`. At this
write (Python 3.13.5, SymPy 1.14.0, Windows) the run exited 0 in about 62 s;
the JSON was CRLF and, after removing CR, equal to the record except
`elapsed_seconds` (60.078 against 38.643); the console, after removing CR,
equal to the log except the final `wrote <path>` line. The evaluator imports
nothing local and writes nothing, so it can be run in place:

```
uv run --no-project --with sympy==1.14.0 python code/02-three-plus-one-sextic_resolvents.py 'x**6+x+1'
```

(it prints `"solvable": false` after the triple test and the first matching
test, as Section 28.3 states).

## Discrepancies and delivery names

- Source 01's text uses its delivery layout: Section 9.1 and the Appendix B
  ledger name `checks/…` (with a `[write]` footnote and an inline `[write]`
  remark respectively), and Appendix A describes an archive with the PDF, a
  README and a checksum file and runs `./build.sh` and
  `python code/verify.py` from the package directory (a `[write]` note there
  gives the shipped layout).
- Source 02's text uses its delivery layout: Section 28 names
  `code/sextic_resolvents.py`, `code/verify.py`, `data/verification.json`,
  `data/verification.log`, and Appendix D runs `pdflatex`,
  `python -m pip install -r requirements.txt` and `python code/verify.py`
  from the package root and describes its build script; `[write]` notes in
  both places give the shipped names. Its delivered README (not shipped)
  said to run `./build.sh` "from any directory".
- `code/build.sh` and `code/02-three-plus-one-build.sh` run `pdflatex`
  after `cd`-ing to their own directory (l.3 of the latter), which is
  `code/` here; both fail there, and the source the second one built is not
  shipped.
- `code/verify.py` (l.183) and `code/sharpness_certificate.py` (l.115)
  write to `parents[1]/checks/`, a directory that is `data/` in the shipped
  layout; they never write into `data/` itself.
  `code/02-three-plus-one-verify.py` (l.226–227) writes to
  `parents[1]/data/verification.json`, Part I's recorded output here, with
  CRLF on Windows (`write_text` without `newline=`); see "Rerunning".
- `data/environment.json` records source 01's run (Python 3.13.5, SymPy
  1.14.0, report date 2026-09-28) and names the commands
  `python code/verify.py` and `python code/sharpness_certificate.py`; it
  is not regenerated by the scripts.
  `data/02-three-plus-one-verification.json` records source 02's run
  (Python 3.13.5, SymPy 1.14.0, `elapsed_seconds` 38.643, the pin).
- The last line of `data/02-three-plus-one-verification.log` names the
  packager's path `/mnt/data/ProveIt_Three_Plus_One_Resolvents/data/verification.json`.
  The file is tracked although the root `.gitignore` ignores `*.log`
  (l.61); it was added with `git add -f` at placement.
- The delivered READMEs asked for `python -m pip install -r
  requirements.txt`; here the files are `data/requirements.txt` and
  `data/02-three-plus-one-requirements.txt` (identical), and the
  `uv --with sympy==1.14.0` form above needs no install.
- Bibliography keys: source 01's key `repo-search` points to
  `SexticIrreducibleDecision.lean`; source 02's key `repo-search` points to
  `SexticSeparatingSearch.lean`, which Part I cites only through the
  `[write]` entry `repo-separating-search`. In the merged bibliography Part
  II's citations of that file use `repo-separating-search`, and its
  `repo-sparse` uses `repo-sparse-search`; the shared entries
  (Landau–Miller, Boswell–Glasser, three Lean files) are printed once.
