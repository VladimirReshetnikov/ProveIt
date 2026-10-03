# Targeted public provenance: real-exact binary sandpile certificates

Checked 3 October 2026, approximately 19:17–19:22 UTC. This is a targeted comparison of public mathematical text, not an exhaustive literature or repository novelty search.

## Finding

The inspected public sandpile manuscripts establish unique **natural** certificates. I did not find the present **nonnegative-real zero-set theorem for the binary specialization** in those sources. In particular, manuscript 16 does not print either the all-pair selector penalties or the smaller change replacing `f g` by `f(g+k+c)`, and does not prove the required real-rank integrality by a finite predecessor chain.

However, the neighboring public quadratic-orthant report already explicitly supplies strong nonnegative-product gates, one-hot selection over the real orthant, and certificates whose every nonnegative-real zero is natural. Those general principles must be credited, not presented as new here. The narrow contribution under examination is their economical use in the binary support-burning certificate, together with the rank-witness integrality argument and unchanged witness/summand ledger of the merged presentation.

## Versions and authentication

- Requested pin: `83befe707f2840c2b53e0606701d8a2b28598e47` in [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/83befe707f2840c2b53e0606701d8a2b28598e47)
- Current public `main` observed during the check: [`0055e1c4d5bd890878edf75a11fb412b9d15f6cc`](https://github.com/VladimirReshetnikov/ProveIt/commit/0055e1c4d5bd890878edf75a11fb412b9d15f6cc), commit timestamp 2026-10-03 19:18:21 UTC. This is a recorded observation, not a claim that the branch will remain there
- Canonical-certificates README Git blob: `87850cba52f8984b668f59a6a098e4ebd36ea93b`, identical at the requested pin and the observed current read
- Canonical-certificates article Git blob: `2f9713f5dcc7c0820a394ea288632e70e45db733`, identical at the requested pin and observed current revision
- Quadratic-orthant article Git blob: `061fe143db3e44a906ff9e0f6351f98efaafe132`, checked at the requested pin and current revision

The already-downloaded canonical article and README were authenticated by independently computing their Git blob SHA-1 values and comparing them with current public GitHub metadata. The current public article was also retrieved as text. The ordinary web fetch returned cache misses, so successful read-only GitHub connector calls supplied the public text and metadata. No repository was cloned, no upstream program was executed, and no public write occurred.

## 1. Exact public sandpile statements

### Manuscript 16: compact cubic

[README, lines 354–371](https://github.com/VladimirReshetnikov/ProveIt/blob/83befe707f2840c2b53e0606701d8a2b28598e47/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md#L354-L371) summarizes a compact cubic with `10n+6E` coordinates and `10n+7E` summands, with one natural certificate per natural input.

[Article, compact construction, lines 23303–23443](https://github.com/VladimirReshetnikov/ProveIt/blob/83befe707f2840c2b53e0606701d8a2b28598e47/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex#L23303-L23443), labels `cdc:sp:eq:fiveway`, `cdc:sp:eq:compactvertex`, `cdc:sp:thm:compact`, gives the actual formulas. Its vertex variables include separately quantified `u` and `alpha`; the specialization `u=k+c, alpha=0` is not made there. The proof relies on naturality when passing from the simplex equation to categorical selectors. The written theorem and zero-set bijection are over natural witnesses.

The five-way edge term consists of the simplex square, five selector-weighted squares, and the inactive middle-gap product. It contains no ten-pairproduct sum. Its five-way lemma is stated for integer differences. Nonetheless, examination of the displayed formula shows that its selector-Booleanity conclusion already holds for real differences: positive selectors force the difference into the pairwise disjoint regions `delta<=-2`, `delta=-1`, `delta=0`, `delta=1`, `delta>=2`. Thus the proposed ten edge pairproducts are not necessary for real one-hotness of this particular gadget. They may be added harmlessly, but should not be advertised as necessary.

[Article, rank characterization, lines 23015–23083](https://github.com/VladimirReshetnikov/ProveIt/blob/83befe707f2840c2b53e0606701d8a2b28598e47/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex#L23015-L23083), label `cdc:sp:thm:ranks`, assumes the proposed rank vector lies in the naturals and then identifies it by induction with the parallel burning rounds. That is not the new obligation of deriving rank integrality from initially real coordinates.

The public discussion also observes that the cubics are nonnegative on the whole real orthant. This is a sign property of the polynomial; it does not assert that all real zeros are natural. See the [README discussion, lines 3669–3677](https://github.com/VladimirReshetnikov/ProveIt/blob/83befe707f2840c2b53e0606701d8a2b28598e47/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md#L3669-L3677).

### Manuscript 19: quadratic residuals and quartic

[Article, manuscript 19 opening](https://github.com/VladimirReshetnikov/ProveIt/blob/83befe707f2840c2b53e0606701d8a2b28598e47/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex#L24371-L24380) distinguishes its independent second route from manuscript 16. Its compiler has `11n+12E` natural witnesses and `12n+16E` quadratic residuals, squared into a quartic. See [the finite-compiler theorem and rejection gap, lines 24812–24891](https://github.com/VladimirReshetnikov/ProveIt/blob/83befe707f2840c2b53e0606701d8a2b28598e47/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex#L24812-L24891), labels `cdc:nb:thm:finitecompiler` and `cdc:nb:cor:gap`.

Its Boolean residuals are exact over the reals, but its compiler theorem quantifies natural witnesses. Its unit rejection gap is explicitly a discrete statement, not a conditioning or real-zero statement. Its comparison gadget is stated for integer-valued expressions; no general magnitude-integrality conclusion should be inferred merely from Boolean branch variables.

The manuscripts' own [16 source ledger](https://github.com/VladimirReshetnikov/ProveIt/blob/83befe707f2840c2b53e0606701d8a2b28598e47/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/16-sandpile-SOURCES.md) and [19 source ledger](https://github.com/VladimirReshetnikov/ProveIt/blob/83befe707f2840c2b53e0606701d8a2b28598e47/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/19-no-borrowed-firings-SOURCES.md) disclaim exhaustive priority claims and Lean certification.

## 2. Existing public real/Nat mechanism that must be credited

[Quadratic-orthant article, strong branch gates, lines 5161–5185](https://github.com/VladimirReshetnikov/ProveIt/blob/0055e1c4d5bd890878edf75a11fb412b9d15f6cc/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/article.tex#L5161-L5185), label `qoc:rn:lem:gates`, uses

`(sum_i e_i - 1)^2 + sum_i (sum_(j!=i) e_j)(e_i + sum_alpha x_(i,alpha))`.

It proves real one-hotness and zeroing of inactive branch bases by nonnegativity. With no bases, the product sum is `2 sum_(i<j) e_i e_j`, so the all-pairproducts idea is already present algebraically. The report attributes that gate to an earlier part of the same report rather than claiming a fresh principle for the lemma.

[The trace and zero-fiber theorem, lines 5320–5337](https://github.com/VladimirReshetnikov/ProveIt/blob/0055e1c4d5bd890878edf75a11fb412b9d15f6cc/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/article.tex#L5320-L5337), label `qoc:rn:thm:trace`, proves that every nonnegative-real zero is natural for bounded reset-net traces, using one-hot gates and induction from natural initial states. The canonical-certificates article itself points to this result at [line 3968](https://github.com/VladimirReshetnikov/ProveIt/blob/83befe707f2840c2b53e0606701d8a2b28598e47/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex#L3968).

The note at quadratic-orthant line 5185 is a directly relevant warning: real Boolean selection does not by itself force a branch magnitude to be natural when divisibility enters its decoding. This supports separating selector exactness from the sandpile rank and endpoint arguments.

## 3. Precise comparison with the present binary upgrade

The reviewed local predecessor certificate fixes `u=k+c` and deletes the general compact compiler's `alpha` and independent `u`. It has eight vertex coordinates. Its theorem was deliberately natural-domain only and included an explicit fractional counterexample.

The present primary change is narrower than the initial all-pairs proposal:

1. Replace `f g` with `f(g+k+c)`; the polynomial difference is `f k + f c`
2. Use the simplex `f+k+c=1` and nonnegativity to force `u=k+c` into `{0,1}`
3. Reuse the already real-exact five-way edge ranges
4. For an active vertex, write `r=1+c+beta`; when `r>1`, the existing masking relations force `c>0`, and previous-round failure with present success forces `B>A`
5. The edge ranges then give a neighbor with rank exactly `r-1`; iterating this finite strict descent, with active ranks at least one, forces natural ranks rather than assuming them
6. Recover the vertex categories, gaps, endpoint and halo coordinates as natural values and apply the established binary-support legality and uniqueness argument

This is a comparison of the mathematical mechanism, not a substitute for the separate full proof/code audit. The strengthened product keeps the displayed summand count and variable count unchanged, and retains degree at most three; its expanded polynomial adds two degree-two monomials per vertex.

The natural zero set is unchanged because every old natural zero already has `f k=f c=0`. The smaller gate differs from enforcing all three vertex pairproducts locally: the missing `k c=0` conclusion is obtained globally through rank integrality. That local-to-global rank argument is the substantive point to describe and audit.

### Essential scope warning

Do not transfer this conclusion to manuscript 16's unrestricted odometer certificate. Even after all proposed selector pairproducts are added, its one-vertex graph with sink degree `2` and input `eta=3` has the fractional real zero

`u=5/4, z=1/2, ell=1/2, f=0, k=1, c=0, alpha=1/4, beta=0, g=1/2, h=0`.

Every displayed compact vertex summand vanishes and there are no internal edges. Its selectors and rank are already integral. The binary specialization excludes it because it imposes `u=k+c` and `alpha=0`. Thus binary support is a mathematical hypothesis, not just a representation choice.

## Suggested attribution boundary

An appropriate statement is: “We strengthen the binary specialization of the existing compact sandpile cubic by replacing one inactive-gap product at each vertex. Building on established strong-gate methods, we prove that its entire nonnegative-real zero set is natural by a finite rank-predecessor argument. A targeted check of the pinned and observed current public sandpile text did not locate this exact strengthening.”

Do not claim first-ever real-exact certificates, a new one-hot gate, new support-burning mathematics, global literature priority, a fixed-arity universal cubic, an unbounded single-fold MRDP theorem, or a Lean-verified result. The current-source check covers the identified texts and their explicit neighboring real/Nat claim; it does not establish absence from every repository branch, unpublished work, or the mathematical literature.
