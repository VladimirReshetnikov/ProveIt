# Dilation Rigidity of Surreal Numbers and Omnific Integers

**Autonomous Mahler equations, finite support, sharp algebraic degrees, a higher-order hierarchy, and the support rank of dilation orbits**
Research report, 23 September 2026, built from three manuscripts. Source 01
is manuscript 08 of batch 30 (archive `surreal_dilation_rigidity`), pinned to
repository commit `b895e86`, placed in `21375f8` and written in `260c143`.
Sources 02 and 03 are manuscripts 02 and 04 of batch 33 (archives
`surreal_dilation_rank` and `surreal_dilation_rank_research`), pinned to
`958b5c4` and `efc5446`, placed in `aa9c891` and merged as Sections 19–27.
Author line of all three: research article prepared with ChatGPT for
Vladimir Reshetnikov.

Every result, proof, example, question and limitation of the three
manuscripts is printed; results proved by both batch-33 sources are printed
once with both named, and genuinely different proofs are kept as marked second
routes. Independent proof review and formalization are pending.

```
article.tex                                  the report, standalone LaTeX with an internal bibliography
article.pdf                                  the compiled report, 65 pages (unnumbered title page,
                                             contents pages i–ii, then pages 1–62)
README.md                                    this guide
SOURCE_AUDIT.md                              source 01's author-side source and claim audit, as delivered
02-dilation-rank-PROOF_AND_SOURCE_AUDIT.md   source 02's proof and source audit, as delivered
03-support-rank-PROOF_AND_SOURCE_AUDIT.md    source 03's proof and source audit, as delivered
code/verify.py                               source 01's exact finite checks (SymPy)
code/02-dilation-rank-verify.py              source 02's exact finite checks (SymPy)
code/02-dilation-rank-build.py               source 02's build helper (three pdfLaTeX passes)
code/03-support-rank-verify.py               source 03's exact finite checks (standard library)
code/03-support-rank-build.sh                source 03's build script (Unix)
code/03-support-rank-build.ps1               source 03's build script (PowerShell)
data/verification_results.json               source 01's recorded run
data/requirements.txt                        source 01's pin, sympy==1.14.0
data/02-dilation-rank-verification_results.json   source 02's recorded run
data/02-dilation-rank-requirements.txt       source 02's pin, sympy==1.14.0
data/02-dilation-rank-BUILD_REPORT.json      source 02's build report
data/03-support-rank-verification_results.json    source 03's recorded run
data/03-support-rank-BUILD_RECORD.json       source 03's build record
```

Every label in `article.tex` carries the prefix `adr:`. Source 01's 83 labels
are kept, unchanged after the prefix, with the eight added when it was written
(`adr:sec:conventions`, `adr:sec:collection`, `adr:sec:nonclaims`,
`adr:app:report`, `adr:app:onesource`, `adr:app:pinned`,
`adr:app:literature`, `adr:app:files`): 91 labels, none renamed or removed,
and no pre-existing theorem, section, equation or question number changed. The
merge of sources 02 and 03 added 109 labels, all with the sub-prefix `adr:sr:`
(200 in total). No `adr:` label has a Lean implementation mapping in the
[formalization ledger](../../FORMALIZATION.md). All `code/`, `data/` and audit
files are byte-identical to the deliveries; the delivered READMEs, PDFs,
manuscripts of sources 02 and 03, and checksum lists are not shipped, and
`article.pdf` is a build of this text. Text added when source 01 joined the
collection is marked `[write]`; text added in the batch-33 merge is marked
`[merge]`.

## The operator

For an ordinary integer `d ≥ 2`, the exponent dilation of a Hahn series is

    S_d(Σ a_γ t^γ) = Σ a_γ t^{dγ},   and on surreals   S_d(Σ a ω^g) = Σ a ω^{dg}.

Sections 19–27 use the same formula for every positive element `a` of an
ordered subfield `𝓕` of the coefficient field (rational or real dilations).
It is the map that
[single-dilation-hahn-support](../single-dilation-hahn-support/) writes `S_q`
at `q = d`, and that
[surcomplex-field-automorphisms](../surcomplex-field-automorphisms/) writes
`S_a` at `a = d` (`saut:eq:dilation`). It is **not** `y ↦ y^d`
(`S_2(ω+1) = ω²+1`, while `(ω+1)² = ω²+2ω+1`), not the argument dilation
`f(z) ↦ f(λz)` of the holonomic-rigidity report, and not an exponential
automorphism. `A_Γ(k)` is the **negative-support** ring (support in `Γ_{≤0}`,
nonnegative growth support in `ω` notation), not the valuation ring. The
"autonomous algebraic order" of `y` is the least `r` with
`y, S_d y, …, S_d^r y` algebraically dependent over `k` (written
`aord_{d,𝔅}(y)` over a base `𝔅` in Section 19). Section 1.4 fixes source 01's
local letters (`M(y)`, `D`, `H_a`, `L`, `T`); Section 19.2 fixes those of
Sections 19–27.

## What the report claims

Theorem numbers are those of the built `article.pdf`. `k` is a field of
characteristic zero, `Γ` any ordered abelian group, `K_Γ(k) = k((t^Γ))` the
full Hahn field, `d ≥ 2` an integer. "Strong" means preserving Hahn summation,
not convergence of partial sums.

### Source 01 (Sections 1–18)

- **Support collapse (Theorem 6.1).** If `y ∈ K_Γ(k) \ k` satisfies
  `F(y, S_d y) = 0` for some nonzero `F ∈ k[X,Y]`, then `y ∈ k((t^δ))` with
  `δ = γ/e ∈ Γ`, where `γ` is the valuation of the positive-valuation
  coordinate (`y − res y` or `1/y`) and `1 ≤ e ≤ deg_Y F`. No divisibility or
  Archimedean hypothesis on `Γ` and no order on `k` is needed. The proof
  combines an evaluated Newton–Puiseux branch with individual-branch
  denominator bound (Lemma 4.1), a formal Böttcher coordinate built and proved
  unique inside `k[[Z]]` (Lemma 5.1), the exhaustive description of all Hahn
  solutions of a superattracting germ `S_d x = h(x)` (Proposition 5.2), and the
  monomial recognizer `S_d w = w^d ⇔ w = a t^η`, `a^{d−1} = 1` (Lemma 3.3).
  Supporting lemmas: strong evaluation commuting with `S_d` (Lemma 3.1);
  constants relatively algebraically closed, `Fix(S_d) = k` (Lemma 3.2).
- **Finite profiles and existence (Theorem 7.1, Corollary 7.2, Theorem 7.3,
  Corollary 7.4).** Over algebraically closed `k`, a fixed `F` has a finite list
  of ordinary Laurent profiles `f` whose evaluations `f(t^δ)`, `δ > 0`, are all
  nonconstant solutions in every nonzero divisible `Γ`; coefficients of
  solutions are algebraic over the coefficient field of `F`; a nonzero
  positive-valuation solution of `G(x, S_d x) = 0` exists iff the minimum of
  `i + dj` over the support of `G` is attained twice; existence is independent
  of `Γ` and effectively decidable for algebraic-number coefficients.
- **Negative-support classification (Theorem 8.1, Corollary 8.2).** For
  `y ∈ A_Γ(k) \ k`: `y, S_d y` are algebraically dependent iff
  `y = P(t^{−δ})` with `P ∈ k[T]` iff the support is finite with cyclic exponent
  group; `deg P ≤ deg_Y F`. The condition does not depend on `d`; infinite
  support, or finite support of rational rank at least two, forces independence.
- **Exact relation degree (Theorem 9.2, Corollary 9.3, Example 9.4).** The least
  `Y`-degree of a relation equals the primitive degree `M(y)`;
  `k(y, S_d y) = k(T)` for the primitive monomial `T`; the irreducible relation
  has bidegree `(dM, M)`. Consequence: `k(P(T), P(T^d)) = k(T^g)`, `g` the gcd of
  the supported positive degrees. `T² + T` at `d = 2` gives an explicit quadratic
  relation (worked in Appendix A).
- **Omnific integers (Theorem 10.1, Corollary 10.2, Examples 10.3–10.6).** For
  `x ∈ Oz \ Z`: `x, S_d x` are algebraically dependent over `R` (equivalently
  over `C`) iff `x = P(ω^δ)` with `P ∈ R[T]`, `P(0) ∈ Z`, iff the support is
  finite with commensurable positive exponents; the least relation degree is
  `deg P` in the primitive step. The same holds for `Oz[i]` with `C[T]` and
  `Z[i]`. Any two distinct forward dilates of an infinite-support omnific
  integer are algebraically independent over `C`. `ω^{√2} + ω + 1` is dilation
  independent (its primality is L'Innocente–Mantova's Theorem B, cited).
- **Rational maps (Theorems 11.1, 11.2, Corollary 11.3).** Over algebraically
  closed `k` and divisible `Γ ≠ 0`, `S_q y = R(y)`, `q ∈ Q_{>1}`, has a
  nonconstant solution iff `R` has a fixed point of local degree `q` (so `q`
  is an integer), with all solutions given by Böttcher
  coordinates; in `A_Γ(k)` the only solutions are `y = α t^{−γ} + b` with
  `R(Z) = α^{1−d}(Z − b)^d + b`; simultaneous solutions force commuting maps.
- **Infinitesimal tail (Theorem 12.1).** For a polynomial `P` of degree `d ≥ 2`
  whose centred normalization is not `X^d`, the infinite solution has an exact
  first positive-valuation term `−(αc/d) T^{1−r}`, so it is not omnific;
  `S_2 y = y² + 1` has no nonconstant omnific solution, `(Z − 3)² + 3` has
  `3 + ω^γ`.
- **Higher order (Definition 13.1, Theorems 13.2, 13.3, Proposition 13.4).**
  `u_d = Σ_{n≥0} ω^{d^{−n}}` is an omnific integer of exact autonomous order two,
  with `S_d² u_d − S_d u_d = (S_d u_d − u_d)^d`; sums of `r` monomials with
  `Q`-independent exponents have exact order `r` (with all coefficients 1 the
  independence is Melánová–Sturmfels–Winter's Proposition 3, credited in the
  merge); finite support of rational rank `r` has order at most `r`, exactly 1
  for `r = 1`, exactly 2 for `r = 2` — and, since batch 33, exactly `r` for
  every `r` (Corollary 21.4).
- **Effective shapes (Theorems 15.1, 15.2).** A fixed `F` has finitely many
  polynomial shapes of degree at most `deg_Y F`; nonconstant solvability in
  `Oz` or `Oz[i]` is decidable for algebraic-number `F`, with a finite list of
  algebraic shapes (a termination result, not implemented).
- **Research questions 1–12** (Section 16). Status notes (batch 33): Question 1
  is answered in every rank; the rank component of Question 2 and the
  relative-rank part of Question 8 are answered; Question 5 has two partial
  data. The others are open.

### Sources 02 and 03 (Sections 19–27)

Here `𝓕 ⊆ k` is an ordered subfield, `Γ` a set-sized ordered `𝓕`-vector space,
`H ⊆ Γ` an `𝓕`-subspace with Hahn subfield `K_H(k) = k((t^H))`, and
`ρ_{𝓕,H}(y) = dim_𝓕 (H + span_𝓕 supp y)/H` the relative support rank
(`ρ(y)` for `𝓕 = Q`, `H = 0`).

- **Support-rank obstruction (Theorem 20.7, both sources).** If
  `ρ_{𝓕,H}(y) ≥ m`, any `m` distinct positive `𝓕`-dilates of `y` are
  algebraically independent over `K_H(k)`, for arbitrary (infinite, non-
  Archimedean) supports and arbitrary nonzero coefficients. The proof picks a
  greedy basis of the support (Lemma 20.3), proves strict rearrangement in an
  ordered vector space (Lemma 20.4) and a unique extremal support tuple
  (Proposition 20.5), and so finds one noncancelling term
  `(∏ q_j)(∏ c_{b_j}) t^{Σ q_j b_j}` of the Euler-derivation Jacobian
  (Theorem 20.6); the Jacobian criterion (Lemma 20.2) concludes. Source 02's
  vector-valued greedy determinant (Theorem 20.8) gives a second route
  (Remark 20.9).
- **Every relation bounds rank (Corollary 20.11, both).** An autonomous
  relation of order `n` over `K_H(k)`, with any support, forces
  `ρ_{Q,H}(y) ≤ n`; infinite rank gives independence of all dilates.
- **Exact finite-support formula (Theorem 21.2, Corollaries 21.3, 21.4, both).**
  For finite support, `m` distinct positive rational dilates have
  transcendence degree `min(m, ρ)`; the rational orbit is the uniform matroid
  of rank `ρ`; the autonomous order of a finite-support omnific or Gaussian
  omnific integer (indeed of any finite-support surreal or surcomplex) is its
  rational support rank, for every rational `d > 0`, `d ≠ 1`. This answers
  Research question 1 in every rank. Examples 23.1 and 23.2 are two explicit
  rank-three certificates (leading terms `96 T_1^4 T_2^4 T_3^7`, 97 terms, and
  `−96 T_1^9 T_2 T_3^6`, 45 terms).
- **Rational monomial functions (Section 22).** For `f ∈ k(Λ)`, `Λ` finitely
  generated, exact order equals rank (Theorem 22.2), by two routes: source 03's
  support descent `k(Λ) ∩ k((t^W)) = k(Λ ∩ W)` (Lemma 22.1) with the
  reduced-quotient formula `span supp f = span{a − b : a, b ∈ supp P ∪ supp Q}`
  (Theorem 22.3), and source 02's coefficient matrix `ρ_cm(f)` of
  `B_j = Q X_j∂P/∂X_j − P X_j∂Q/∂X_j`, which needs no reduction (Lemma 22.4),
  with a Jacobian-rank upper bound (Lemma 22.5) and an exact algorithm.
- **Certificate (Section 23.3, source 03).** A separating weight, greedy
  basis and one coefficient certify independence in polynomial time for
  exact finite input.
- **Infinite supports (Section 24).** `Ξ = Σ_{n≥0} ω^{ω^{−n}}` has its whole
  positive-real dilation orbit algebraically independent over `C` (Theorem
  24.2; source 02 proves it for `Ξ − ω` and rational dilations, with `Z^s`
  shifts, Corollary 24.3). Algebraic Hahn elements have a finite denominator
  index `|𝒟_y| ≤ N` (Theorem 24.5, source 02; rank-one case Lemma 24.6, source
  03). `u_d` has rank one and order two (Proposition 24.7, a proof without
  Theorem 10.1). Multi-scale telescopes have infinite support, rank `ρ` and
  exact order `ρ + 1` for every `ρ ≥ 1` (Theorem 24.8, source 02), with an
  explicit third-order equation (Example 24.9).
- **Fresh parameters (Section 25).** Joint independence for supports whose
  spans are in direct sum modulo the core (Theorem 25.1, both); an explicit
  ordinal family `Ξ_α` with independent real-dilation orbits (Theorem 25.2) and
  a tail independent over the full Hahn field of any set of surcomplex
  parameters (Theorem 25.3, Corollary 25.4, source 03); `κ` many orbits
  independent over any set-sized subfield of `No[i]` and equivariant
  embeddings of free (inversive) difference polynomial rings into `Oz` and
  `Oz[i]` (Theorem 25.5, Corollary 25.6, source 02).
- **Prime characteristic (Theorem 26.1, source 03).** For `f ∈ F_p[Λ]` whose
  support generates `Λ`, the transcendence degree of `S_{n_1}f, …, S_{n_m}f`
  is `min(rank Λ, number of distinct p-free parts of the n_j)`.
- **Merge observation (Remark 20.12, marked `[merge]`).** With `m = 2`,
  Corollary 20.11 shows that every solution of `F(y, S_q y) = 0` over `k`, for
  rational `q > 0`, `q ≠ 1`, and any support, has rational support rank at
  most one: a partial datum for Research question 5, which stays open.
- **Research questions 13–30** (Section 27.5), from both sources.

## What the report does not claim

Section 18 collects source 01's non-claims (S1–S24) and those added when it
joined the collection (W1–W7); Section 27.6 collects those of sources 02 and 03
(R1–R19) and those added in the merge (R20–R23). In brief:

- Not refereed; AI-assisted. No theorem is Lean-verified and no Lean source is
  supplied; none of the sources made a repository Lean build. Source 02's audit
  says that its proofs and audit were prepared by the same assistant, with no
  external reviewer. No named published conjecture is claimed solved; the
  questions answered are this report's own. Novelty is proposed, priority is
  not certified, and an absence of search results is not proof of priority.
- Credited, not claimed: Hahn arithmetic, the Neumann lemma, Conway normal
  forms (Gonshor), Newton–Puiseux, formal Böttcher coordinates
  (Salerno–Silverman), the collection's `d = 2` recognizer, resultants and exact
  algebraic-system solving; greedy bases (Edmonds), the Jacobian criterion
  (Beecken–Mittmann–Saxena), series derivations (Kuhlmann–Matusinski),
  power-sum independence (Melánová–Sturmfels–Winter), the character method.
  Mahler equations, Böttcher coordinates and non-Puiseux solutions are not new
  topics. The decreasing-denominator pattern of `u_d` is prior
  (Chyzak–Dreyfus–Dumas–Mezzarobba Remark 2.18, Gontsov–Goryuchkina); only
  exact orders are claimed. The polynomial-field identity is a consistency
  check, not a priority claim. Not a factorization theorem; the primality
  example is cited.
- Scope of source 01: membership in `k((t^δ))` is necessary, not sufficient;
  strong evaluation is not valuation convergence; coefficient descent is for a
  fixed coefficient field; the Newton-weight test decides existence in the
  full field, not omnific existence and not whether an encoded series is a
  solution. Pairwise independence is not independence of longer tuples.
- Boundaries: false for `d = 1`, for repeated or negative parameters
  (`T_1 + T_1^{−1} + T_2 + T_2^{−1}` is fixed by `S_{−1}`); fails in positive
  characteristic (Frobenius; the prime-field formula covers only `F_p`
  coefficients and the support lattice); fails with nonconstant coefficients
  (`S_d u_d − u_d = ω^d`); real rank is not an exact upper bound for real
  dilations (`ω`, `ω^{√2}`); nothing about full first-order theories, and no
  contradiction with the single-dilation report's undecidability. There is no
  classification of infinite supports of finite rank and no bound on order
  type or denominators; the exact orders of `u_{d,ℓ}` (`ℓ ≥ 2`) and of the
  iterated telescopes are not proved. Implicit relations with nonintegral `q`
  are not classified.
- The Euler derivations are auxiliary probes, not the Berarducci–Mantova
  derivation; `S_q` is not a power map, an exponential or an argument
  dilation; nothing on factorization, primality, Diophantine decidability,
  normalization fibres, analysis, birthdays or first-order decidability. No
  independence over all of `No[i]` (impossible); bases are fixed before fresh
  scales; the families are not transcendence bases; `(No[i], S_d)` is not
  difference closed (`S_d x − x = 1` has no solution); `C` is not embedded in
  `Oz`. Exact order is not reconstruction. The denominator results are
  necessary conditions only.
- Algorithms assume exact finite input and do not decide arbitrary surreal
  equalities; source 01's decision procedure is a termination result, not
  implemented; source 03's certificate produces no relation. The finite checks
  (91, 549 with 1,918 comparisons, and 1,490 check units) certify no infinite
  statement.
- Source comparisons are pinned and not line-by-line; source 01 compared
  Nishioka–Nishioka at abstract level and cited the late-2025 preprints from
  their abstracts; source 03 read Kuhlmann–Matusinski only in abstract.
- Added: (W1, R20) no `adr:` label has a Lean mapping; (W2) Mahler's 1983
  criterion, recorded by Nishioka–Nishioka, is prior for the rank-one
  power-series case of Theorems 7.1, 7.3 and Corollary 7.4; (W3, R21) the
  partial data for Question 5 do not answer it, and Question 8 is answered only
  in its relative-rank part; (W4) none of the single-dilation report's
  questions is answered; (W5) not the holonomic report's argument dilations;
  (W6) nothing on exponential lifts or the surcomplex-automorphisms questions;
  (W7) source 01's repository statements stand at its placement; (R22) source 02
  does not answer source 03's question on `u_{d,ℓ}`; (R23) source 03's text says
  its build record holds file hashes, but the shipped
  `data/03-support-rank-BUILD_RECORD.json` has none.

## Source 02 and Source 03

| Local | Manuscript | Pin | Contributes |
|---|---|---|---|
| **03** (base of the part) | *Support Rank and Algebraic Independence of Dilation Orbits* (29 pages, US Letter, 23 September 2026; batch 33, manuscript 04, archive `surreal_dilation_rank_research`) | `efc5446` | The theorems over an ordered scalar field `𝓕` relative to `K_H(k)` (Sections 19–21); rational support descent and the reduced-quotient formula (Lemma 22.1, Theorem 22.3); the six-term rank-three certificate, the affine-span, relative and power-sum examples and the polynomial-time certificate (Section 23); `Ξ` under real dilations, the rank-one character lemma, the order-two proof without Theorem 10.1, the `u_{d,ℓ}` family (Section 24); the ordinal family, uniform tail and one-witness corollary (Theorems 25.2–25.3, Corollary 25.4); the prime-field formula (Theorem 26.1); the real-rank boundary; twelve questions. Files `03-support-rank-*`. |
| **02** | *Support Rank and Algebraic Freeness under Surreal Dilations: exact finite-profile order, higher-order support bounds, and free omnific difference algebras* (23 pages, A4, 23 September 2026; batch 33, manuscript 02, archive `surreal_dilation_rank`) | `958b5c4` | The same central theorems over `Q` (Theorems 20.7, 21.2, Corollaries 20.11, 21.3, 21.4, Theorem 25.1); the vector-valued greedy determinant (Theorem 20.8); the coefficient-matrix route, Jacobian-rank lemma and algorithm (Lemmas 22.4, 22.5); the five-term rank-three certificate (Example 23.2); `Ξ − ω` and `Z^s` shifts (Corollary 24.3); the character extension lemma and denominator index (Lemma 24.4, Theorem 24.5); telescopes of rank `ρ` and order `ρ + 1` (Theorem 24.8, Example 24.9); `κ`-families and free difference algebras (Theorem 25.5, Corollary 25.6); the relative part of Question 8; the non-closure `S_d x − x = 1`; eleven questions. Files `02-dilation-rank-*`. |

Both sources were written against this report; its `article.tex` is the same
file (blob `495d539`) at both pins, at the placement commit `aa9c891` and at
`260c143`, so their descriptions of Proposition 13.4 and Questions 1, 2 and 8
are accurate, not stale. Neither uses Theorem 6.1, Newton–Puiseux or the
Böttcher coordinate.

- **Placement.** Sections 19–27, after the non-claims ledger (Section 18) and
  before the appendices, so that Sections 1–18, Appendices A–C.4 and Research
  questions 1–12 keep their numbers; provenance in Appendix C.5, files and
  rerun in Appendix C.6. Base: source 03, the more general (ordered subfield
  `𝓕` instead of `Q`, real dilations, relative core, more results). Source
  02's proofs use only `Q` and were re-read for hidden stronger hypotheses;
  there are none.
- **Convention converted.** Both sources use growth support (`X^g`,
  `𝗍^γ`, reverse well-ordered supports, largest exponent leading); the part
  uses the report's valuation convention (`t^γ ↦ ω^{−γ}`): supports negated,
  greedy maxima become minima, the leading determinant term is the one of
  least valuation (the largest `ω`-exponent). Surreal statements are in
  `ω`-notation, where the conventions agree.
- **Renamed symbols** (Section 19.2): `F → 𝓕` (ordered subfield), `G, V → Γ`,
  `K_G, 𝓗_k(V) → K_Γ(k)`, `K_H, 𝓗_k(H) → K_H(k)`, `ρ_{F,H}, r_H, r → ρ_{𝓕,H}, ρ`,
  source 02's `ρ(f) → ρ_cm(f)`, `aord_{S_d,B} → aord_{d,𝔅}`, `D_λ, D_ℓ, D_i →
  ∂_λ, ∂_i` (the report reserves `D`), `ℓ → λ`, `Λ(g) → λ⃗(γ)`, greedy `g_j → b_j`,
  supports `A, E → Σ`, leading exponent `E → η`, dilation set `Q → 𝒬`,
  relations `P → F`, groups `L → Λ`, `B = supp P ∪ supp Q → Σ_{P,Q}`, twist
  variable `T → τ`, monomials `X, Y, Z → T_1, T_2, T_3`, `Y → Ξ − ω`,
  `Z_α, b_{αn} → Ξ_α, g_{α,n}`, `Y_α, γ_{α,n}, B, T → Υ_α, h_{α,n}, ν_0, 𝓘`,
  base fields `E, F, B → 𝔅`, parameter set `P → 𝔓`, `Z_r, P → 𝒵_ρ, w_ρ`,
  `A_y; N, M → 𝒟_y; N, N'`, `V_s → u_d^{[s]}`, twists `T_j, σ_χ → τ_j, τ_χ`,
  `e_j → σ_j` (elementary symmetric), certificate `M, B, C → N_0, B_0, c_*`,
  coefficient automorphism `ρ → φ`. Source 02's increasing parameters are
  listed decreasingly; its sign `(−1)^{m(m−1)/2}` is stated in Remark 20.9.
  The shipped audits keep the sources' notation.
- **Printed once** (both sources): the Euler derivations, Jacobian criterion,
  greedy dominance, rearrangement, extremal tuple and leading term; the
  support-rank obstruction (02 Thm 4.3 = 03 Thm 1.1 at `𝓕 = Q`); the
  relation-rank corollary (02 Cor 4.4, 03 Cor 5.2); the exact finite-support
  formula (02 Thm 5.1, 03 Thms 1.2/5.1 and Cor 6.6); the uniform matroid (02 Rem
  5.3, 03 Cor 6.5); `Ξ` (02 Thm 7.1, 03 Thm 8.2); the block theorem (02 Thm
  7.3, 03 Thm 9.1); the rational example `(T_1 + T_2)/(1 + T_1T_2)`; the
  Frobenius and negative-dilation counterexamples. Near-identical questions
  (field degrees, small relations, overlapping spans, support structure,
  formalization) are printed once with both formulations.
- **Second routes kept:** functionals before the greedy basis (Remark 20.9);
  the coefficient-matrix proof of Theorem 22.2; the two character arguments
  (Theorem 24.5, Lemma 24.6); two further proofs that `u_d` has order two
  (Proposition 24.7, Theorem 24.8), beside Theorem 13.2. Both rank-three
  certificates are printed; they differ in example and row order (the sign of
  `−96` is the row order).
- **Merge additions** (marked `[merge]`): the conventions and notation table;
  Remark 20.12 (Question 5 partial datum); the reconciliation of the two
  hierarchies (Remark 24.10: source 02's telescopes raise the rank with gap
  one and do **not** decide source 03's `u_{d,ℓ}` question); the comparison of
  the two fresh-scale constructions and with the independent-copies report;
  the sign check of Example 23.2; non-claims R20–R23.
- **Stale text corrected in this report:** status notes after Proposition 13.4,
  after Research questions 1, 2, 5 and 8, in the closing recommendation of
  Section 16, in non-claim S22 and in Appendix C.1; the title page, abstract,
  status box, Section 1.4 and Section 1.5; this README. **Priority correction:**
  Theorem 13.3 with all `a_j = 1` is Melánová–Sturmfels–Winter's Proposition 3
  (read for this report in the arXiv HTML version), which source 01 did not
  cite; the credit follows Theorem 13.3.
- **Corrected in printing:** source 03's five unclosed quotation marks around
  question titles; its false statement about hashes in its build record
  (R23). No mathematical statement of either source was found false.
- **Verified for this merge.** Both suites were rerun on copies (below). The
  proofs were re-read against their statements, including the conversion to
  valuation support; the sign of Example 23.2 was recomputed by hand.

## Relation to the neighbouring reports

Section 1.5 of the article gives these relations with labels.

**[single-dilation-hahn-support](../single-dilation-hahn-support/)** (`dsup:`)
— the same operator and the nearest report. Lemma 3.3 at `d = 2` is
`dsup:lem:monomialrecognition` (same least-term proof), and `Fix(S_d) = k` is
`dsup:eq:dilationfixed`. The boundary equation `S_d u_d − u_d = ω^d` is, at
`d = 2`, the Conway form of the second series of `dsup:ex:opposite` after one
application of `S_2` (`u_2 = S_2 y` with `y = Σ_{n≥1} ω^{2^{−n}}`,
`S_2 y − y = ω`); that report calls the example illustrative, and only the
exact order is claimed here. **Partial answer to this report's Question 5:**
for divisible `Γ` and `q = a/b`, `dsup:lem:rationalrecognition` shows that the
nonzero solutions of `(S_q x)^b = x^a` are exactly `μ_{|a−b|}(k) t^Γ`. So
implicit relations `F(y, S_q y) = 0` with nonintegral `q` do have nonconstant
solutions; these are monomials, consistent with Theorem 11.1 (since `b ≥ 2`)
and with the cyclic-support conclusion, and with the rank bound of Remark
20.12. The source's Section 14.3 leaves the nonintegral case open, which is no
contradiction; the general case stays open. The linear and multiplicative
equations of `dsup:thm:dilationcohom` and the undecidability of
`dsup:thm:undecidable` are credited; none of the three questions of
`dsup:sec:questions` (in particular definability from other exponent
automorphisms) is answered. Source 02 read that report's README at its pin for
dilation conventions; nothing of it is used as a premise.

**[independent-surreal-copies](../../surreal/independent-surreal-copies/)**
(`isc:`) — the fresh-parameter constructions of Section 25 separate a set-sized
base by bounding the second-level supports of its exponent span, the
localization of `isc:cor:parameters`. That report's subject is independent
copies of `No` and their intersections, not dilation orbits; neither report
uses the other.

**[surcomplex-field-automorphisms](../surcomplex-field-automorphisms/)**
(`saut:`) — `S_d` is its `S_a` at `a = d` (`saut:eq:dilation`), built by
`saut:thm:monomial`; none of its questions is addressed.

**[exponential-automorphism-rigidity](../../surreal/exponential-automorphism-rigidity/)**
(bare labels) — on `No`, `S_d` is the canonical lift (`prop:hahn-lift`) of the
value-group dilation by `d`, which has no exponential lift (`thm:dilation`);
so `S_d` does not commute with `exp`. That report's subject, which value-group
automorphisms admit exponential lifts (`q:image`), is not this report's
subject, and source 01's last question (interaction with the surreal
exponential) stays open, as does source 03's question 29.

**[holonomic-rigidity-for-entire-hahn-functions](../holonomic-rigidity-for-entire-hahn-functions/)**
(`hol:`) — its dilations are argument dilations `f(z) ↦ f(qz)` of entire Hahn
functions in linear `q`-difference equations (`hol:main:q`,
`hol:sec:qnecessity`), and its "order" is a differential order. It shares a
word with this report, not a theorem.

**[dynamics-and-normal-forms](../dynamics-and-normal-forms/)** — cited by
source 01 as a point of contact; it has no superattracting germs or Böttcher
coordinates (they occur in no other report), and nothing of it is used.

No other report treats algebraic independence of exponent dilates.

## Provenance and corrections (Appendix C)

Source 01 compared itself with the collection at `b895e86`; Section 1.2 keeps
that comparison as written. Checked at its placement commit `21375f8`, its
repository statements stand (Appendix C.2). Sources 02 and 03 compared
themselves with this report at `958b5c4` and `efc5446`; their statements about
it are accurate (Appendix C.5).

References checked for this report (Appendices C.3 and C.5):

- L'Innocente–Mantova: Theorem B of arXiv:1710.07304v5 states that
  `ω^{√2} + ω + 1` is prime in `Oz` (Gonshor's conjecture); the attribution is
  correct. The journal DOI is listed on arXiv; the volume number was not checked.
- Nishioka–Nishioka (Tsukuba J. Math. 39(2), 251–257): bibliographic data
  confirmed and the open-access full text read; see W2. Its example
  `f(z²) = f²/(1 − 2f²)` has the reciprocal solution `z^r + z^{−r}`, the
  identity `S_2 y = y² − 2` of Section 12.1.
- Gontsov–Goryuchkina (J. Symbolic Comput. 128, 102399): bibliographic data
  confirmed through the DOI registry; not read.
- Faverjon–Poulet (arXiv:2511.18877) and Faverjon–Roques (arXiv:2512.10661):
  titles, authors and dates confirmed; abstracts only, as in the source. The
  source's one-line summary of the second (generalized Mahler-series structure)
  is not confirmed by its abstract, which describes a purity theorem.
- Melánová–Sturmfels–Winter (Experimental Math. 33(2), 225–234; arXiv:2106.13981):
  Proposition 3 read in the arXiv HTML version during the merge: `m ≤ n` power
  sums of distinct positive degrees in `n` variables give a dominant map, by
  Vandermonde-times-Schur Jacobian minors.
- Neumann, Mannaa–Coquand, Salerno–Silverman, Chyzak–Dreyfus–Dumas–Mezzarobba
  and Faverjon–Roques (arXiv:2412.04928) were confirmed during placement.
  Mahler (1983) is cited as reported by Nishioka–Nishioka and was not consulted;
  Basu–Pollack–Roy, the encyclopedia page, Gonshor, Edmonds,
  Kuhlmann–Matusinski and Beecken–Mittmann–Saxena were not checked here and are
  cited as the sources cite them.

## Build and reproduce

TeX Live or MiKTeX with newtxtext/newtxmath, amsmath/amsthm, mathtools,
geometry, microtype, xcolor, booktabs, tabularx, array, enumitem, fancyhdr,
needspace, tcolorbox, xurl, hyperref, aliascnt and cleveref. No external
figures or bibliography file.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX) has 65 pages and no errors, undefined references
or citations, multiply defined labels, duplicate destinations, LaTeX or package
warnings, or overfull or underfull boxes. A clean compile proves nothing about
the proofs. Do **not** run the delivered build scripts
(`code/02-dilation-rank-build.py`, `code/03-support-rank-build.sh`,
`code/03-support-rank-build.ps1`) in this directory: they run `pdflatex` on an
`article.tex` beside themselves, and the source 03 scripts first run its
verifier in place (see below).

All three suites use exact arithmetic, and none is an implementation of
infinite Hahn series. Run each on a copy, from this directory, with a fresh
scratch directory `$T`. Do not use Python optimization flags that disable
assertions.

**Source 01** (`code/verify.py`, Python 3.9+, SymPy; `data/requirements.txt`
pins 1.14.0) prints its report and **writes `verification_results.json` beside
itself, overwriting any file of that name**; Appendix B and `SOURCE_AUDIT.md`
describe the flat delivered layout.

```sh
python -m pip install -r data/requirements.txt
cp code/verify.py "$T"/ && (cd "$T" && python verify.py > run.txt)
diff <(grep -v '"python"' "$T/verification_results.json") \
     <(grep -v '"python"' data/verification_results.json)
```

This was run for the write under Python 3.14.4 with SymPy 1.14.0: exit code 0,
`"status": "PASS"`, and the written file agrees with
`data/verification_results.json` except for the recorded Python version
(3.13.5 in the delivery). The 91 checked instances are 6 inverse Böttcher
expansions through degree 32, 20 resultant cases (10 polynomials at `d = 2, 3`: one
irreducible factor of bidegree `(dM/g, M/g)` with multiplicity `g`), 10
Jacobian instances, 45 finite telescoping identities (with their boundary
terms), 4 Frobenius examples and 6 Newton-weight tests. They check finite
instances only; the decision procedure of Theorem 15.2 is not implemented.

**Source 03** (`code/03-support-rank-verify.py`, Python 3.9+, standard library
only; about one second). Its default output is `../data/verification_results.json`
relative to the script, which in this layout is **source 01's record**: run in
place without `--output` it would overwrite `data/verification_results.json`.
It rewrites its record in place; its delivered README and article describe
`code/verify.py` and `data/verification_results.json`.

```sh
mkdir -p "$T/code" "$T/data"
cp code/03-support-rank-verify.py "$T/code/verify.py"
(cd "$T" && python code/verify.py)
diff "$T/data/verification_results.json" data/03-support-rank-verification_results.json
```

Run for this merge under Python 3.14.4: exit code 0, status `PASS`, 1,490
check units (85 full-rank and 60 partial-rank characteristic-zero Jacobians,
72 characteristic-`p` Jacobians, 4 rational-function Jacobians, 72 Frobenius
identities, 1 negative-dilation example, 528 rank and inverse-matrix entries,
668 power-sum reconstructions), worked certificate `96 T_1^4 T_2^4 T_3^7` with 97
terms; the written record is identical to the shipped one up to line endings
(it records no interpreter version or timing).

**Source 02** (`code/02-dilation-rank-verify.py`, Python 3.9+, SymPy;
`data/02-dilation-rank-requirements.txt` pins 1.14.0; about ten seconds) writes
`verification_results.json` in the current directory unless `--output` is
given; its delivered article names `verify.py` and `build.py`.

```sh
python -m pip install -r data/02-dilation-rank-requirements.txt
cp code/02-dilation-rank-verify.py "$T"/
(cd "$T" && python 02-dilation-rank-verify.py --output out.json)
diff "$T/out.json" data/02-dilation-rank-verification_results.json
```

Run for this merge under Python 3.14.4 with SymPy 1.14.0: exit code 0, 549
named cases (257 vector-valued greedy determinants, 133 logarithmic Jacobians,
140 truncated telescopes, 10 rational profiles, 2 explicit relations, 6
Frobenius and 1 sign counterexample) with 1,918 basis comparisons, worked
leading term `−96 T_1^9 T_2 T_3^6` with 45 terms; the output agrees with the
record except for the recorded Python version (3.13.5 in the delivery) and
elapsed time (3.852 s in the delivery, about 10 s here).

The build records `data/02-dilation-rank-BUILD_REPORT.json` and
`data/03-support-rank-BUILD_RECORD.json` describe the delivered PDFs (23 and
29 pages), which are not shipped. Source 03's text says its build record holds
file hashes; it does not.
