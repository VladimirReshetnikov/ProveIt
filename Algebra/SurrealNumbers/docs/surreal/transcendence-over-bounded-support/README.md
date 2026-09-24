# Bounded-Support Hahn Arithmetic

**Cofinal descent, optimal support thresholds, maximal transcendence, and a
Galois rank dichotomy**
Two-source research report, 22 and 23 September 2026, built from two
research drafts prepared with ChatGPT:

- **source 01** (Sections 1–10, Appendices A–B), *Bounded-Support Hahn
  Arithmetic*, item 07 of batch 19. Its own repository audit is pinned to
  `048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`; its raw source and artifacts
  were placed in `30dfb4f`, and the editorial article and first repository
  PDF were assembled in `ed88b8f`.
- **source 02** (Sections 11–19, the Galois part), *A Galois Rank Dichotomy
  for Omnific Fraction Fields*, manuscript 06 of batch 32, placed as an
  addition in `7d04483` with the local prefix `02-`; pinned to
  `343dc2c471212bb9b53ff4623bace2e1943f255b`. See "Source 02" below.

```
article.tex         the report, standalone LaTeX with an internal bibliography
article.pdf         the compiled report, 62 pages
README.md           this guide
research_audit.md   source 01: repository and literature audit, as delivered
02-galois-rank-SOURCE_AUDIT.md   source 02: source, contribution and proof audit, as delivered
code/  build.py          source 01: three-pass pdfLaTeX builder (expects the flat delivered layout, see "Build")
       coefficients.py   source 01: the explicit countable coefficient code; standard library only
       verify.py         source 01: exact finite regression checks; imports coefficients.py
       02-galois-rank-build.py    source 02: three-pass builder for its unshipped manuscript (see "Build")
       02-galois-rank-verify.py   source 02: exact finite regression checks (Python 3.10+, SymPy)
data/  verification.json the delivered run of verify.py: 3,163 assertions in 12 groups, all passed
       build_audit.json  layout audit of source 01's delivered 24-page PDF (not of this PDF)
       manifest.json     SHA-256 digests of source 01's delivered files (see "Provenance")
       02-galois-rank-verification_results.json   delivered run of 02-galois-rank-verify.py: 8,950 assertions in 18 groups, all passed
       02-galois-rank-verification_console.txt    its console output, byte-identical to the results file
       02-galois-rank-build_audit.json            build and hash record of source 02's delivered 27-page PDF (not of this PDF)
       02-galois-rank-requirements.txt            sympy==1.14.0
```

Every label in `article.tex` carries the prefix `bst:`; the labels of the
Galois part carry the sub-prefix `bst:gr:`. The report had 74 labels before
batch 32 and has 153 now: the merge of source 02 renamed or removed none and
added 79, all `bst:gr:`. Every section, theorem-like and equation number of
Sections 1–10 and Appendices A–B is unchanged (checked against a build of the
committed text); the Galois part is inserted after Section 10 and before the
appendices, with its equations numbered within its sections. Neither source
manuscript, nor its PDF or delivery README, is shipped. The code, data and
audit files are the delivered bytes.

## What the report claims

Items 1–8 are source 01's (Sections 1–10, Appendix A); the Galois part of
source 02 is summarized in "Source 02" below.
Numbers refer to the built `article.pdf`. Throughout, `G` is a nonzero
set-sized ordered abelian group, `B_G(K)` is the ring of Hahn series in
`K((t^G))` whose support is **bounded above in G**, `F_G(K)` is its fraction
field, and `κ = cf(G)` is the least cardinality of a subset of `G` unbounded
above.

1. **The sharp support theorem, Theorem 5.3** (`bst:thm:independent`; preview
   Theorem 1.1). For `K` of characteristic zero there are a strictly increasing
   cofinal sequence `a_α` (α < κ) and positive integers `c_A(α)` such that
   the `2^κ` series `Y_A = Σ_{α<κ} c_A(α) t^{a_α}` (A ⊆ κ) are algebraically
   independent over `F_G(K)`. All have the one support `{a_α}`, of order
   type κ. The mechanism is a separated exponent system (Lemma 4.2), a
   support-band estimate (Lemma 4.4) and a finite-pattern coding lemma
   (Lemma 5.1) with integer-grid detection (Lemma 5.2).
2. **Optimality, Corollary 5.4.** The least support cardinality, and the least
   support order type, of an element transcendental over `F_G(K)` are both κ.
   So countable supports suffice exactly when `cf(G) = ℵ_0`.
   Corollary 5.5 (bounded perturbations) and Corollary 5.6 (`2^κ` independent
   elements in every valuation ball) follow.
3. **Exact degrees.** `trdeg_{F_G(K)} K((t^G)) = 2^κ` when `|G| = cf(G) = κ`
   and `|K| ≤ 2^κ` (Corollary 5.8), and `= 2^{ℵ_0}` for every nonzero
   `G ⊆ R` and `|K| ≤ 2^{ℵ_0}` (Corollary 5.9). The upper bounds are a
   separate cardinality count.
4. **Simultaneous descent, Theorem 3.2** (preview Theorem 1.2). For fields
   `K ⊆ L` and a nonzero **cofinal** subgroup `H ⊆ G`, `K((t^H))` and
   `F_G(L)` are linearly disjoint over `F_H(K)`, in any characteristic.
   Corollary 3.3: `F_G(L) ∩ K((t^H)) = F_H(K)`, relation ideals and finite
   algebraic degrees are preserved. Corollary 3.4: at an order unit `u`,
   `K((t^u)) ∩ F_G(L) = K(t^u)`. In characteristic zero cofinality is also
   necessary (Section 3.4, using Theorem 5.3).
5. **Explicit witnesses.** Corollary 4.6 (one lacunary series); Theorem 6.1:
   `Σ_{n≥2} q_j^n t^{n!u}` for multiplicatively independent `q_j > 0`, e.g.
   primes, are independent over `F_G(L)` for `L ⊇ R`; the integer family `W_A`
   of equation (18) is a continuum-sized independent family, each member
   computable relative to `A`.
6. **Rank structure, Section 7.** `B_G(K)` is a field iff `G` has no order
   unit, and is then the union of the Hahn fields over proper convex subgroups
   (Theorem 7.1); it is real closed or algebraically closed when `G` is
   divisible and `K` is (Corollary 7.2). With an order unit and `G` divisible,
   the top-rank presentation (Proposition 7.3) and the **imported**
   upper-support theorem of L'Innocente–Mantova (Proposition 7.4) give the
   units: support in one coset of the maximal proper convex subgroup
   (Corollary 7.5).
7. **Actual surreal numbers, Section 8.** Via `t^g ↦ ω^{-g}`: continuum many
   positive infinitesimals `η_A = Σ c_A(n) ω^{-n!}` and the explicit `η_p`,
   independent over the bounded fraction field `𝓕_C` of real-exponent,
   complex-coefficient series, with exact degrees `2^{ℵ_0}` (Theorem 8.1);
   for every infinite regular κ, in `G_κ = ⊕_{α<κ} Q ω^α`, `2^κ` positive
   infinitesimals `Σ c_A(α) ω^{-ω^{α+1}}` and exact degrees `2^κ` (Theorem
   8.2). Section 8.4: along the noncofinal embedding `R ⊂ Rω + R` every
   real-exponent series becomes a bounded-support coefficient.
8. **Conditional GCD descent, Appendix A.** *Assuming* the hypothesis
   `(GCD_{R,K̄})` that `B_R(K̄)` is a GCD domain, `B_H(K)` is a GCD domain for
   every nonzero `H ⊆ R` (Theorem A.1), which would answer the pre-Schreier
   question after Example 9.1.3 of L'Innocente–Mantova; a universal form of the
   hypothesis gives the GCD property at every divisible rank.

## What the report does not claim

This section lists source 01's non-claims; source 02's 23 are summarized in
"Source 02" below and listed in Section 18.6 of the article.
No non-claim of the manuscript was dropped. The article states each at its
point of use; Section 10.3 and Appendix B collect the principal ones, and the
delivered `research_audit.md` repeats most of them. There are 24, grouped here.

**Status and verification (4).** Not refereed. No Lean implementation mapping for its results. The 30 standard statements
are listed in the collection's source inventory, which is not proof coverage. 3,163 is an assertion count, not a
count of theorems; finite checks do not prove any transfinite, cardinal or
summability statement. PDF byte-for-byte reproducibility is not claimed.

**Priority (5).** Proposed contributions only; the literature search was
targeted, not an exhaustive MathSciNet, Zentralblatt, thesis or
citation-network audit. The cofinality/nonrationality obstruction is
L'Innocente–Mantova's Proposition 2.4.5 and is **not** claimed new; their
Fact 2.1.1, Fact 2.4.2 and Proposition 3.5.1 are imported. The coding lemma,
linear-disjointness algebra, Hahn-field closedness and Conway normal form are
background. Gonshor's book was not freshly audited. The repository audit was
not line by line, the later revision `6e34651` it observed was not re-audited,
and a negative indexed search is not proof of absence.

**GCD appendix (3).** The hypothesis `(GCD_{R,K̄})` is **not** proved; no
unconditional answer to the pre-Schreier question and no resolution of
Conway's refinement conjecture. The external Lean project
`gaearon/conway-refinement` was read, not built or validated, and is not a
premise. Proving GCD would not remove the transcendental extension, and the
transcendence theorems do not use the appendix.

## Source 02: the Galois part (Sections 11–19)

| | |
|---|---|
| Manuscript | *A Galois Rank Dichotomy for Omnific Fraction Fields: finite covers, independent radical towers, and collapse at a new surreal scale*, prepared for Vladimir Reshetnikov with ChatGPT, 23 September 2026; 27-page PDF (4 front-matter + 23 numbered pages) |
| Batch, archive | batch 32, manuscript 06; `surreal_galois_rank_article` (main file `galois_rank_dichotomy.tex`), delivered in `aa268a4`, placed as an addition in `7d04483` with local prefix `02-` |
| Pin | `343dc2c471212bb9b53ff4623bace2e1943f255b`; at the pin this report had Sections 1–10 and Appendices A–B with today's numbering, so its citations of Theorem 3.2, Corollaries 3.3–3.4, Theorem 7.1, Corollary 7.2 and Section 8.4 still match |
| Contributes | every result, proof, example, question and non-claim of Sections 11–19 |
| Placement | new Sections 11–19 after Section 10 and before the appendices (no existing number changes); short pointers marked "Added in batch 32" in Sections 3.2, 3.3, 3.4, 7.1, 8.4 and 10.1; a corrected provenance paragraph in Section 1.4; the title page, subtitle and abstract; one row in the Appendix B table |

**Setting.** `G` a nonzero set-sized ordered abelian group (divisible where
stated), `K = R` or `C` (or any field where stated), `F_G(K)` the
bounded-support fraction field of the report, `s = t^u` for an order unit
`u`. Via `t^γ ↔ ω^{-γ}` these are subfields of `No` and `No[i]`, and
`F_G(K)` is also the fraction field of the omnific-type ring
`A_G(D,K) = D + K((t^{G<0}))` for every unital `D ⊆ K` (Proposition 12.1).

**Results** (numbers of this report).

- **Galois rank dichotomy** (Theorem 11.1; proofs in 14.7, 13.5). For divisible
  `G`: without an order unit `F_G(C)` is algebraically closed and `F_G(R)`
  real closed; with one, every product of at most `c = 2^ℵ0` finite groups is
  a Galois group over `F_G(C)` inside `C((t^G))`, and `1 − t^u` has no square
  root in `F_G(C)` or `F_G(R)`.
- **Descent tools** (Section 12). The fraction bridge (12.1) and
  complexification `F_G(C) = F_G(R)(i)` (12.3); finite coset slices at an
  order unit (Lemma 12.4); transport of degrees, minimal polynomials, Galois
  groups and the whole intermediate-field correspondence under any cofinal
  descent (Corollary 12.6).
- **Finite covers** (Section 13). Riemann existence with a split place over
  `s = 0` (Lemma 13.1) gives every finite group (Theorem 13.2); the local
  Galois envelope `E_0` of `C(s)` in `C((s))` keeps its whole Galois group
  over `F_G(C)` (Theorem 13.3); disjoint branch loci give products of
  `≤ c` finite groups (Lemma 13.4, Theorem 13.5), all continuous quotients of
  the absolute Galois group (Corollary 13.6). Divisibility is not needed.
- **Radicals and closedness** (Section 14). The normalized roots `r_{a,n}` of
  `1 − as` (Lemma 14.1): `X^n − (1 − as)` irreducible (Proposition 14.2); `q`
  distinct `a` give degree `n^q` and group `(Z/n)^q` (Theorem 14.3); the whole
  tower `E_T` has group `∏_{a∈T} Ẑ`, degree `max(|T|, ℵ0)` and group
  cardinality `2^{max(|T|,ℵ0)}` (Theorem 14.5); the exact closedness boundary
  (Theorem 14.7) and Example 14.8 (countable cofinality without order unit).
- **Symmetric, real, cardinal** (Section 15). `X^m − X − t^u` has group `S_m`
  (Theorem 15.1); real multiquadratic extensions with group `∏ Z/2`
  (Proposition 15.3); `Gal(E_T/F_G(R)) ≅ (∏ Ẑ) ⋊ C_2` with inversion
  (Theorem 15.4); for `0 ≠ G ⊆ R`: `|F_G(K)| = c`, `|absolute Galois group| = 2^c`,
  exactly `c` quadratic extensions (Theorem 15.5).
- **Rank transitions** (Section 16). A dominating `θ` puts the whole old Hahn
  field `K((t^H))` into `B_G(K)` with the single denominator `t^{−θ}`
  (Theorem 16.1); for divisible `H` every finite extension of `F_H(C)`
  splits completely over `F_G(C)` (Theorem 16.2); **all-or-nothing
  transition** (Theorem 16.3): cofinal `H ⊆ G` keeps every finite extension a
  field of the same degree (restriction of absolute Galois groups surjective),
  noncofinal splits all (restriction trivial); the real counterpart absorbs a
  real closure (Proposition 16.5); for `G = Qθ ⊕ H` the new field again
  realizes every finite group (Theorem 11.3).
- **Actual surreals** (Section 17). `√(1 − ω^{−1})` is not a fraction of
  omnific integers with real exponents but is `(ω^ω − ½ω^{ω−1} − …)/ω^ω`
  with exponents in `Qω + R` (equations 17.1–17.2), where
  `√(1 − ω^{−ω})` is again missing; the tower `Ω_n = R + Qω + … + Qω^n`
  (Theorem 17.1): each stage realizes every finite group, each splits over
  the next, and the union is a proper algebraically (real) closed subfield.
- **Twelve research questions**, Questions 19.1–19.12 (absolute Galois group,
  kernel, embedding problems, relative algebraic closure, minimal
  enlargement, integral closure, real realization, nondivisible and
  positive characteristic, cardinally restricted supports, functorial
  transitions, effective certificates, formalization).

**Renamed symbols** (Section 11.2). Source 02 → here: `Γ, k` → `G, K`;
its calligraphic `K_Γ(k)` (the **full** Hahn field) → `K((t^G))` (here `K`
is always a coefficient field); `B_Γ(k), F_Γ(k)` → `B_G(K), F_G(K)`;
`A_Γ(D,k)` → `A_G(D,K)` (the independent-copies report writes
`A_k(H)`, arguments reversed); `P_Γ(k), I_Γ(k)` written out (its `I_Γ` is not
the relation ideal `I_K(z)`); `z = t^u` → `s` (here `z` is a germ or tuple);
finite extensions `L` → `Λ` (here `L` is a coefficient field); finite groups
`H, H_j` → `Φ, Φ_j` and Galois subgroups `H` → `Ψ` (here `H` is an exponent
subgroup); absolute Galois group `G_E` → `𝔊_E`; inclusion `Γ ⊆ Δ` →
`H ⊆ G`; dominating `h` → `θ` (as in Section 8.4); `Γ_g` → `C(g)`; tower
`Γ_n` → `Ω_n` (distinct from `G_κ`); `F_0^R, F_0^C` → `F_R(R), F_R(C)`, that
is `𝓕_R, 𝓕_C` of Section 8.2; `U_0, U_Γ` → `E_0, E_G`; its two definitions of
`E_T` are one; counts `s` → `q`; `f(x) = x^m − x` → `φ`. The notation guide's
`F_Γ = R((t^Γ))` is never meant.

**Printed once** (credited at the original place). Source 02's Theorem 3.2 =
Corollary 3.4 with `L = K`; Theorem 3.5 = Theorem 3.2 with `L = K` (its
proofs, the coset-projection proof without the coefficient functional, are
Remarks 12.5 and 12.8); Proposition 7.1 = Theorem 7.1 (Remark 14.6); the
positive half of Theorem 7.2 = Corollary 7.2; the inclusion of Theorem 10.1 =
equation (6); its normal-form map = equation (21); its full-surreal remark =
Section 8.4. Theorem 1.1(iii)'s obstruction is the example after
Corollary 3.4 (for `1 + t^u`).

**Merge additions** (marked `[merge]` in the article). Corollary 12.6 stated
at the generality of Theorem 3.2; a corrected ledger entry (the Galois-group
part of source 02's Corollary 3.3 is explicit, not "implicit", in the
paragraph after Corollary 3.3); the reverse implications of Theorem 14.7 for
every real closed or algebraically closed `K` of characteristic zero; the
identification of Example 14.8 with `G_{ℵ0}` and Theorem 8.2(1), and
transcendence of its witness; transcendence of the tower witness
`Σ t^{ω^n}` over the algebraically closed union (Corollary 4.6); the
comparison with neighbouring reports (Section 18.10); the questions as
numbered environments. Source 02 answers none of Section 10.3's questions.

**Stale against the tree.** Source 02's fraction bridge (Proposition 12.1)
was printed after its pin, for `D = Z, Z[i]`, as `isc:prop:boundedfrac` in
the independent-copies report; source 02 is more general (any unital `D`,
any `K`). Its ledger's "implicit" is corrected as above.

**What source 02 does not claim** (Section 18.6, 23 items). No nontrivial
algebraic extension of `No[i]`; `F_G(K)` is not the full Hahn field; the
local envelope is not an algebraic closure; the absolute Galois group is not
determined (cohomological dimension, projectivity, freeness, embedding
problems open) and not claimed free profinite; cardinality is not generator
rank; nothing about inverse Galois over `Q`; prime ideals, integral closure
and arithmetic ramification of `A_G` not classified, and the curve and Hahn
senses of ramification kept apart; divisibility used only for closedness and
universal splitting (without it only extensions already in the Hahn field
are absorbed); the real case does not split `X^2 + 1`; scalar-extension
splitting is not collapse of the old extension; the binary alternative is
for monomial exponent inclusions only, general field embeddings open; one
dominating scale does not absorb the new Hahn field; no CH, GCH or large
cardinals; birthday-bounded and cardinally restricted fields not treated;
nothing in positive characteristic; no single-coordinate description of the
relative algebraic closure and embedding problems only for independent
products; finite checks only; no Lean, no repository build, no referee;
priority not certified, classical inputs credited; no named conjecture
solved; targeted, non-exhaustive repository comparison; PDF reproducibility
not promised; the questions are not claimed open in the literature.

**Verification.** `code/02-galois-rank-verify.py` (exact rationals and
SymPy, seed `20260923`): the delivered run passed **8,950 assertions in 18
groups** (Python 3.13.5, SymPy 1.14.0). Rerun at this merge on a copy with an
explicit `--output` (Python 3.14.4, SymPy 1.14.0): 8,950 passed, output
identical to `data/02-galois-rank-verification_results.json` except the
`python` field. `data/02-galois-rank-verification_console.txt` is
byte-identical to the results file. The SHA-256 digests in
`data/02-galois-rank-build_audit.json` match the unshipped delivered
`galois_rank_dichotomy.tex` and `.pdf`, and the staged files match the
delivery's checksum manifest (not shipped).

**Scope of the theorems (12).** Nothing is transcendental over all of **No**
or `No[i]`: every statement is relative to named set-sized subfields, and
"bounded" is relative to the named exponent group. A family of maximal
cardinality is not asserted to be a transcendence basis. The transcendence
degree for arbitrary `G` is not determined (`2^{cf(G)}` may be smaller than
the Hahn field's cardinality). Finite coefficient fields are not covered; the
positive-integer form is characteristic zero. No differential-independence
theorem. (Since batch 31 the
[holonomic report](../../surcomplex/holonomic-rigidity-for-entire-hahn-functions/)
proves one over this report's base: its source 17 gives `∂_BM`-jet algebraic
independence over the bounded-support field `F_R(R)` for its
finite-private-tail witnesses, `hol:fh:cor:boundedjets` (its Corollary 35.8),
through `hol:fh:lem:bounded`, the order-unit, integer-lattice case of
`bst:thm:descent`. That is a result of that report, not of this one, and the
non-claim stands for this report.) Hahn partial sums are not claimed to converge in the full fine
topology. The bounded-truncation remark after Corollary 5.6 is
information-theoretic, not an undecidability claim; the integer family is not
asserted to consist of computable streams; `coefficients.py` decides no
algebraicity question. The regularity of κ in Theorem 8.2 is genuine; no CH
or GCH is used. No arbitrary-rank supremum formula is assumed for units.
Density is not an algebraicity statement.

## Relation to the neighbouring reports

Section 9 of the article states this in full, with the labels it quotes.

**[tail-spans-and-differential-transcendence](../tail-spans-and-differential-transcendence/)**
(Section 9.1). Different base-field problems, neither implying the other.
There the base is a *full* Hahn field `M((t^Γ))` and transcendence comes from
the coefficients (`tail:thm:coefficient`, for `M` of characteristic zero: algebraic iff the coefficients
generate a finite extension of `M`); here the base keeps the coefficients and
transcendence comes from the support. The witnesses `η_A`, `η_p` here have
integer coefficients and exponents, so they are *elements* of that report's
base `Q((t^Q))`; conversely `√2 ∈ F_R(R)` is not in `Q((t^Q))`. At uncountable
cofinality a countable-support series `Σ √p_n t^{γ_n}` lies in the bounded
ring here but is transcendental over `Q((t^G))` there.
*Overlap:* both prove a relative transcendence degree `2^{ℵ_0}` with explicit
actual surreal witnesses and a separate cardinality upper bound
(`tail:thm:surreal`; Corollary 5.9, Theorem 8.1); both deny that maximal
cardinality means a basis; both show a noncofinal enlargement changing the
answer for the same surreal expansion (its `Q ↪ Q²` example in
`tail:thm:closure`, which loses algebraic approximability; Section 8.4 here,
which erases transcendence over the bounded base).
*Differences:* differential and analytic independence and the exact relation
classification (`tail:thm:tail`) are only there; the simultaneous descent theorem
and exact cofinality-dependent support threshold are only here. Its general
coefficient and tail-span theorems also allow arbitrary ordered groups. Its `(ξ_A)` over all
subsets satisfies `ξ_{A∪B} + ξ_{A∩B} = ξ_A + ξ_B` (`tail:rem:indexfamily`),
whereas `(η_A)` here is independent over all subsets because `c_A` is a
finite-pattern code; this is why the manuscript's `ξ_A`, `ξ_p` were renamed
`η_A`, `η_p`.

**[entire-functions-at-arbitrary-rank](../../surcomplex/entire-functions-at-arbitrary-rank/)**
(Section 9.2; terminology in Section 2.3). **`cf(G)` here is exactly that
report's `cf(Γ)`**, the least cardinality of a cofinal subset of the value
group, and the order unit is its `ent:def:order-unit`. That report
(`ent:rem:one-name`) excludes the ordinal-index sense of "cofinal"; here that
sense occurs only in Lemma 5.1 (a set of indices cofinal in the ordinal κ),
and is flagged there. The parallels are the threshold `ℵ_0`
(`ent:cor:cofinality`: nonpolynomial entire series exist iff `cf(Γ) = ℵ_0`;
Corollary 5.4 here), the order unit (`ent:thm:main`, `ent:thm:units`;
Theorem 7.1 here), and cofinal versus noncofinal enlargement
(`ent:thm:main-extension`(b); Theorem 1.2 here). The objects differ: entire
power series over `C((t^Γ))` with divisible `Γ` there, the bounded-support Hahn
ring here. Its entire ring is proved GCD; that does not supply the hypothesis
of Appendix A, which concerns a different ring.

**[hidden-negative-hermitian-directions](../../surcomplex/hidden-negative-hermitian-directions/)**
(Section 9.3), placed in the same commit, proves independence over the field
`𝒫_Γ` of series supported in finitely generated subgroups (the Puiseux field
for `Γ = Q`) by prime denominators in the exponents. Its prime-tail series have
support bounded above, so they lie in the base `B_Γ(C)` here; the witnesses
`W_A` here (with `u = 1`) lie in `C((t^Z)) ⊆ 𝒫_Q` and are
transcendental over `F_Q(C)`. Thus for `Γ = Q` the two *fields* `𝒫_Q` and
`F_Q(C)` are incomparable. The prime-tail statement uses the chosen
almost-disjoint family, not all infinite prime sets. Without an order unit,
every finitely generated subgroup is bounded above and `𝒫_Γ ⊆ B_Γ(C)`.

**[independent-surreal-copies](../independent-surreal-copies/)** (`isc:`;
Section 9.5 and the paragraph after Corollary 4.6, both added in batch 31).
Its `isc:thm:cofinalgap` prints the root count of Corollary 4.6 at every
cofinality over an arbitrary field, finite fields included, for the series
`1 + Σ_{α<cf(G)} t^{a_α}`; Corollary 4.6 needs countable cofinality and
Theorem 5.3 characteristic zero, so the single-series case at uncountable
cofinality in positive characteristic is not stated here. Its
`isc:thm:sliceddisjoint` (full Hahn fields on two subgroups are linearly
disjoint over the full Hahn field on the intersection) uses the projections
of Lemma 3.1 and is not stated here. A batch-34 sentence at the end of
Section 9.5 notes that its coefficient-field part (`isc:cp:`) compares
itself with Theorem 5.3: `isc:cp:thm:lacunary` and `isc:cp:thm:generic` also
use private indices, but prove differential independence over the compositum
`F k((t^Γ))` or a finite-generation coefficient envelope, with a
coefficient-degree or coefficient-derivation certificate instead of a
support gap.
A batch-35 paragraph after the remark following Corollary 5.9 notes that
its Hahn-join part (`isc:hj:`) reaches the same cardinals over a different
base, the ordinary compositum of two full Hahn subfields of a join: degree
`2^κ` for explicit interleaved groups of cardinality `κ`
(`isc:hj:main:cardinal`) and `𝔠` for dense Archimedean groups
(`isc:hj:main:prime`), where Corollary 5.9 with `G = A + B` gives `𝔠` over
`𝓕_G(K)` as well; the proofs use coordinate-character derivations, not
support gaps, and neither result is deduced from the other. The `RepoIsc`
bibliography entry now also records that these labels were checked at
`8105a52`.

**Notation.** The collection's [notation guide](../../NOTATION.md) writes
`F_Γ = R((t^Γ))`, and the tail-span report writes `B`, `B_0` for full Hahn
fields; the calligraphic `𝓑_G(K)`, `𝓕_G(K)` here always carry both arguments and
mean the bounded ring and its fraction field. The workspace-versus-fine
topology distinction is the guide's "Topologies and strong summation"; the
Lean normal-form bridge is tracked in
[NORMAL_FORM_BRIDGE.md](../../NORMAL_FORM_BRIDGE.md).

**The Galois part** (Section 18.10, batch 32). Its all-or-nothing transition
(Theorem 16.3) is a third instance of the cofinal/noncofinal dichotomy, beside
`ent:thm:main-extension`(b) of the entire-functions report (entire series
stay entire exactly over cofinal enlargements) and the `Q ↪ Q²` example of
`tail:thm:closure` in the tail-span report (a noncofinal embedding loses
algebraic approximability over a *full* Hahn base); different objects,
independent proofs. The independent-copies report's `isc:prop:boundedfrac`
is Proposition 12.1 for `D = Z, Z[i]`. Question 19.9 (cardinally restricted
supports) concerns the kind of field studied in
[first-kappa-coefficients](../../surcomplex/first-kappa-coefficients/) and the
short-support field of
[large-cardinal-embeddings-and-normal-forms](../../foundations-and-computation/large-cardinal-embeddings-and-normal-forms/);
nothing from them is used.

Cardinally bounded Hahn fields, which this report excludes, are studied in
[first-kappa-coefficients](../../surcomplex/first-kappa-coefficients/): omitted
types, completion and spherical completeness of the fields of series with fewer
than `κ` terms.

## Main-text proof review

Sections 1–10 and the conditional implication in Appendix A have received a
mathematical proof review. It expands the support and projection arguments,
tensor-product consequences, polynomial support bands, coefficient coding,
top-rank grouping and normalized GCD descent. The explicit factorial-family
proof now uses a finite Vandermonde matrix over the Hahn field, eliminating
the ordinary-limit step while keeping the theorem's hypotheses.

The convergence wording is corrected: bounded initial Hahn truncations of
the constructed families converge in the named workspace. At countable cofinality these are finite
partial sums; at uncountable cofinality finite subsums do not converge, even
though the family is strongly summable. The article gives the obstructing
valuation neighborhood. Local comparisons now distinguish a sufficient
almost-disjoint construction from a necessary condition and restrict the
prime-tail base comparison to `Γ = Q`.

The 30 standard result statements retain their mathematical content; two
wording clarifications specify extension of relation ideals and that the
integer-grid coefficient object is a field. All 73 labels and result numbers
are preserved. The imported Hahn closedness, iterated presentation,
nonrationality obstruction and upper-support theorem were checked against
L'Innocente–Mantova's cited v5. The GCD input remains a hypothesis; no external
Lean proof was built or adopted. Remaining foundational/source reconciliation
and literature priority remain separate obligations. See
[the review record](../../REVIEW.md); this review adds no Lean mapping.

## Provenance

Two manuscripts. Source 02 (batch 32) and where the merge chose are
described in "Source 02" above and in Section 11.1 of the article. The rest
of this section concerns source 01. Until batch 32 nothing was merged, so no
result of Sections 1–10 is printed twice and no proof was chosen over
another; source 01 contributed every theorem, proof, example, appendix and
non-claim of Sections 1–10 and Appendices A–B. Editorial changes (Section 1.4): the `bst:` prefix on
all 67 delivered labels (none lost; 6 labels added, 73 in all); the renaming
`ξ → η` above; the terminology conventions of Section 2.3; the comparison of
Section 9 and its four bibliography entries; one tagged display changed to
`equation*` to remove a duplicate PDF destination present in the delivered
source. No theorem statement was changed at editorial assembly. The later main-text
review clarifies two statement wordings without changing their intended scope.

**Stale statements corrected**, keeping the pin as provenance:

- "The catalogue contains 36 reports": true at the pin `048b72c`. Raw
  placement `30dfb4f` brought that historical count to 40; assembly followed
  in `ed88b8f`. The former `52c7ab6` citation is unavailable in local history;
  the guide and article now distinguish the two retained commits.
- At the pin, a literal case-insensitive search in tracked documentation
  excluding `docs/new` finds no `lacunary` and two `bounded support` matches,
  in the analytic-geometry guide and article, concerning one unrelated topic.
  At assembly `lacunary` occurs in this report and its audit, though not
  outside this report. The three-duals example `duals:ex:bounded-support` is
  a related concept, not a literal match for `bounded support` at assembly.
  These dated searches make no absence claim about the current collection.
- The normal-form transport "must be linked to the repository's exact proved
  normal-form bridge": the article now points to `docs/NORMAL_FORM_BRIDGE.md`
  and distinguishes the source statement inventory from the Implementation
  mappings table, which has no `bst:` result mapping.
- The fine-topology distinction was cited to the catalogue only; the notation
  guide's table is now cited too.
- File paths: the delivered text and README used the flat delivered layout
  (`verify.py`, `verification.json`, `python build.py`); the article and this
  README now use `code/` and `data/`.

`research_audit.md` is kept as delivered and speaks at its pin (for example
"The catalogue describes 36 reports"). `data/manifest.json` lists digests of
the delivered files: those of `code/*.py`, `data/verification.json`,
`data/build_audit.json` and `research_audit.md` still match; those of
`article.tex` and `README.md` no longer do, because both were rewritten here,
and the delivered `article.pdf` is not shipped. `data/build_audit.json`
describes the delivered 24-page PDF.

## Build

MiKTeX or TeX Live with pdfLaTeX, the AMS packages, New PX text/math,
`geometry`, `microtype`, `booktabs`, `tabularx`, `longtable`, `array`, `xcolor`,
`enumitem`, `fancyhdr`, `needspace`, `titlesec`, `hyperref` and `bookmark`.
Internal bibliography: no BibTeX, no shell escape, no images, no network.
From a copy of this directory (to keep auxiliary files out of it):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three times.
Last build (batch 35, MiKTeX, after the batch-35 paragraph following the
remark after Corollary 5.9, which adds no label and changes no label or
citation number; all 153 labels compared in the `.aux` files against a build
of the committed text): exit 0, **62 pages** (61 in batches 32–34; 32 before the Galois
part, 31 before the batch-31 reciprocal remarks; every statement, section and
equation number of Sections 1–10 and Appendices A–B unchanged), no errors, no
LaTeX or package warnings, no undefined or multiply defined references or
citations, no duplicate PDF destinations, no overfull or underfull boxes. The
log contains one informational line "ignored: Infinite glue shrinkage found
in box being split", at the page break inside the Appendix B `longtable`
(before the batch-35 paragraph there were two, the Galois-part ledger of
Section 18.8 then also crossing a page); a minimal `longtable` test document
produces the same line at every page break with this TeX installation. It is
not a warning.

The delivered `code/build.py` looks for `article.tex` **beside itself**, as in
the flat delivered package, so `python code/build.py` in this directory stops
with "Missing LaTeX source". To use it, copy `article.tex` and `code/build.py`
into one scratch directory and run `python build.py` there; it writes
`.build/` and `article.pdf` in that directory. Run that way on this
`article.tex` it succeeds; with its `-no-shell-escape` flag MiKTeX prints the
harmless `epstopdf` shell-escape warning that the delivered README mentions
(the article has no EPS graphics). `build.py` is kept byte-identical.

Source 02's `code/02-galois-rank-build.py` builds that manuscript, not this
report: it looks for `galois_rank_dichotomy.tex` in the parent of its own
directory, which is not shipped, so here it stops with "Missing article
source"; when it runs it writes `data/build_pass_1.txt`–`build_pass_3.txt`
and, with `--verify`, overwrites `data/verification_console.txt` (delivered
names, not the shipped `02-` names). Do not run it in this directory.
`data/02-galois-rank-build_audit.json` records the delivered 27-page PDF.

## Rerun the checks

**Source 01.** Python 3.10 or later, standard library only. From this directory:

```sh
python code/verify.py --output <scratch>/verification-local.json
python code/coefficients.py
```

`verify.py` writes `verification.json` **in the current directory** by
default; pass a scratch `--output` path, and never run it from `data/`, so
the delivered record is not overwritten. Seed `20260922`; exact integers and
`fractions.Fraction`, no floating point. At placement it was run on a copy
under Python 3.14.4: **3,163 assertions, all passed**, identical to
`data/verification.json` in every field except `python_version` (the
delivered run used 3.13.5). `coefficients.py` prints a 12-term formal prefix
of `W_A` for `A` the even numbers; it computes coefficients, not Hahn sums,
and uses a surjective finite-table code with a repetition coordinate rather
than the bijection of Lemma 5.1, which has the one property the theorem needs.

The main-text review reran the delivered verifier under Python 3.13.14:
all 3,163 assertions passed, with JSON identical apart from `python_version`.
All seven delivered audit/code/data files, including the manifest, remain
byte-identical; its six recorded digests for retained historical files match.
The current PDF was rebuilt with three clean `pdflatex` passes.

**Source 02.** Python 3.10 or later with SymPy
(`pip install -r data/02-galois-rank-requirements.txt`, which pins
`sympy==1.14.0`). From this directory:

```sh
python code/02-galois-rank-verify.py --output <scratch>/galois-rank-local.json
```

Without `--output` the script writes `data/verification_results.json` in
the parent of its own `code/` directory (here: this directory), an
unprefixed file that is not part of this report, so always pass a scratch path (or run on a copy); it never
touches the shipped `02-` record unless pointed at it. Seed `20260923`,
exact arithmetic, no floating point. At the batch-32 merge it was run on a
copy under Python 3.14.4 and SymPy 1.14.0: **8,950 assertions in 18 groups,
all passed**, identical to `data/02-galois-rank-verification_results.json`
in every field except `python` (the delivered run used 3.13.5). These are
finite regression checks; they prove none of the infinite statements.
