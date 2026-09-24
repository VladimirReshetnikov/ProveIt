# Omnific Groups and Lattices

**Algebraic groups, elementary and Chevalley quotients, current Lie rings, and missing lattice minima over the omnific integers**
Merged research report, 23 September 2026, from five manuscripts written
independently on the same day: 06 (the base), 07 and 10 of batch 26 (placed in
`f4c9504`), 11, item 05 of batch 29 (placed in `66d7e55`), and 12, item 07 of
batch 32 (placed in `7d04483`), each numbered here after its file prefix
(`11-`, `12-`). Source 12 is not the source 07 of batch 26.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 95 pages
README.md     this guide
10-shortest-vectors-provenance.md          source 10's provenance and evidence record, as delivered
11-matrix-shadows-SOURCES_AND_SCOPE.md     source 11's repository snapshot, source roles and exclusions, as delivered
11-matrix-shadows-PROOF_AUDIT.md           source 11's own proof review, as delivered
11-matrix-shadows-BUILD_REPORT.md          source 11's build and rendering report, as delivered
12-chevalley-quotients-SOURCES_AND_SCOPE.md  source 12's repository snapshot, literature roles and non-claims, as delivered
12-chevalley-quotients-PROOF_AUDIT.md        source 12's own proof-audit record, as delivered
12-chevalley-quotients-BUILD_REPORT.md       source 12's build and PDF inspection record, as delivered
code/
  06-algebraic-groups-verification.py   source 06 checks (1,108; stdout, file only with --output)
  07-matrix-dichotomy-checks.py         source 07 checks (23; always writes checks-results.json, see below)
  10-shortest-vectors-verify.py         source 10 checks (6 groups; stdout)
  11-matrix-shadows-verify.py           source 11 checks (2,111; always writes verification_results.json, see below)
  12-chevalley-quotients-verify.py      source 12 checks (2,188; always writes verification_results.json, see below)
  12-chevalley-quotients-Makefile       source 12's Makefile, as delivered (names its delivery files, see below)
data/
  06-algebraic-groups-verification-results.txt   recorded run of the source 06 checks
  07-matrix-dichotomy-checks-results.json        recorded run of the source 07 checks
  07-matrix-dichotomy-checks-output.txt          its console output
  07-matrix-dichotomy-requirements.txt           sympy==1.14.0
  10-shortest-vectors-verification-output.txt    recorded run of the source 10 checks
  10-shortest-vectors-requirements.txt           sympy==1.14.0
  11-matrix-shadows-verification_results.json    recorded run of the source 11 checks
  12-chevalley-quotients-requirements.txt        sympy==1.14.0
  12-chevalley-quotients-verification_results.json  recorded run of the source 12 checks
```

Every label in `article.tex` carries the prefix `ogl:`, with the sub-prefixes
`ogl:alg:` (Part I, algebraic groups), `ogl:el:` (Part II, elementary groups),
`ogl:ker:` (Part II, source 11's kernel structure, Steinberg groups and
fragments, Sections 19–21, and its root-kernel lemmas in Section 9),
`ogl:lat:` (Part III, lattices) and `ogl:ch:` (Part IV, source 12's Chevalley
groups and Lie rings, Sections 35–46); the report has 284 labels (168 before
source 11 was added, 202 before source 12; 82 added with source 12; none was
renamed or removed, and no earlier theorem, section or equation number
changed, since Part IV follows the questions of Section 34). The text placed in
`f4c9504` was source 06 with 55 bare labels; no ledger or report cited them,
and they were renamed during the first write (for example `main:real` is
`ogl:alg:thm:real`, `main:elementary` and `thm:invisible` are
`ogl:el:thm:invisible`). The source manuscripts are not shipped; their code,
data and delivered records are, under the prefixes above, byte-identical to the
deliveries. Both `SHA256SUMS.txt` files delivered with 07 and 10 were dropped,
since they list files under their original names; 11 delivered none. The three
`11-matrix-shadows-*.md` files are verbatim and name files under their delivered
names: `omnific_matrix_groups.tex` and its 24-page PDF (not shipped),
`verify.py` (shipped as `code/11-matrix-shadows-verify.py`) and
`verification_results.json` (shipped as
`data/11-matrix-shadows-verification_results.json`). Source 12's
`SHA256SUMS.txt` was dropped for the same reason. Its three
`12-chevalley-quotients-*.md` files and its Makefile are verbatim and name
files under their delivered names: `article.tex` and its 28-page PDF (source
12's manuscript, not shipped), `verify.py` (shipped as
`code/12-chevalley-quotients-verify.py`), `verification_results.json`
(`data/12-chevalley-quotients-verification_results.json`), `requirements.txt`
(`data/12-chevalley-quotients-requirements.txt`) and `SHA256SUMS.txt` (not
shipped); the Makefile's targets therefore do not run from the shipped layout.

## Five sources, one report

| | Manuscript (pages) | Pin | Contributes |
|---|---|---|---|
| **06** | *Omnific Points of Algebraic Groups* (22) | `220784a` | **The base.** Part I (Sections 3–6): the real and Gaussian dichotomies (Theorems 4.4, 4.5), bounded fibers over a torus (Theorem 3.3), orthogonal examples, unipotent kernels and the unitriangular filtration (Theorem 6.2). In Part II: normality of the root-generated subgroup for any constant ring (Propositions 7.2, 7.3), the proof of Theorem 9.1 by division by nearby monomials, the congruence tower (Theorem 10.1), and the boundaries (Section 12). Files `06-algebraic-groups-*`. |
| **07** | *A Matrix-Size Dichotomy over the Omnific Integers* (25) | `fb5c4b5` | Base of Part II: the relative-kernel lemma, the proof of Theorem 9.1 by rescaling a set field (for maps defined only on the kernel), the collision criterion (Proposition 9.7); rank two: amalgam, free-product kernel, countable detection (Theorems 13.2, 14.1, 15.3); the trichotomy (Theorem 16.5); abelian characters (Section 17); cusp residues, non-elementary unipotents, stabilization (Section 18). Files `07-matrix-dichotomy-*`. |
| **10** | *Shortest Vectors and Missing Infima over the Omnific Integers* (26) | `220784a` | All of Part III (Sections 22–32). Files `10-shortest-vectors-*`. |
| **11** | *Arithmetic Shadows of Omnific Matrix Groups* (24) | `9693b28` | Theorem 9.1 again (its Theorem A), with a third proof by root-kernel reconstruction (Theorem 9.2, Corollary 9.3, Lemma 9.4); torsion-freeness, centerlessness, set-sized normal subgroups and conjugacy classes, finite subgroups, a congruence chain and common congruence elements, the profinite completion (Section 19); Steinberg groups (Section 20); set-sized fragments, cardinal and action thresholds and the exact-threshold criterion (Section 21). Files `11-matrix-shadows-*`. |
| **12** | *Arithmetic Quotients of Omnific Chevalley Groups and Lie Rings* (28) | `7af8a30` | All of Part IV (Sections 35–46): the root-kernel ideal and set-image reconstruction for every root system without `A_1` component (Theorems 37.2, 37.4); intrinsic invisibility and the arithmetic quotient of `E_Φ` (Theorem 38.2, Corollary 38.3, Example 38.4); the ring–group equivalence (Theorem 38.5); perfectness, torsion, center, nonsimplicity (Section 39); Steinberg groups and isogeny forms (Section 40); a second proof of the amalgam theorem and the componentwise classification (Section 41); the Lie-ring classification (Section 42); the cardinal transfer (Section 43); explicit `C_2`, `G_2` matrices (Section 44); twelve questions (Section 45). Files `12-chevalley-quotients-*`. |

- **Why one report.** 06 and 07 prove the same main theorem (the purely
  infinite elementary kernel for `n ≥ 3` has no set-sized images), each has a
  large part the other lacks, and 10 studies modules and bases over the same
  rings; its ordinary backbone belongs to a surcomplex report about theta
  series, where its omnific content would be foreign. 11 proves the same main
  theorem a third time and adds structure around it, so it was added to Part II
  rather than made a separate report. 12 generalizes Part II from `E_n` to
  every elementary Chevalley group and answers this report's question
  `ogl:q:roots`; it was added as Part IV, after the questions, so that no
  earlier number changes.
- **Printed once, three proofs kept.** Theorem 9.1 is stated in 06's generality
  (any unital `D ⊆ k`) and 07's intrinsic form (maps defined only on the
  kernel); 11 states it for `D = Z, Z[i]`, and its proof, like 07's, uses `D`
  only through the split retraction. 07's proof rescales a large set field (the
  sibling report's `osq:lem:collision`); 06's divides by a difference of nearby
  monomials (`osq:lem:division`); neither uses the other's ingredients. 11's
  proof rebuilds a set-sized ring from the root maps of a group homomorphism and
  invokes the ring theorem `osq:thm:universal`(iii); it is kept as a marked third
  route that is not independent of the collision identities. 11's finite
  residual (credited at Theorem 16.4), finite-support counterexample (at
  Proposition 12.2) and action and representation corollaries (at
  Corollary 9.5, where its intertwiner statement is added) are not reprinted.
- **Source 12, printed once** (Section 35.4). Its normal-form facts are
  Lemma 2.1 and Proposition 2.4; its scalar theorem (its Theorem 4.3) is the
  sibling report's `osq:thm:universal`(ii),(iii), proved by the scaled-field
  collision (`osq:lem:collision`; its compression is Lemma 8.3's `Φ_δ`); for
  `Φ = A_{n−1}` its main theorem is Theorem 9.1(iii) and its proof is 11's
  third route, not a fourth independent proof. Its general statements extend,
  and credit, `ogl:ker:thm:rootkernel`, `ogl:el:lem:normalgen`,
  `ogl:el:rem:ring`, `ogl:ker:thm:torsionfree`, `ogl:ker:thm:center`,
  `ogl:ker:cor:normalsets`, `ogl:ker:prop:finitesubgroups`,
  `ogl:ker:thm:steinberg`, `ogl:ker:cor:transfer`(ii) and
  `ogl:ker:prop:exactthreshold`. In rank one its amalgam theorem is Theorem 13.2,
  and its leading-term proof is kept as a marked second route; its free
  product, equivariant functional, countable detection and nonexistence of a
  universal quotient are Theorems 14.1, 15.3, Lemma 15.1 and Corollary 15.5
  (07) and are credited, not reprinted (its countable target is, for `D = Z`,
  isomorphic to 07's). Its ring collision criterion is printed (Proposition
  43.2) as `osq:lem:collision`(i) plus a factorization; its finite-support,
  subgroup and standard-part remarks are recalled for all root systems in
  Section 44 with the earlier sources credited.
- **Printed by citation, not reprinted.** `O_n(Oz)` (`odg:cor:orthogonal`); the
  existence of unipotent families for `x² + y² − 3z²` (`odg:cor:unipotent`; 06's
  rational-anisotropy argument and explicit matrix are kept); from the
  Hahn–Tate report's Part II, the lattice-projection lemma
  (`tate:theta:lem:latticeprojection`), the rational-flag minimum criterion
  (`tate:theta:thm:flag`, `tate:theta:cor:domain`), the `2^n` parity bound
  (`tate:theta:thm:minimizers`) and the Pell example (`tate:theta:ex:irrational`)
  (Section 27.1). 10's proofs are kept only for its converse (a bad center for
  an irrational flag), the non-closedness of projected lattices, the Gaussian
  bounds, arbitrary surreal targets and all omnific statements. 11's set-sized
  ring is the sibling report's `R^{11}_κ` (`osq:prop:lex`,
  `osq:rel:lem:embedding`; the superscript names that report's manuscript 11,
  not source 11 here); its ring facts are cited there, and 11's own short proofs
  of the two lemmas it needs are kept (Lemmas 21.1, 21.2).
- **Renamed symbols** (Section 1.4, Table 3): the purely infinite ideal is the
  collection's `Π_k` (was `𝓘_k`, `𝒥_k`, `𝒥`); the constant term is `ct` (07's
  `c_0`); the kernel is `P_n` (06's `P_n(k)`, 07's and 11's `N_n`); 06's congruence
  subgroups `N_a` are `P_n^(a)`, 11's `N^(m)` modulo `(1+ω)^m` are
  `P_n⟨(1+ω)^m⟩`; 11's Steinberg kernel `K_n(A)` is `P_n^St`; 11's fragments
  `A_{κ,D}`, `Π_{κ,k}` are `R_{<κ}`, `Π_{<κ}`; 10's energy `E` is `𝓔`, since `E_n`
  is the elementary group; 10's *primitive* vectors are **unimodular**, because
  the omnific Diophantine report uses *primitive* for "no common nonunit
  divisor" (`odg:thm:realray`); further renames avoid clashes of `G`, `K`, `T`,
  `X`, `Y`, `H`, `F`, `V_j`, `D_i`.
- **Source 12's renamed symbols** (Section 35.2 and Table 3). `Φ` is a root
  system only; 12's exponent compression `T_δ` is Lemma 8.3's `Φ_δ` and is not
  used in Part IV. 12's reconstruction letters `U, h, J, T(a), R_h, τ` are
  `Σ, φ, J_φ, ϑ_φ(a), R_φ, ϑ_φ` as in Theorem 9.2 (`τ` stays the monomial
  `ω^{2δ}` of Lemma 8.5); its rank-one `G_0, B_0, B(A)` are `G_D, C_D, B_D`;
  its detection field `F ∈ {Q, Q(i)}` is `K_D` and its set field `F` is `L`
  (`F` stays the ambient field); its Lie lattice `Λ`, `𝔤 = Λ⊗Q`, `L(A)` are
  `𝔩`, `𝔩_Q`, `𝔩(A)` (`Λ` stays an ordinal or a Euclidean lattice); its basis
  `b_i`, integers `n_{ℓij}`, target `M`, functional `λ` and `sl_2` basis
  `e, f, h` are `𝖻_i`, `z_{lij}`, `𝔥` (fraktur H), `ϖ`, `𝖾, 𝖿, 𝗁`; its
  appendix matrices `N, M, L, K` and `A, …, F`, `A_−`, `B_−`, `H_A`, `H_B` are
  `𝖭_1, …, 𝖭_4`, `𝖦_1, …, 𝖦_6`, `𝖦_1^−`, `𝖦_2^−`, `𝖧_1`, `𝖧_2`; its
  congruence subgroup `N` at `q = 1+ω` is `P_Φ⟨1+ω⟩` (`q` written out, as for
  11); its collision data `u, v, μ` are `w, v, ν`. `P_Φ`, `P_Φ^St` extend
  `P_n`, `P_n^St` (`P_{A_{n−1}} = P_n`). Roots are `α, β, γ` in Part IV, where
  exponents are written `η`.
- **Foundations.** 06 and 07 state Gödel–Bernays with global choice, 10 NBG, 11
  allows Gödel–Bernays with global choice, 12 Gödel–Bernays with a ZFC set
  part (global choice harmless but unnecessary, no inaccessible); no proof uses
  global choice (the Hartogs ordinal replaces a cardinal above the target), and
  11's set-sized fragments give ordinary ZFC statements.

## Results added in the merge

Each is marked `[merge]` and has a complete proof.

- **The rigid-affine-variety question for group schemes** (Remark 4.6): 06's
  theorems answer `odg:q:affine` for closed subgroup schemes of `GL_N` over `Z`
  (and over `Z[i]`), and contain `odg:cor:unipotent` and `odg:cor:orthogonal`.
- **The ring theorem as a consequence** (Remark 9.6): Theorem 9.1 implies the
  universal set-sized quotient theorem `osq:thm:universal` for coefficient
  fields `R`, `C` (unital, nonunital through the unitalization, and modules). It
  is a logical implication, not an independent proof. The remark now also
  records 11's converse (the third proof), so the group theorem and the
  nonunital ring theorem imply each other.
- **The finite side** (Proposition 11.1): for `n ≥ 3`, every homomorphism from
  the kernel of standard part on `SL_n` of the finite surreals (or surcomplex
  numbers) to a set-sized group is trivial, so `SL_n(R)`, resp. `SL_n(C)`, is
  the universal set-sized quotient. Remark 11.2 compares it and Theorem 9.1 with
  the rotation-group theorems of the euclidean-three-space report: parallel,
  neither implies the other.
- **Exact thresholds for the fragments** (Proposition 21.12): for `κ` regular
  uncountable, every nonzero additive multiplicative map from `Π_{<κ}` has image
  of cardinality at least `κ^{<κ}` (the sibling report's field bound
  `osq:prop:card11` with the scaled-field collision `osq:lem:collision`, which
  applies to maps defined on the ideal alone); with 11's exact-threshold
  criterion (Proposition 21.11), every nonidentity element of the kernel
  `P_{n,<κ}`, `n ≥ 3`, has least detecting group of cardinality exactly `κ^{<κ}`
  (also for the Steinberg kernel), and `𝔠` at `κ = ℵ1`. This replaces 11's lower
  bound `κ`, which 11 explicitly declines to sharpen.
- **The sibling report's five set-sized models** (Corollary 21.13): by the same
  argument, in each ring of `osq:thm:thresholds` the least detecting group of
  every nonidentity kernel element, `n ≥ 3`, has the cardinality of the ring.
  Together with Proposition 21.12 this partly answers Question 34.4.
- **Exact thresholds for every root system** (Corollary 43.7, batch 32): source
  12's cardinal transfer (Theorem 43.3, Corollary 43.4), applied with Proposition
  21.12(i) and the proof of Corollary 21.13, gives the same exact values
  (`κ^{<κ}` in `R_{<κ}`, `𝔠` at `ℵ1`, `|A_0|` in the five models) for the
  elementary and Steinberg kernels of every root system without `A_1`
  component, and for perfect current Lie rings `𝔩 ⊗ Π_{<κ}`; this extends the
  partial answer to Question 34.4.
- **Bounded supports** (Corollary 44.1, batch 32): for uncountable `λ`, the
  quotient theorems of Part IV hold for the rings `A^{<λ}_{D,k}` of normal forms
  with fewer than `λ` terms (the sibling report's `osq:thm:support`(i) with
  `D = Z` makes `Π_k^{<λ}` set-invisible, and 12's proofs use nothing else);
  they fail for finite supports. In particular `E_Φ(Z)` is the universal
  set-sized quotient of `E_Φ(O_κ)`, `O_κ` the omnific integers with fewer than
  `κ` terms of the report on first `κ` coefficients.
- **The kernel form of the classification** (Theorem 41.1(ii)): `P_Φ` is
  set-invisible iff `Φ` has no `A_1` component; an `A_1` factor `P_2` is
  detected by 07's countable maps. Immediate from 12's Theorem B and 07's
  Theorem 15.3; recorded because Question 34.3 asks for the kernel.
- **Unipotent lattices** (Remark 42.8): nilpotent Lie lattices are not
  perfect, so their current Lie rings have no universal quotient, the Lie
  counterpart of the characters of `UT_n(Π_k)` (Theorem 6.2); a comparison
  only.

Not results, and not marked: status notes of batch 32 on Questions 34.3
(answered for split elementary groups), 34.4, 34.1 and 34.2, a pointer in 11's
non-claim 11.17, a correction of the Steinberg sentence of Section 20 ("no other
statement … in the collection"), and a pointer in Remark 9.6 to 12's
equivalence.

## What the report claims

Here `(D,k)` is `(Z,R)` or `(Z[i],C)`, `Π_k` the normal forms supported on
strictly positive exponents, `B_k = k ⊕ Π_k`, `A_{D,k} = D ⊕ Π_k`.

- **Part I (06).** For a real algebraic group `G`: `G(B_R) = G(R)` iff `G(R)` has
  no nonidentity unipotent iff `G` has no `G_a` subgroup iff `G^0` is reductive
  with compact real derived group; for a closed subgroup scheme of `GL_{N,Z}`
  these are equivalent to `𝒢(Oz) = 𝒢(Z)`, and otherwise `(Π,+)` embeds in the
  constant-term kernel by a finite exponential (Theorem 4.4). Over `C`, rigidity
  holds iff `G^0` is a torus, also for `Z[i]`-models and `Oz[i]` (Theorem 4.5).
  Bounded real fibers over a torus give rigidity (Theorem 3.3); `SO_3(Oz)` has 24
  elements while `SO_3(Oz[i])` has unipotent families; the constant-term kernel
  of a unipotent group is `exp(𝔲 ⊗ Π_k)` (Proposition 6.1); `UT_n(Π_k)` has
  `[Fil_r, Fil_s] = Fil_{r+s}` (Theorem 6.2).
- **Part II, `n ≥ 3` (06, 07, 11).** `P_n = ker(ct : E_n(A_{D,k}) → E_n(D))` is
  generated by the purely infinite root elements, perfect, nontrivial,
  `E_n = P_n ⋊ E_n(D)`, and every homomorphism from `P_n` to a set-sized group is
  trivial; so `E_n(D)` (`SL_n(Z)`, `SL_n(Z[i])`, or `SL_n(k)` for `D = k`) is the
  universal set-sized quotient (Theorem 9.1). A proper-class congruence tower
  separates elements of `P_n` though no set-sized subfamily does
  (Theorem 10.1); the theorem fails in fixed set-sized Hahn workspaces
  (Proposition 12.1 gives only a conditional lower bound) and for finite
  supports (Proposition 12.2).
- **Part II, the kernel for `n ≥ 3` (11).** The constant-term kernel of
  `GL_n(A_{D,k})` is torsion-free for every `n` (Theorem 19.1); `P_n` is
  centerless (Theorem 19.2), has no nontrivial set-sized normal subgroup, and its
  nonidentity conjugacy classes are proper classes (Corollary 19.3); finite
  subgroups of `E_n` inject under `ct` (Proposition 19.4). The subgroups
  `P_n⟨(1+ω)^m⟩` form a strictly decreasing chain containing `e_12(ω^ω)`
  (Theorem 19.5), and any set of principal congruences has common root elements
  (Proposition 19.6). With Bass–Milnor–Serre, the profinite completion of
  `E_n(Oz)` is `SL_n(Ẑ)`; for `Oz[i]` only `≅ \widehat{SL_n(Z[i])}`
  (Corollary 19.7). `St_n(A_{D,k})` has universal set-sized quotient `St_n(D)`
  and a perfect kernel with no set-sized images, mapped onto `P_n`
  (Theorem 20.2). In the rings `R_{<κ}` of supports of size `< κ` over
  `⊕_{α<κ} Q`, `κ` regular uncountable, the kernel has no nontrivial image of
  cardinality `< κ` and is nontrivial, nonabelian, torsion-free, centerless and
  perfect (Theorem 21.3, Corollary 21.4 for Steinberg groups), non-simple
  (Proposition 21.5), of size `𝔠` at `κ = ℵ1` (Proposition 21.6); action and
  complex-representation thresholds (Proposition 21.7, Corollaries 21.8, 21.9);
  an abstract exact-threshold criterion (Proposition 21.11).
- **Part II, rank two (07).** `E_2 ≅ SL_2(D) *_{C_D} B_D` (Theorem 13.2); `P_2` is
  a free product of copies of `(Π_k,+)` indexed by `P¹(Frac D)` (Theorem 14.1);
  maps to `SL_2(Frac(D)(t))` separate every finite subset (Theorem 15.3), and
  neither `E_2` nor `P_2` has a universal set-sized quotient (Corollary 15.5).
  Detection trichotomy: finite iff `ct(g) ≠ 1`; least detecting cardinal `ℵ0`
  on `P_2`; none on `P_n`, `n ≥ 3` (Theorem 16.5). `E_2(Oz)^ab ≅ Z/12 ⊕ Π`
  (Proposition 17.1, classical), every abelian image of `E_2(Oz[i])` kills `P_2`
  (Proposition 17.2). `I + ω^{2a}[[α,1],[−α²,−α]]`, `α ∉ Frac D`, lies in
  `SL_2 \ E_2` (Theorem 18.2) and is a commutator in `P_3` after one
  stabilization (Theorem 18.4).
- **Part III (10).** For a separated positive pencil `𝓔 = Σ ε_j q_j`: a shortest
  nonzero vector exists iff `L_m = K_m ∩ D^n ≠ 0`; otherwise the lower bounds of
  the energies are exactly `ε_m O_fin,≥0`, there is no surreal infimum
  (Theorem 24.1), and one monomial vector improves every set-sized family
  (Theorem 24.2). Low energies recover the kernel flag (Theorem 25.1). The
  unimodular minimum exists iff `q_r` is definite on the span of the last nonzero
  integral intersection; otherwise the coinitiality is `ℵ0` (Theorem 26.4).
  Closest points exist for every surreal target iff every prefix kernel is
  rational, and then lie among at most `2^n` / `4^n` ordinary candidates
  (Theorems 27.2, 27.5). The Pell comparison (Theorems 28.1, 28.2), the strict
  hierarchy (Corollary 29.1), no Gauss or `δ`-LLL basis for ordinary
  `δ ∈ (1/4,1]`, Gaussian `δ ∈ (1/2,1]` (Theorems 30.3, 30.4), and a closed
  uniformly separated module without a shortest vector (Proposition 31.1).
- **Part IV (12).** Let `Φ` be a finite reduced root system, `E_Φ` the
  elementary subgroup of the split simply connected group, `D ⊆ k` any unital
  subring. If `Φ` has no `A_1` component, the common kernel of the root maps of
  any homomorphism is an ideal (Theorem 37.2; only `2Π_k = Π_k` is used, not
  `2 ∈ A^×`), every homomorphism from `P_Φ = ker(ct : E_Φ(A_{D,k}) → E_Φ(D))` to
  a set-sized group is trivial, and `E_Φ(D)` is the universal set-sized quotient
  (Theorem 38.2, Corollary 38.3), including `C_2`, `G_2`, `F_4`, `E_6`, `E_7`,
  `E_8` (Example 38.4), for Steinberg groups (Theorem 40.1) and for other split
  isogeny forms, whose relative kernels are isomorphic to `P_Φ`
  (Proposition 40.3). For a class ring `I` with `2I = I`, ring invisibility of
  `I` and set-invisibility of the kernel over its Dorroh unitization are
  equivalent (Theorem 38.5). `P_Φ` is perfect (each root element a product of
  at most three commutators), torsion-free, centerless, without nontrivial
  set-sized normal subgroup, and not simple (Section 39). For `D = Z, Z[i]`,
  `E_Φ(A)` has a universal set-sized quotient iff `Φ` has no `A_1` component,
  so `A_1 × A_1` fails (Theorem 41.1). For a Lie lattice `𝔩`, the current Lie
  ring `𝔩 ⊗ A_{D,k}` has a universal set-sized Lie-ring quotient iff `𝔩 ⊗ Q`
  is perfect, and it is then `𝔩 ⊗ D` (Theorems 42.3, 42.6); so
  `sl_2(Oz) → sl_2(Z)` is universal while `E_2(Oz)` has none. For every
  infinite `κ`, ring invisibility below `κ` transfers to groups and Lie rings,
  with exact detecting size `κ` when `|A| = κ` (Theorem 43.3, Corollary 43.4,
  Theorem 43.5).

## What the report does not claim

- All five sources are AI-assisted, unrefereed drafts that call their main
  results proposed contributions; priority is not certified, no named
  conjecture is claimed settled, and nothing is formalized:
  `docs/FORMALIZATION.md` maps none of these labels to Lean (its inventory rows
  for this report are Pending), and the repository has no omnific Lean module.
- The Part II theorems concern `E_n`, not `SL_n`; whether `SL_n(Z)` is the
  universal set-sized quotient of `SL_n(Oz)` for `n ≥ 3` is open
  (Question 34.1). `P_n` is not simple and not trivial; its tautological
  proper-class representation is faithful.
- Source 11's Steinberg kernel is not `K_2`: no `K_2` computation, no universal
  central extension, no excision, and the kernel of `St_n(A) → E_n(A)` is not
  computed; the Steinberg kernel is not claimed centerless or torsion-free. No
  isomorphism `\widehat{E_n(Oz[i])} ≅ SL_n(\widehat{Z[i]})` is asserted, and the
  Bass–Milnor–Serre step is imported. Finite subgroups are not claimed conjugate
  to constant ones. At `ℵ1` nothing excludes actions on countable sets or all
  finite-dimensional complex representations. 11 itself claims no exact
  threshold for its fragments; the exact values of Proposition 21.12 and
  Corollary 21.13 are the merge's, for `n ≥ 3` and these rings only.
- Part I answers `odg:q:affine` only for group schemes, and in the nonrigid case
  constructs families through integral points without describing all omnific
  points. The transfer is between real closed fields only.
- Part III covers separated positive pencils only (`(x − ωy)² + y²` is a
  counterexample to extending contraction, and even has a reduced basis); the
  strongest coinitiality statement fails in fixed Hahn fields; the reduction is
  not an algorithm for arbitrary surreal inputs; no surreal volume theory.
- Source 12 (Part IV) concerns elementary, root-generated groups:
  `E_Φ(Oz) = G_Φ(Oz)` is not asserted, and nothing is said about `SL_n(A)` or
  elementary generation. It computes no `K_2`; its Steinberg kernel is the
  kernel of the constant term, not of `St_Φ → E_Φ`, and is not claimed
  torsion-free or centerless. No normal-subgroup classification, no global
  commutator width (the bound three is per root element), no global
  exponential group–Lie correspondence. The rank-one converse is in the
  simply connected elementary category and for `D = Z, Z[i]` only. Subgroups of
  invisible groups need not be invisible. The transfer uses no regularity, but
  collision data in a Hahn fragment may need it; actions need `2^{|X|} < κ`, not
  `|X| < κ`. No congruence-subgroup claim, Gaussian or other. Finite support
  destroys the theorem; `ct` is not the standard part; the converse of the
  ring–group equivalence uses only the Dorroh unitization. Root systems were
  checked by computer only up to rank 8; the finite checks are not proofs;
  nothing is in Lean; its repository review was targeted and its negative
  search is not proof of absence (and is stale, see below); priority is not
  certified and no named conjecture is claimed solved.
- Appendix B keeps every limitation stated by a source, numbered per source:
  06 (23 items), 07 (20), 10 (21), 11 (24), 12 (28), and 15 for the merge (131
  in all). Section 34 lists seven questions: one answered negatively within the
  report (the rank-two question of 06, asked again by 11, answered by 07), one
  answered by source 12 for split elementary groups (Question 34.3, other root
  systems: exactly the systems without `A_1` component, with twisted, nonsplit
  and full groups still open), one partly answered by the merge (Question 34.4,
  thresholds at set-sized stages: answered in `R_{<κ}` and in the sibling
  report's five models, for `n ≥ 3` and, since batch 32, for every root system
  without `A_1` component; open for other exponent groups and supports), four
  open. Section 45 lists source 12's twelve questions: one partly answered by
  the merge (Question 45.5, as Question 34.4), eleven open (Question 45.1
  contains Question 34.1). `odg:q:affine` is answered here for group schemes
  only. Its curve part is now answered in the Diophantine report
  itself (status notes of batch 31 in Remark 4.6 and after Question 34.7), except
  the real case of `odg:sg:q:real`; higher dimension stays open.
- The finite checks verify finite identities and examples only.

## Corrections and stale statements

Sources 06, 07 and 10 pin commits that precede the written omnific reports (at
`220784a` and `fb5c4b5` the omnific directories held only their placed base
manuscripts, with bare labels); source 11 pins `9693b28`, at which this report
was already written; source 12 pins `7af8a30`, at which it held sources 06,
07, 10 and 11. Appendix A.3 lists the corrections.

- 06's "geometric collision construction in Section 3" and 07's "scaled-field
  collision" of the quotient article are now `osq:lem:division` and
  `osq:lem:collision`.
- 06 described the euclidean-three-space theorem from the catalogue as a
  statement about `SO(3,No)`; that report also proves it for `SO(n,No)`,
  `n ≥ 3`, and `SU(n,No[i])`, `n ≥ 2` (`e3:cut:thm:allranks`). 06's count of 51
  catalogued reports was accurate then; the catalogue now lists 56.
- 06 and 07 leave rank two and `SL_n` open; rank two is settled inside this
  report by 07, and `SL_2(Oz) ≠ E_2(Oz)`.
- 10's search for "shortest vector" found nothing, and 10 cites the Lean module
  `LatticeEnergyCertificate.lean` but not the report it formalizes: the
  Hahn–Tate report's Part II, present at 10's pin, already had the projection
  lemma, the flag criterion, the parity bound and the same Pell example; they are
  credited (Section 27.1).
- 11 says its searches did not locate its elementary-group statements in the
  repository. At its pin this report already contained its main theorem (the
  label `ogl:el:thm:invisible` occurs 16 times there), the finite residual, the
  finite-support counterexample and the answer to its rank-two question; the
  report was missing from the catalogue 11 inspected (`docs/README.md` at the pin
  describes 51 reports and has no row for it). The claim is accurate for the
  Steinberg statements.
- 11 declines to identify the root-generated subgroup with the kernel;
  Propositions 7.2 and 7.3 (06) prove it, and 11's proofs do not depend on it.
- 11 calls its fragments "related to" the sibling report's constructions; they
  are the same ring (`osq:prop:lex`, present at the pin), and the embedding in
  `Oz` was added to that report later (`osq:rel:lem:embedding`). The sibling
  report's exact ring thresholds, which 11 says "motivate" its criterion,
  satisfy its hypothesis (`osq:prop:card11`, present at the pin).
- 12 says an indexed search of the repository for "Chevalley" found no match.
  That is false as a description of the tree: at its pin this article contains
  the word twice (lines 3822 and 3829 there), in Question 34.3
  (`ogl:q:roots`) and its status note, which asked for exactly 12's extension;
  12 answers that question. Its restricted novelty statement is unaffected:
  the tree held no theorem for root systems other than `A_{n−1}` and no current
  Lie ring. 12 read this guide and 11's proof audit, not the article; its
  account of the antecedents (type `A`, rank two, kernels, Steinberg groups,
  cardinal arguments) is accurate, though it does not mention Proposition
  21.12 or Corollary 21.13.
- Section 20's sentence "No other statement about Steinberg groups or `K_2`
  appears in the collection" now points to Part IV's Theorem 40.1.
- **Citations checked for this report.** Mirzaii–Torres (arXiv:2401.06330v3):
  Corollary 3.3 (credited to Cohn) gives `E_2(R)^ab ≅ R/M` for rings universal
  for `GE_2`, Example 3.4(i) gives `R/M = R/12Z` when `R^× = {±1}`, and
  Example 1.1(vi) records Cohn's theorem that discretely ordered rings are
  universal for `GE_2`, as 07 says. Cohn's non-elementary pattern
  `[[1+xy, x²], [−y², 1−xy]]` is on p. 26 of his 1966 paper (end of Section 7).
  06's Milne references were checked: *Algebraic Groups* Proposition 14.32 and
  Corollary 17.25, *Introduction to Shimura Varieties* Theorem 1.16 and
  Example 1.17(c). 06's reference to Sections 22–23 of Milne's *Reductive
  Groups* was not checked, nor were 11's Bass–Milnor–Serre and Voronetsky
  citations, nor 12's Geck, Hazrat–Vavilov–Zhang, Cohn and Serre citations.

## Relations to neighbouring reports

- [`omnific-diophantine-geometry`](../omnific-diophantine-geometry/): Part I
  answers its question `odg:q:affine` for group schemes and contains
  `odg:cor:unipotent`, `odg:cor:orthogonal`; Theorem 3.3 and `odg:thm:bounded`
  use the same transfer and neither contains the other. Its batch-31 curve
  theorems (`odg:cr:thm:affine`, `odg:sg:thm:main`, `odg:sg:thm:omnific`,
  `odg:sg:cor:gaussian`) answer the curve part of `odg:q:affine`, except over
  `Oz` for real curves with normalization `A^1_R` whose integer points all
  lack a real preimage (`odg:sg:q:real`); the two "open for curves" sentences
  here are re-scoped accordingly (Remark 4.6 and the note after Question
  34.7), and higher dimension stays open.
- [`set-sized-quotients-of-omnific-integers`](../set-sized-quotients-of-omnific-integers/):
  Theorem 9.1 strengthens `osq:thm:universal`, `osq:cor:faithful`,
  `osq:prop:matrices` to abstract group maps and uses its collision lemmas;
  11's third proof derives it back from `osq:thm:universal`(iii) (Remark 9.6);
  Proposition 11.1 is the group form of `osq:thm:finite`; 11's fragments are
  that report's `R^{11}_κ`, and Proposition 21.12 and Corollary 21.13 transfer
  its exact thresholds (`osq:prop:card11`, `osq:thm:thresholds`) from rings to
  groups. Part IV (12) uses `osq:thm:universal`(iii) as the ring input for every
  root system without `A_1` component and for current Lie rings, proves that
  ring and group invisibility are equivalent for Dorroh unitizations
  (Theorem 38.5), and with `osq:prop:card11` gives Corollary 43.7.
- [`first-kappa-coefficients`](../../surcomplex/first-kappa-coefficients/)
  (batch 32): its omnific integers `O_κ` with fewer than `κ` terms are the
  sibling report's `A^{<κ}_{Z,R}`, so for uncountable `κ` Corollary 44.1 makes
  `E_Φ(Z)` the universal set-sized quotient of `E_Φ(O_κ)` for every `Φ` without
  `A_1` component. Cited by name only (Sections 33, 44.1); nothing is imported.
- [`euclidean-three-space`](../euclidean-three-space/), Part III: the rotation
  groups' standard-part theorems (`e3:cut:thm:smallquotient`,
  `e3:cut:thm:allranks`) are parallel; different rings, kernels and mechanisms;
  neither implies the other (Remark 11.2).
- [`hahn-tate-uniformization`](../../surcomplex/hahn-tate-uniformization/),
  Part II: the ordinary backbone of Part III's closest-point theory and the Pell
  example (Section 27.1).
- [`surcomplex-field-automorphisms`](../../surcomplex/surcomplex-field-automorphisms/):
  07's exponent rescaling is its dilation `saut:eq:dilation`.
- [`omnific-preserving-automorphisms`](../omnific-preserving-automorphisms/),
  written from the same batch as 06, 07 and 10: algebraic group actions *on*
  `Oz`, not points of groups *over* `Oz`.

## Build

From a copy in a scratch directory:

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build has no errors, warnings, overfull or underfull boxes, undefined
references or duplicate destinations. Commit only `article.pdf`, not the
auxiliary files.

## Reproducing the finite checks

The first three scripts and source 12's need Python 3 and SymPy (the recorded
runs used Python 3.13.5 and SymPy 1.14.0); source 11's needs only the Python
standard library (3.10 or later). The reruns for this report used Python 3.14.4
and SymPy 1.14.0 and passed. Run them **on a copy**, because 07's script always
writes `checks-results.json`, and 11's and 12's always write
`verification_results.json`, next to themselves (so 11's and 12's overwrite
each other's output in one directory; run 12's in a directory of its own):

```
cp -r code data /path/to/scratch/ && cd /path/to/scratch
python -m pip install -r data/07-matrix-dichotomy-requirements.txt
python code/06-algebraic-groups-verification.py            # prints; add --output FILE to write a report
python code/07-matrix-dichotomy-checks.py                  # prints; writes code/checks-results.json
python code/10-shortest-vectors-verify.py                  # prints only
python code/11-matrix-shadows-verify.py                    # prints; writes code/verification_results.json
mkdir run12 && cp code/12-chevalley-quotients-verify.py run12/
python run12/12-chevalley-quotients-verify.py              # prints; writes run12/verification_results.json
```

Do not run 12's with `python -O`: it refuses to run without assertions. Its
shipped Makefile (`code/12-chevalley-quotients-Makefile`) targets the delivery
names `article.tex` and `verify.py` and does not work from the shipped layout.

Expected: `TOTAL: 1108 exact checks passed.` (06); `PASS: 23 checks, including
120 exact target-word examples.` (07; the written JSON equals
`data/07-matrix-dichotomy-checks-results.json` except for the recorded Python
version); `All finite checks passed.` with six `PASS` lines (10); a JSON report
with `"status": "PASS"` and `"total_checks": 2111` in twelve families, equal in
content to `data/11-matrix-shadows-verification_results.json` (11); a JSON
report with `"status": "passed"` and `"total_checks": 2188` in twelve families
(1,868 of them one root-reconstruction witness per root of `A_ℓ, B_ℓ, C_ℓ`,
`2 ≤ ℓ ≤ 8`, `D_ℓ`, `4 ≤ ℓ ≤ 8`, `G_2`, `F_4`, `E_6`, `E_7`, `E_8`; 240 rank-one
leading-term, nonvanishing and determinant checks on 80 polynomial words; 80
matrix identities, divided powers, root counts and `sl_2` brackets), equal to
`data/12-chevalley-quotients-verification_results.json` except for the recorded
Python version (12; Appendix C). The checks do not verify Hahn
summability, support gaps, class-size or cardinal arguments, algebraic-group
structure, reduced-word arguments, the coverage lemma in every rank, or any
minimization or coinitiality theorem; those are proved in the text.
