# Omnific Groups and Lattices

**Algebraic groups, elementary quotients, and missing lattice minima over the omnific integers**
Merged research report, 23 September 2026, from four manuscripts written
independently on the same day: 06 (the base), 07 and 10 of batch 26 (placed in
`f4c9504`), and 11, item 05 of batch 29 (placed in `66d7e55`), numbered here
after its file prefix `11-`.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 70 pages
README.md     this guide
10-shortest-vectors-provenance.md        source 10's provenance and evidence record, as delivered
11-matrix-shadows-SOURCES_AND_SCOPE.md   source 11's repository snapshot, source roles and exclusions, as delivered
11-matrix-shadows-PROOF_AUDIT.md         source 11's own proof review, as delivered
11-matrix-shadows-BUILD_REPORT.md        source 11's build and rendering report, as delivered
code/
  06-algebraic-groups-verification.py   source 06 checks (1,108; stdout, file only with --output)
  07-matrix-dichotomy-checks.py         source 07 checks (23; always writes checks-results.json, see below)
  10-shortest-vectors-verify.py         source 10 checks (6 groups; stdout)
  11-matrix-shadows-verify.py           source 11 checks (2,111; always writes verification_results.json, see below)
data/
  06-algebraic-groups-verification-results.txt   recorded run of the source 06 checks
  07-matrix-dichotomy-checks-results.json        recorded run of the source 07 checks
  07-matrix-dichotomy-checks-output.txt          its console output
  07-matrix-dichotomy-requirements.txt           sympy==1.14.0
  10-shortest-vectors-verification-output.txt    recorded run of the source 10 checks
  10-shortest-vectors-requirements.txt           sympy==1.14.0
  11-matrix-shadows-verification_results.json    recorded run of the source 11 checks
```

Every label in `article.tex` carries the prefix `ogl:`, with the sub-prefixes
`ogl:alg:` (Part I, algebraic groups), `ogl:el:` (Part II, elementary groups),
`ogl:ker:` (Part II, source 11's kernel structure, Steinberg groups and
fragments, Sections 19–21, and its root-kernel lemmas in Section 9) and
`ogl:lat:` (Part III, lattices); the report has 202 labels (168 before
source 11 was added; none was renamed or removed). The text placed in
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
`data/11-matrix-shadows-verification_results.json`).

## Four sources, one report

| | Manuscript (pages) | Pin | Contributes |
|---|---|---|---|
| **06** | *Omnific Points of Algebraic Groups* (22) | `220784a` | **The base.** Part I (Sections 3–6): the real and Gaussian dichotomies (Theorems 4.4, 4.5), bounded fibers over a torus (Theorem 3.3), orthogonal examples, unipotent kernels and the unitriangular filtration (Theorem 6.2). In Part II: normality of the root-generated subgroup for any constant ring (Propositions 7.2, 7.3), the proof of Theorem 9.1 by division by nearby monomials, the congruence tower (Theorem 10.1), and the boundaries (Section 12). Files `06-algebraic-groups-*`. |
| **07** | *A Matrix-Size Dichotomy over the Omnific Integers* (25) | `fb5c4b5` | Base of Part II: the relative-kernel lemma, the proof of Theorem 9.1 by rescaling a set field (for maps defined only on the kernel), the collision criterion (Proposition 9.7); rank two: amalgam, free-product kernel, countable detection (Theorems 13.2, 14.1, 15.3); the trichotomy (Theorem 16.5); abelian characters (Section 17); cusp residues, non-elementary unipotents, stabilization (Section 18). Files `07-matrix-dichotomy-*`. |
| **10** | *Shortest Vectors and Missing Infima over the Omnific Integers* (26) | `220784a` | All of Part III (Sections 22–32). Files `10-shortest-vectors-*`. |
| **11** | *Arithmetic Shadows of Omnific Matrix Groups* (24) | `9693b28` | Theorem 9.1 again (its Theorem A), with a third proof by root-kernel reconstruction (Theorem 9.2, Corollary 9.3, Lemma 9.4); torsion-freeness, centerlessness, set-sized normal subgroups and conjugacy classes, finite subgroups, a congruence chain and common congruence elements, the profinite completion (Section 19); Steinberg groups (Section 20); set-sized fragments, cardinal and action thresholds and the exact-threshold criterion (Section 21). Files `11-matrix-shadows-*`. |

- **Why one report.** 06 and 07 prove the same main theorem (the purely
  infinite elementary kernel for `n ≥ 3` has no set-sized images), each has a
  large part the other lacks, and 10 studies modules and bases over the same
  rings; its ordinary backbone belongs to a surcomplex report about theta
  series, where its omnific content would be foreign. 11 proves the same main
  theorem a third time and adds structure around it, so it was added to Part II
  rather than made a separate report.
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
- **Foundations.** 06 and 07 state Gödel–Bernays with global choice, 10 NBG, 11
  allows Gödel–Bernays with global choice; no proof uses global choice (the
  Hartogs ordinal replaces a cardinal above the target), and 11's set-sized
  fragments give ordinary ZFC statements.

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

## What the report does not claim

- All four sources are AI-assisted, unrefereed drafts that call their main
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
- Appendix B keeps every limitation stated by a source, numbered per source:
  06 (23 items), 07 (20), 10 (21), 11 (24), and 10 for the merge (98 in all).
  Section 34 lists seven questions: one answered negatively within the report
  (the rank-two question of 06, asked again by 11, answered by 07), one partly
  answered by the merge (Question 34.4, thresholds at set-sized stages: answered
  for `n ≥ 3` in `R_{<κ}` and in the sibling report's five models, open for other
  exponent groups and supports), five open; `odg:q:affine` is answered for group
  schemes only.
- The finite checks verify finite identities and examples only.

## Corrections and stale statements

Sources 06, 07 and 10 pin commits that precede the written omnific reports (at
`220784a` and `fb5c4b5` the omnific directories held only their placed base
manuscripts, with bare labels); source 11 pins `9693b28`, at which this report
was already written. Appendix A.3 lists the corrections.

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
  citations.

## Relations to neighbouring reports

- [`omnific-diophantine-geometry`](../omnific-diophantine-geometry/): Part I
  answers its question `odg:q:affine` for group schemes and contains
  `odg:cor:unipotent`, `odg:cor:orthogonal`; Theorem 3.3 and `odg:thm:bounded`
  use the same transfer and neither contains the other.
- [`set-sized-quotients-of-omnific-integers`](../set-sized-quotients-of-omnific-integers/):
  Theorem 9.1 strengthens `osq:thm:universal`, `osq:cor:faithful`,
  `osq:prop:matrices` to abstract group maps and uses its collision lemmas;
  11's third proof derives it back from `osq:thm:universal`(iii) (Remark 9.6);
  Proposition 11.1 is the group form of `osq:thm:finite`; 11's fragments are
  that report's `R^{11}_κ`, and Proposition 21.12 and Corollary 21.13 transfer
  its exact thresholds (`osq:prop:card11`, `osq:thm:thresholds`) from rings to
  groups.
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

The first three scripts need Python 3 and SymPy (the recorded runs used Python
3.13.5 and SymPy 1.14.0); source 11's needs only the Python standard library
(3.10 or later). The reruns for this report used Python 3.14.4 and SymPy 1.14.0
and passed. Run them **on a copy**, because 07's script always writes
`checks-results.json` and 11's always overwrites `verification_results.json`
next to themselves:

```
cp -r code data /path/to/scratch/ && cd /path/to/scratch
python -m pip install -r data/07-matrix-dichotomy-requirements.txt
python code/06-algebraic-groups-verification.py            # prints; add --output FILE to write a report
python code/07-matrix-dichotomy-checks.py                  # prints; writes code/checks-results.json
python code/10-shortest-vectors-verify.py                  # prints only
python code/11-matrix-shadows-verify.py                    # prints; writes code/verification_results.json
```

Expected: `TOTAL: 1108 exact checks passed.` (06); `PASS: 23 checks, including
120 exact target-word examples.` (07; the written JSON equals
`data/07-matrix-dichotomy-checks-results.json` except for the recorded Python
version); `All finite checks passed.` with six `PASS` lines (10); a JSON report
with `"status": "PASS"` and `"total_checks": 2111` in twelve families, equal in
content to `data/11-matrix-shadows-verification_results.json` (11). The checks do not verify Hahn
summability, support gaps, class-size or cardinal arguments, algebraic-group
structure, reduced-word arguments, or any minimization or coinitiality
theorem; those are proved in the text.
