# Automorphisms of the Surcomplex Numbers

**Real forms, Hahn symmetries, valuation, and rigidity**
Single-source research report, 22 September 2026. It is built from one
manuscript, manuscript 07 of batch 20 (archive `surcomplex_automorphisms`),
pinned to repository commit `dcf8666`, and placed in commit `5fe7f8d`.
Author line: research article prepared with ChatGPT.

This directory holds one manuscript. It is not a merge: there was no second
source, and nothing was selected out of a larger body of work. Every result,
proof, example, question and limitation of the manuscript is printed. The
delivery had no code and no data.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 36 pages (title, two contents pages, 33 numbered pages)
README.md     this guide
```

Every label in `article.tex` carries the prefix `saut:`. The source's 79 labels
are kept, unchanged after the prefix, and seven were added
(`saut:sec:conventions`, `saut:sec:position`, `saut:eq:Lchain`,
`saut:sec:nonclaims`, `saut:app:conjugacy`, `saut:app:provenance`,
`saut:app:pinned`). The delivered PDF is not shipped; `article.pdf` is a build
of this text.

## Which automorphisms

Let `K = No(i)`, `c` its conjugation, `O` the finite ring and `v` the natural
valuation (`t^g = ω^{-g}`, `v = min supp`). The report never says
"automorphism" without the structure preserved (Section 1.4):

- **plain field automorphism** — any ring automorphism: `Aut(K)`, `Aut(No)`;
- **valued automorphism** — `α(O) = O` (the group `G_v`), so
  `v(αz) = τ_α(v z)` for an ordered automorphism `τ_α` of the value group; it
  need not fix any value. Every field automorphism of `No` is valued; one of
  `K` need not be;
- **value-fixing** — valued with `τ_α = id`;
- **1-automorphism** — `v(αz − z) > v(z)` for all `z ≠ 0` (the group `U`),
  i.e. every leading term fixed; the leading-term notion of Kaplan–Krapp–Serra;
- **exponential automorphism** — an automorphism of `No` commuting with the
  surreal `exp` (`Aut_exp(No)`); there is no surcomplex exponential here;
- **L-automorphism** — an automorphism of `K` commuting with the logarithmic
  modulus `L(z) = log|z|` (`Aut_L(K)`, the rigidity report's notation).

`U ⊆ value-fixing ⊆ G_v ⊆ Aut(K)` and
`{id, c} = Aut(K/No) ⊆ Aut_L(K) ⊆ G_No ⊆ G_v`, where `G_No` is the setwise
stabilizer of `No`.

## What the report claims

Section and theorem numbers are those of the build.

- **Real axis (Theorem 2.2).** For real closed `F`, `Aut(F(i)/F) = {id, c}`,
  and the setwise stabilizer of `F` is the centralizer of `c` and is
  `≅ Aut(F) × C₂`. Exact norm or modulus preservation forces `id` or `c`
  (Theorem 2.3); preserving the unit circle setwise is equivalent to
  preserving `F` (Theorem 2.4).
- **Explicit Hahn automorphisms (Theorem 4.1).** `M_{ρ,τ,χ}` (coefficient
  automorphism `ρ`, ordered exponent automorphism `τ`, arbitrary character
  `χ: No → C^×`) is a strong field automorphism with a stated composition law;
  it preserves `No` exactly when `ρ ∈ {id, c}` and `χ > 0`. Special cases: the
  dilations `S_a` (`ω ↦ ω^a`), witnessing `Aut(K/No) ⊊ G_No`; positive
  characters `D_λ`; and the **phase twists** `P_θ` (Theorem 4.2), a faithful
  action of `(R,+)` by strongly `C`-linear, value-fixing automorphisms that
  move `No` (`P_{π/2}(t) = it`), witnessing `G_No ⊊ Aut(K)` with no choice.
  The conjugates `P_{2θ}c` have pairwise distinct fixed fields, all `≅ No`.
- **Leading-term kernel (Theorems 5.1, 5.2).** Taylor motions `Φ_d` are
  1-automorphisms preserving `No` that move a real transcendental constant
  `b ↦ b + t^δ`; fixed-shift flows `T_s` (e.g. `t ↦ t/(1−st)`) are strongly
  `C`-linear 1-automorphisms.
- **Four layers (Theorem 6.1).** Every valued automorphism factors uniquely as
  `u · D_χ · M_{ρ,τ}`: `G_v ≅ (U ⋊ Hom(Γ,C^×)) ⋊ (Aut(C) × Aut_ord(Γ))`; for
  `No`, `(U_R ⋊ Hom(Γ,R_{>0})) ⋊ Aut_ord(Γ)` (6.5), and a further
  kernel–skeleton layer for `Aut_ord(Γ)` (Section 6.2).
- **Topology (Propositions 7.1, 7.2; Section 7.2).** Valued automorphisms are
  fine homeomorphisms; set-sized subsets are closed and discrete; an explicit
  fine-continuous real-axis-preserving automorphism fails to preserve a Hahn
  sum.
- **Derivatives (Theorems 8.1, 8.2; Corollary 8.3).** A field automorphism
  with a fine derivative somewhere has the same derivative everywhere, and a
  nonzero one forces the identity; `S_a` (`a > 1`) has derivative 0
  everywhere; only the identity is bidifferentiable.
- **Pure field (Theorems 9.1, 9.2; Propositions 9.3, 9.4).** Class
  back-and-forth (global choice): `Aut(K/C)` is transitive on `K \ C`; for any
  set of parameters some automorphism fixing them moves `No`, and some moves
  `O`, so neither is definable in the pure field; `G_No ⊊ G_v ⊊ Aut(K)`;
  fixed fields `Q`, `C`, `Q^rc`, `Q^rc`, `Q̄`.
- **Real forms (Theorems 10.1, 10.2; Proposition B.1).** Nontrivial finite
  subgroups of `Aut(K)` have order 2, each involution fixes a real form; a real
  form with a countable cofinal subset exists, so not every involution is
  conjugate to `c`; an involution is conjugate to `c` iff its fixed field has
  the set-cut interpolation property.
- **Exponential structure (Section 11).** Simplicity plus order forces the
  identity; commuting with the omega-map and fixing values forces the
  identity. Lemma 11.1, Theorem 11.2 (faithful value-group action), the
  equation `ker(Aut_exp(No) → Aut_ord(Γ)) = {id}` (11.2), Proposition 11.3
  (no exponential automorphism induces `g ↦ qg`, `q ∈ Q_{>0} \ {1}`) and
  Theorem 11.4 (`Aut_L(K) ≅ Aut_exp(No) × C₂`, value-action kernel `{id, c}`)
  are the rigidity report's results, reprinted with attribution.
- **Observation of the edit (1.2).** `Aut_L(K) = {α ∈ G_No : α|No ∈
  Aut_exp(No)} ⊊ G_No`, strict by `S_q` (`q` rational, `≠ 1`). Whether
  `{id, c} ⊊ Aut_L(K)`, i.e. whether `Aut_exp(No)` is nontrivial, is not
  decided.
- **Questions (Section 14):** the image of exponential automorphisms in the
  value group (the rigidity report's Question 13.1); omega-map compatibility
  (KKS Questions 5.6, 5.7); effective descriptions inside `U`; real-form and
  continuity classifications. All open.

## What the report does not claim

Section 15.3 keeps the source's non-claims in place and collects them in a
ledger of 33 items: 28 from the source and 5 added when the report joined the
collection. In brief:

- Not refereed; no theorem here is Lean-verified and no Lean code
  accompanies it; no independent build of the repository. No complete
  classification of `Aut(K)`; priority not certified; no exhaustive
  nonduplication claim.
- The exponential results of Section 11 and the answer to KKS Question 5.4
  are prior work of the rigidity report, not results of this one.
  Faithfulness is not triviality.
- The four-layer decomposition covers `G_v` only, not `Aut(K)`. Continuity is
  an inclusion, not a classification. The non-strong witness is not claimed
  value- or leading-term-fixing, and non-density is only for the
  pointwise-equality topology.
- `S_2` is not a locally convergent power series; zero derivative does not
  imply local constancy; the Berarducci–Mantova derivation, formal
  differentiation and the fine derivative are three notions.
- Back-and-forth results and `Φ_d` are not algorithms; the transcendence-basis
  slogan is not a classification; real forms and the conjugacy criterion are
  not classified or decided effectively.
- The finite symbolic checks mentioned in the delivered README were not
  delivered; nothing here rests on them, and they would prove no infinite
  statement.
- Added: the Q5.4 reading rests on the rigidity report's check of the pinned
  KKS v3; the source's readings of KKS Examples 4.3–4.4 and Questions 5.6–5.7
  were not rechecked; nontriviality of `Aut_exp(No)` and exponentiality of
  `S_a|No` for non-rational `a` are not decided; relations in Section 1.5
  transfer no theorem between topologies or derivative notions.

## Relation to the neighbouring reports

**[exponential-automorphism-rigidity](../../surreal/exponential-automorphism-rigidity/)**
studies *exponential* automorphisms of an ordered exponential field and, in its
Section 9, `L`-automorphisms of `F(i)`; this report studies *plain* field
automorphisms of `No(i)`. Section 11 here reprints: Lemma 11.1 = its
`lem:amplify` (3.1); Theorem 11.2 = its faithfulness `thm:cofinal`/`cor:faithful`
(4.1/4.2) via `lem:bridge`, `lem:bounded`, `prop:finite-log`; (11.2) and the
sentence after it = its `eq:main-no`, `thm:no`, `cor:question54` (5.1/5.2, the
answer to KKS Question 5.4, arXiv v3); Proposition 11.3 = its `thm:dilation`
(8.4), second proof, any positive infinite `X` for `ω`; Theorem 11.4 = its
`thm:L-classification` with `lem:range`, `thm:complex-kernel`, `cor:surcomplex`
(9.1, 9.2, 9.4, 9.5) for `F = No`. Theorem 2.2 is the field-level, exponential-free
counterpart of its classification. `S_q|No` is its canonical lift `T̂_q`
(`prop:hahn-lift`), and `ℓ(g) = [g]_0` its layer coefficient. The report's
image question is its Question 13.1.

**[foundations](../../foundations-and-computation/foundations/)** —
`found:prop:complex` (the pair field, algebraic closedness); Proposition 7.2 is
`found:thm:discrete` (Lean-proved for the surcomplex carrier, with
lower-universe smallness, per `FORMALIZATION.md`); the derivative is
`found:eq:derivative`. The collection's earlier zero-derivative witnesses
(`found:rem:fourtypes`, **[analysis](../analysis/)** `b:L`) are locally
constant; `S_2` is injective, hence constant on no nontrivial open set.

**Character twists.** `D_χ = M_{id,id,χ}` generalizes the diagonal twists of
[spectral-theory](../spectral-theory/) (`spec:lem:finiteindex`),
[hidden-negative-hermitian-directions](../hidden-negative-hermitian-directions/)
(`hnd:lem:supportdegree`) and
[transcendence-over-bounded-support](../../surreal/transcendence-over-bounded-support/)
(`bst:lem:characters`) from set-sized groups to `Γ = No`.

**[trigonometry](../trigonometry/)** — the Cayley map of Theorem 2.4 is a
reparametrization of `trigonometry:thm:cayley`. Rotations there and in
[euclidean-three-space](../../surreal/euclidean-three-space/) (same batch) are
`No`-linear isometries, not field automorphisms; by Theorem 2.3 the only field
automorphisms preserving every modulus are `id` and `c`.

**Lean.** `Surreal/Surcomplex/Basic.lean` (`conj` as a ring automorphism) and
`Surreal/HahnSeries/ComplexNumbers.lean` (`coefficientEquiv`, the case
`M_{ρ,id,1}` in a workspace) are interfaces; `Surreal/Algebra/SigmaDerivation.lean`
proves valued-field forms of the rigidity report's displacement results, while
its ordered `lem:amplify` is pending. No statement of this report is covered.

"Rigidity" here (Theorems 2.3, 11.2; Section 11.1) is not `f:thm-rigidity` of
analysis nor the scalar rigidity of gamma-functions; "phase" is a coefficient
multiplier, not an argument or the trigonometry/differential-equations phase;
"real form" is a real closed `F` with `K = F(i)`, not the real-coefficient
versions in entire-functions or analytic-geometry.

Two later reports use conjugation on `No[i]`.
[surreal-fields-across-universes](../../foundations-and-computation/surreal-fields-across-universes/)
continues, but does not settle, the real-form question of Section 14: under
global choice it transports an inner model's conjugation to real forms of
`No[i]` that have no set-sized cofinal subset and are not conjugate to `c`
(by the easy direction of `saut:prop:conjugacycriterion`), separates several
such forms by an external gap invariant, and lets them agree with `c` on `C`.
[birthday-cutoffs-and-hereditary-sets](../../foundations-and-computation/birthday-cutoffs-and-hereditary-sets/)
enriches bounded surcomplex fields by conjugation and a coordinate birthday;
its bounded `Aut = {id, c}` statements are credited to `saut:thm:axis` and the
simplicity rigidity of `saut:sec:exponential`, and only its two-lift
classification of elementary embeddings and, under GBC, its elementary
self-embeddings of the full structure are new there. Neither addresses
`Aut_L`.

## Stale statements corrected

The source compared itself with the repository at `dcf8666` (Section 13, kept
as provenance); Appendix C.2 records the check. Its descriptions of
`Complexify.lean`, `FineDerivative.lean`, `NORMAL_FORM_BRIDGE.md` and the
rigidity report with its audit correction are accurate, and none of those
files changed between the pin and the placement. The source did not relate its
results to `found:thm:discrete` and its Lean proof, the zero-derivative
witnesses, `spec:lem:finiteindex`, `trigonometry:thm:cayley`, or the Lean
modules above; the hidden-negative-directions and bounded-support reports and
`SigmaDerivation.lean` postdate the pin. Section 1.5 supplies these relations.
The rigidity report's README sentence that no other report proves its theorems
about `Aut(No)` predates this report.

Six symbols were renamed so that each has one meaning: `E_{ρ,τ} → M_{ρ,τ}`,
`E_d → Φ_d` (so `E` is only an exponential), the derivation `D → 𝒟`, the
Puiseux field `P → 𝒫`, the automorphism `τ → ψ` in Section 7.2, and cut sides
`(L,R) → (𝓛,𝓡)`; `Aut(K,L)` is written `Aut_L(K)`. `Γ = (No,+,<)` is a proper
class here, departing from `NOTATION.md`'s set-sized `Γ`. No mathematical
statement was changed.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Standard packages (`newtx`, `amsmath`, `mathtools`, `geometry`, `microtype`,
`booktabs`, `longtable`, `enumitem`, `ragged2e`, `tocloft`, `fancyhdr`,
`hyperref`, `cleveref`); no shell escape, no external `.bib`. The recorded
build has no errors, no undefined or multiply-defined references, no duplicate
PDF destinations, no LaTeX warnings and no overfull or underfull boxes. A
clean compile proves nothing about the proofs. There is nothing to rerun: the
delivery contained no code or data.
