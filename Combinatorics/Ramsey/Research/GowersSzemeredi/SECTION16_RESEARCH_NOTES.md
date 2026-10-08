# Theorem 16.2: quantitative obstructions and a regime-splitting reduction

Research notes, 2026-10-07. They concern the exact catalogue statement
`theorem_16_2` (`Theorem162At k` for every `k`) in
`Combinatorics/Ramsey/Lean/GowersSzemeredi/Section16.lean`, and its open
dependants: Corollary 16.11, Theorem 18.1, Theorem 18.2, Corollary 18.7 and
(via 18.2) Theorem 1.3.

Everything below is about **what the printed route can certify** with the
catalogue's control functions. None of it refutes Theorem 16.2. Results marked
*proved* have complete proofs here; results marked *heuristic* do not.

Notation follows `Section16.lean`:

- `c(θ,γ,k) = (γθ)^A_k` with `A_k = 2^(2^(k+8))`, and `q = 1/c`.
- `s(θ,γ,k) = (2/(θγ))^(2^(2^(k+6)))`.
- `MultiplyLinear γ r` demands, for **every** inner loss θ′ ∈ (0,1] and every
  proper box `P`, a cover off θ′|P| points by at most `q(θ′/r,γ,k)^r`
  multilinear graphs, on proper cells of width at least
  `P.width^(c(θ′/r,γ,k)^r)`.
- Theorem 16.2 asks for this with `r = R := γ⁻²·s(θ,γ,k)`.

Both controls are **polynomial in 1/θ′** of degree `A_k·R`, and `R` is a
polynomial in `1/θ` (of enormous degree).

## A. Inner-loss uniformity (Lemma 16.10): why the small-scale escape fails

The anchor-sampling lift needs `r ≈ 6q/σ` slices with `σ = θ′/4`. Their
sequential refinements give controls `q(·)^(r·s)` and `c(·)^(r·s)`, which
are **exponential** in a power of `1/θ′`. This is what makes the printed
`lemma_16_10` false; that encoding is now `lemma_16_10_printed_unit_encoding`.

It is tempting to hope that small boxes rescue the lift, because they are
trivial.

*Proved (elementary).* Let `W = P.width` and `e(θ′) = c(θ′/R,γ,k)^R = (γθ′/R)^(A R)`.

- If `W^e ≤ 2`, split every axis into pieces of length 2 or 3, using length 1
  only on axes of length 1. The cells are proper, have width at least
  `min(W,2) ≥ W^e`, and hold at most `3^k` points each.
- A relation whose fibres have size at most `M` is then covered exactly, with
  no loss, by at most `M·3^k` constant graphs per cell.

The nontrivial regime is therefore `W^e > 2`, that is
`log₂W > (R/(γθ′))^(A R)`. Since `W ≤ N`, this regime is nonempty exactly
for θ′ ≥ (R/γ)·(log₂N)^(−1/(A R)), a lower bound that tends to 0 as N grows.
Down to that bound, controls exponential in a power of `1/θ′` exceed the
polynomial targets once N is large.

So the sampling lift cannot be repaired by special-casing small boxes. The
lift itself must have controls polynomial in `1/θ′`.

## B. A second, independent break: Lemma 16.1 is exponential in the graph count

Lemma 16.1 (Corollary 5.11) refines a box so that q multilinear forms are
simultaneously small. Its cell-width exponent is `K^(−2^(k+1)·q)`, with
`K = (k+1)²·2^(k+4)`, so it is **exponential in q**.

In Lemma 16.6, and hence in Lemma 16.9, the method applies it with
`q = q_δ ≤ q(σ/2t, δ, k)^t`, where `t = δ⁻²·s(θ₁/8, δ, k)` is a polynomial in
`1/θ`. Thus `q_δ` is certified only up to `exp(poly(1/θ))`, and the certified
cell-width exponent of Lemma 16.9 (`section16Lemma9Width`) is
`exp(−exp(poly(1/θ)))`, which is doubly exponential.

For each fixed inner loss θ′, Theorem 16.2's target exponent in dimension
k+1 is `c(θ′/R,γ,k+1)^R = exp(−poly(1/θ))`. A log-scale evaluation of the
formal definitions at k = 1 (target dimension 2), γ = 1/2 and θ′ = 1 gives
the table below; θ′ = 1/2 is indistinguishable at this scale. The certified
value assumes the worst case `q_δ = q(σ/2t,δ,k)^t`, which is all the
statement of Lemma 16.6 provides.

| θ      | log₂log₂log₂(1/E₁₆.₉), certified | log₂log₂log₂(1/target) |
|--------|----------------------------------|------------------------|
| 1/2    | ≥ 1.6·10⁵⁹                       | 257.6                  |
| 10⁻³   | ≥ 5.3·10⁵⁹                       | 259.6                  |
| 10⁻³⁰  | ≥ 4.2·10⁶⁰                       | 262.7                  |

So even a perfect replacement for Lemma 16.10 could not close the printed
induction with these control functions. For every θ, and not only as
θ → 0, the certified widths are a whole exponential level too small for
every fixed θ′. Only as θ′ → 0 does the target eventually fall below any
fixed exponent; the nontrivial-regime analysis of A shows that does not
help.

Heuristically, the same propagation would turn Theorem 18.1's exponent
into `exp(−exp(poly(1/α)))`. The density-increment iteration of §18 would
then need a triple-exponential threshold rather than the printed
`2^(2^(δ^(−C)))`.

Caveats:

- The *actual* `q_δ` may be much smaller than its certified bound. In the
  base dimension the input is Lemma 16.3, whose construction uses only
  polynomially many graphs.
- So the break is in the strength of the **induction hypothesis's count
  bound**, not necessarily in the mathematics. A repair would strengthen the
  hypothesis to polynomial graph counts, or prove a simultaneous multilinear
  recurrence whose exponent is polynomial in q, as Dirichlet's theorem gives
  for linear forms. Either is a research problem.
- **Update (2026-10-08, J.3).** The second repair is supported by the
  literature on simultaneous small fractional parts:
  - for K polynomials of fixed degree, exponent c/K² (Schmidt) and c/K
    (Maynard), and explicitly 1/(10.5·K·d(d−1)) (Lau);
  - with K = O(2^k·q), the width exponent becomes 1/poly(q). With
    q = exp(poly(1/θ)) that is exp(−poly(1/θ)), the same order as
    Theorem 16.2's own c(θ'/r, γ, k)^r.
  So Break B would be removed by a multilinear Lemma 16.1 built on those
  bounds. Break A (Lemma 16.10's inner-loss uniformity) is independent and
  unaffected. The bounds have not been formalized.

## C. The unit-parameter selected lift is θ-dependent (heuristic)

`Section16SelectedLiftAt` asks, from a structured pair at density θ, for a
piece of mass `N^(k+1)/s(θ,γ,k+1)` with **unit** `(γ,1)` controls. Those
controls depend on γ and θ′ only, not on θ.

Consider the slab `φ(z) = n₁(last z)` on `Z_N^k × B`, where `B` is a balanced
proper generalized progression of rank `d ≈ log(1/θ)`, all side lengths about
`N^(1/d)`, and `n₁` is its first coordinate.

- **It has the product property.** It is a Freiman homomorphism and
  `|B+B| ≤ N`, so it has the product property at γ = 1; this is the
  weighted-collision mechanism of `Proofs16SlabProductProperty` with the
  pair-sum set bounded by `|B+B|`.
- **Local linearity needs exponent at most about 1/d.** Along a progression
  of length `N^E`, `n₁` is affine only across windows of length about
  `N^(1/d)`. So for E > 1/d the number of affine pieces grows like
  `N^(E − 1/d)`.
- **Selecting a dense piece does not help.** Every piece of relative density
  `1/s` (a constant) still has rank d: lowering the rank costs density about
  `N^(−1/d)`.

So for θ small enough that `1/d < c(θ′,γ,k+1)`, no admissible selected piece
has unit controls. If this is right, the existential selected-lift
obligation of `Proofs16SelectedLiftInduction` is false, just as Report 299
refuted the universal one. A formal proof would need quantitative
equidistribution for balanced generalized progressions.

## D. Literature check

Gowers and Milićević,
[*An inverse theorem for Freiman multi-homomorphisms*](https://arxiv.org/abs/2002.11667)
(2020), prove the finite-field version of the core structure statement:
multi-homomorphisms agree with multiaffine maps on a dense set. Their density
is only `1/exp^(O_k(1))(O_{k,p}(δ⁻¹))`, an iterated exponential.

Theorem 16.2 needs a structured piece of **polynomial** mass `N^k/s(θ,γ,k)`
and controls of the form `exp(−poly(1/θ))`. I found no published polynomial-
bound analogue, and no published erratum for §16 of Gowers (2001). As
encoded, Theorem 16.2's quantitative content appears to be beyond current
published methods, although the statement may well be true.

This concerns polynomial bounds. H.5 records Milićević's 2026 quasipolynomial
structure theorem for Freiman bihomomorphisms in general finite abelian
groups. Through simultaneous Bohr unions, quasipolynomial bounds appear to
fit the exact budget.

## E. A positive reduction (proved; formalized in `Proofs16RegimeSplitting`)

The Lean version, `multiplyLinear_of_powerLossCover`, is kernel-checked. Its
axioms are only propext, Classical.choice and Quot.sound. It differs from the
statement below in two ways. Condition (3) becomes `b·C ≤ δ·log 2`, which is
linear in C, because the proof then needs only `exp y ≥ y`. The
covers are also required only on boxes of width at least a threshold `T`,
with the added condition `T ≤ 2^(1/b)`; this matches the thresholds of the
existing `LargeBoxMultilinearCover` profiles. Here `b = c(1/R,γ,k)^R = 1/B`.

**Proposition (regime splitting).** Let `Γ ⊆ Z_N^k × Z_N` have all fibres of
size at most `M`. Let `R ≥ 1`, `0 < γ ≤ 1`, `A = A_k` and `B = (R/γ)^(A R)`.
Suppose there are `E, Q, C, δ > 0` such that every proper box `P` admits a
cover with:

- an exceptional set of size at most `C·P.width^(−δ)·|P|`;
- at most `Q` multilinear graphs per cell;
- proper cells of width at least `P.width^E`.

The loss is θ′-free: it does not depend on any requested loss. If

1. `Q ≤ B` and `M·3^k ≤ B`,
2. `E ≥ 1/B`, and
3. `δ·B ≥ log₂ max(C,1) + 1`,

then `MultiplyLinear γ R Γ`.

*Proof.* Fix θ′ ∈ (0,1] and a proper box `P` of width `W`.

The two targets are `q(θ′/R)^R = (R/(γθ′))^(A R) ≥ B` and
`e = c(θ′/R)^R = (γθ′/R)^(A R) ≤ 1/B`. So counts at most `B` and exponents
at least `1/B` are always admissible.

- **Case `W^e ≤ 2`.** Use the coarse cover: cells with sides 2 or 3, and
  sides 1 only on axes of length 1. Splitting axes into consecutive pieces
  keeps the common difference and properness, every cell has width at least
  `min(W,2) ≥ W^e`, and at most `M·3^k` constant graphs per cell cover with
  no loss.
- **Case `W^e > 2`.** Then `log₂W > 1/e ≥ B/θ′`, using `A R ≥ 1` and
  `1/θ′ ≥ 1`. Put `C′ = max(C,1)`. The exceptional fraction satisfies
  `C·W^(−δ) < C′·2^(−δB/θ′) ≤ C′·2^(−(log₂C′ + 1)/θ′) ≤ 2^(−1/θ′) ≤ θ′`.
  The middle step uses `1/θ′ ≥ 1` and `log₂C′ ≥ 0`. The last step is
  `2^(−x) ≤ 1/x` for `x ≥ 1`.

In both cases the count, width and loss meet the targets. ∎

Theorem 16.2 therefore follows from a **θ′-free** structure theorem: after
removing a θ-fraction of base points, a cover on every box whose losses decay
as a power of the box width, with `θ`-dependent constants inside the budgets
(1)–(3).

The anchor lift does not have this shape, because of its small classes and
missed anchors. The budgets are also where obstruction B bites: (2) asks
`log(1/E) ≲ R·log R`, a polynomial in `1/θ`.

## G. Why common-anchor lifts cannot have loss-independent controls (method obstruction)

This obstruction is to the anchor method. It is not a counterexample to
Theorem 16.2 or to a structure theorem with loss-independent losses.

Assume the strengthened, loss-independent lower-dimensional inputs:

- `φ''` is covered jointly in `(h,x)`;
- `φ′(h,·)` is affine on each whole cell fibre.

Then every fibre has one class, and the only role of the anchors is to supply
two points of each fibre `D_h ∩ J` common to all `h` in the cell. Each anchor
`x_a` contributes a cross-section cover of `h ↦ φ₁(h,x_a)` on its own
partition. With r anchors these refinements are sequential, so the cell-width
exponent is `c^(r·s)`.

**Random domains defeat this.** Let `D` be a random subset of density α (the
truth can be trivial here, e.g. `φ₁ = h·x`). A fixed set of r anchors in a
cell misses the fibre `D_h ∩ J` for a `(1−α)^r` fraction of `h`. That is a
constant loss, not one decaying in the width W. Driving it below `C·W^(−δ)`
forces `r ≳ δ·log W/α`. Then `c^(r·s) = W^(−δ′)` for some δ′ > 0, and the cell
widths `W^(W^(−δ′))` tend to 1.

So no choice of anchor count gives covers whose losses are independent of θ′
and power-small. Stacking anchors into one relation (the union of r
cross-sections has the product property with `γ/√r`, which is proved by
pigeonholing the branch vector along each line) removes the sequential
compounding. It does not help, because the anchors must lie in each cell's
own progression `J_u`, and global anchors almost never do.

**Consequence.** A lift whose losses do not depend on θ′ needs a
*family-uniform* structure theorem: one partition serving the cross-sections
`φ₁(·,x)` for all x in a cell. Alternatively it needs direct additive
structure in h of the slope functions `h ↦ ψ_h(d)`, which might come from
8-arrangement respect. Neither is available, and both are research problems.

**No fixed r helps either.** `MultiplyLinear γ r` needs controls polynomial in
θ′ for every r. Controls that are exponential in a power of 1/θ′ (the proved
`LargeBoxMultilinearCover` profiles) therefore never imply `MultiplyLinear`.
At the nontrivial-regime boundary `1/θ′ ≈ (γ/r)(log W)^(1/(A r))`, they
exceed the target `≈ log W` by a factor `exp((log W)^ε)`. Any all-dimension
induction built on the proved lift must therefore replace `MultiplyLinear` by
a predicate with general control functions (route 2 below).

## H. The dimension-two route and the stackability gap in dimension three

Written 2026-10-07 against main at `14e18f4db`. The peer's unconditional
dimension-two route ends in `section16_cubic_relation_decomposition`
(`Proofs16CubicRelationDecomposition.lean`). It covers `Γ` restricted to a set
`J` of mass `(1−θ)N²` by at most `γ⁻²/m₂(θ,γ)` pieces, where
`m₂ = section16CubicPieceMass` is a polynomial in θγ. Each piece satisfies
`MultiplyLinearWith` with explicit "cubic" controls. This part asks what
the same route needs from dimension k in order to reach dimension k+1 ≥ 3.

### H.1 What is dimension-specific

The lift is already proved for every k; see
`Section16AllBoxLineCoversWith.cubic_multiplyLinearWith`. It consumes two
inputs:

- the line covers, from Lemmas 16.6 and 16.9 in their `…With` forms;
- a **slice provider** (`Section16SliceProvider`).

For every sample `t₁,…,t_r` of final coordinates, the provider covers the
stacked slices, that is the union of the r graphs `x ↦ φ(x,t_i)` on
`Z_N^k`. The proved lift takes a provider with these controls:

- graph count `3·r·q`, and
- exponent `cubicBaseExponent(r·q, σ) = 2^(−27)·σ³/(r·q)⁴`.

Both are **polynomial in r**. This matters because the lift samples
`r = section16UniformSampleCount ≈ 6·Q₉/σ` anchors, a polynomial in 1/σ.

In dimension two the slices are one-dimensional, and two facts supply the
provider:

1. **Loss-free slices.** After an outer θ-removal, every slice is covered
   *exactly* by at most q Freiman 8-homomorphisms on α-dense sets
   (`Section16FinalFreimanFamilies`). Here `α = 2^(−2000)·(γθ)^10000` and
   `q ≤ γ⁻²/α`, so all parameters are polynomial in γθ.
2. **Simultaneous linearization.** Corollary 7.11 linearizes any number n
   of Freiman homomorphisms on one common partition into APs with a common
   step. Its exponent is `2^(−14)·α²/n`, and the inner loss enters only
   through a threshold. Stacking r slices just replaces n = q by n = r·q.

These are the only places where the route uses `Point N 1`
(`section16_freiman_family_cubic_cover` and
`section16_cubic_slice_provider_of_freiman_families`).

### H.2 Sequential unions are exponential in the number of pieces

*Proved; formalized as `MultiplyLinearWith.fin_union` and
`MultiplyLinearWith.finsetUnion` in `Proofs16WithUnion`, from the two-relation
`MultiplyLinearWith.union`.* Suppose `Γ₁,…,Γ_m` each satisfy
`MultiplyLinearWith Q E`. Then their union satisfies `MultiplyLinearWith`
with count `m·Q(ρ/m)` and exponent `E(ρ/m)^m`.

*Proof.* Fix a box P. Cover P for `Γ₁` at loss ρ/m. Then cover every cell
for `Γ₂` at loss ρ/m, and so on through `Γ_m`.

- Each stage loses at most a ρ/m fraction of every cell, hence of P.
- Each stage raises the cell widths to the power `E(ρ/m)`.
- The graphs from the m stages are pooled on every final cell. ∎

The interface `MultiplyLinearWith` says nothing about how the partitions of
different pieces relate, so this is the only bound it certifies.
Heuristically it is also the truth for unrelated partitions. Two partitions
into APs with large coprime steps have a common refinement only into much
shorter APs.

### H.3 Why the dimension-two theorem cannot serve as the provider for dimension three

Take `B ⊆ Z_N³` and stack r two-dimensional slices, with `r ≳ 1/σ` as in
H.1. There are two ways to cover the stack using what is proved in
dimension two. Both give certified controls that are exponential in a
power of 1/σ.

- **Piecewise.** Decompose each slice with
  `section16_cubic_relation_decomposition`. That gives `m = r·γ⁻²/m₂`
  pieces in total. Every piece exponent is at most 1/4, because
  `section16CubicLiftExponent` carries a factor 1/4 and its other factors
  are at most 1. By H.2 the stacked exponent is at most `4^(−m)`, that is
  `exp(−Ω(1/σ))`. The provider needs an exponent polynomial in σ.
- **All at once.** The union of r graphs with the product property at γ has
  it at `γ/√r` (pigeonholing the branch vector along each line; see G).
  The dimension-two count, `section16CubicLiftGraphBound`, is about
  `9·(6/σ)⁴·(2R/(γσ))^(4·A₂·R)·q²`. Here `R = γ⁻²·s(θ/8,γ,1)` comes from
  `section16Lemma9QBound` and `section16Lemma9R`. Replacing γ by `γ/√r`
  multiplies R by about `r^(1+2^127)`. The count is then at least
  `exp(c·r^(1+2^127))` for some c > 0 depending on θ and γ, which is
  exponential in a power of 1/σ.

So the dimension-two controls are polynomial in the inner loss only for
fixed (θ,γ). In θ and γ they are exponential in a polynomial, through R, the
Bohr radius `ζ = 2^(−s(θ,γ,1))`, and the Lemma 16.1 exponent
`K^(−4q)`. Dimension one is polynomial in **every** parameter, and that is
what made it stackable. Neither computation is an impossibility proof. They
show only that the dimension-two theorem, as stated and proved, does not
supply the dimension-three slice provider.

### H.3a Break B in dimension three is the same gap; truncation does not help

Lemma 16.6 feeds the lower-dimensional graph count `q` of the spectrum
relation into Lemma 16.1, whose exponent is `K^(−2^(k+1)·q)`. That exponent
is `exp(−poly(1/θ))` only when q is polynomial in `1/θ` and `1/γ`. So break
B and the stacking gap of H.3 come from one defect.

- **Dimension two.** The spectrum count comes from dimension one:
  `section16CubicSpectrumCount`, which the peer bounds by `s(θ,γ,1)` in
  `Proofs16CubicSpectrumBudget`. It is polynomial.
- **Dimension three.** The count would come from dimension two. Through
  `section16CubicLiftGraphBound` it is exponential in a polynomial, so
  Lemma 16.9's width exponent becomes doubly exponential again.

Gowers's definition (`sz-thm-gowers-proof.tex`, line 3342) asks for every
inner loss, exactly as the encoding does. But its only consumer outside
Section 16, the proof of Corollary 16.11 (line 3534), uses one loss,
θ′ = α/8. A version of Theorem 16.2 truncated at `θ′ ≥ ρ₀(θ,γ,k)` looks
inductive, because the lift requests lower-dimensional losses proportional
to its own. It would remove break A. It would not remove break B, and the
catalogue's Corollary 16.11 exponent `(α/8)·c(r⁻¹α/8, α/2, k)^r` is
`exp(−poly(1/α))`, so truncation alone does not reach the open catalogue
items. Every route beyond dimension two needs lower-dimensional counts that
are polynomial in all parameters.

**Polynomial controls are necessary but not sufficient.** One could try to
make dimension two polynomial in every parameter:

- feed the cubic dimension-one controls into the cross-sections of
  Lemma 16.4(i) and the line covers of Lemma 16.9, instead of the printed
  `(γ,R)` controls behind `section16Lemma9QBound`;
- replace Lemma 16.1 for linear forms (the case k = 1) by Dirichlet's
  theorem, whose exponent is about `1/q` rather than `K^(−4q)`.

Even then, stacking would fail. The proof of Theorem 16.2 ends with a
greedy decomposition into about `γ⁻²/θ₂` pieces united by Lemma 16.8, which
is a sequential union (H.2). Applied to a stack of r slices at `γ/√r`, the
number of pieces is polynomial in r, so the exponent is exponential in it.
A stackable invariant must therefore support **simultaneous** unions, not
merely polynomial counts.

### H.4 A stackable invariant: Bohr-structured multilinearity (proposal)

The induction needs a class of k-dimensional structures that (a) is closed
under finite unions at a cost polynomial in the number of members, and (b)
implies `MultiplyLinearWith` with a count independent of ρ and an exponent
polynomial in ρ. Dimension one shows the right shape. A Freiman
homomorphism on a dense set is, by Bogolyubov and Freiman, a homomorphism
of a Bohr set. Corollary 7.11's exponent `α²/n` is the reciprocal of the rank
`n·α⁻²` of a common Bohr set.

**Definition (proposal).** `Γ` is *Bohr-multilinear on J with data
(D, ζ, q)* if `Γ` restricted to J is covered by q maps. Each map
must agree, on every translate of a product Bohr set `∏_j B(Λ_j, ζ)` with
`|Λ_j| ≤ D`, with a function multilinear in the Bohr coordinates.

- **(i) Stackable.** *Proved (trivial).* `B(Λ,ζ) ∩ B(Λ′,ζ) = B(Λ ∪ Λ′,ζ)`.
  So a union of r structures with data `(D,ζ,q)` has data `(rD, ζ, rq)`:
  ranks add, and nothing is raised to a power.
- **(ii) Readout.** *Heuristic, by the proof of Corollary 7.11.* Boxes have
  one common difference for all axes (`Box.commonDiff`). Simultaneous
  Dirichlet approximation of the kD frequencies along that difference
  partitions most of a box of width W into proper sub-boxes of width about
  `ζ·W^(1/(kD))`. Every map is multilinear on each of them. The inner loss ρ
  enters only through a threshold `W ≥ (1/(ρζ))^(O(kD))`, and the
  regime splitting of E handles the boxes below it.
- **(iii) Anchors become an outer loss.** *Heuristic.* The random-domain obstruction of
  G concerned losses that must decay with W. Under this invariant the
  anchors only have to fix each map on each Bohr translate, which is
  loss-free structure. A fixed fraction of missed fibres can be charged to
  the outer θ by taking `r ≈ log(1/θ)/α` anchors, independent of ρ.

With (i)–(iii), an induction that preserves Bohr-multilinearity would supply
the slice provider in every dimension. The exact Theorem 16.2 would then
reduce to a budget comparison: `D` and `log(1/ζ)` must be bounded by
polynomials in `1/(θγ)` of degree below that of `s(θ,γ,k)`.

**The open step.** The step that is genuinely open is preservation: lifting
from dimension k to k+1 must again produce Bohr-multilinear maps. That is an
inverse theorem for Freiman multi-homomorphisms in Bohr form.

- Dimension one: Bogolyubov–Freiman gives it with polynomial rank.
- Higher dimensions: the structure theorem of Gowers and Milićević (D) has
  this form over finite fields, with iterated-exponential bounds.
  - Those bounds would be enough for the qualitative route 2.
  - They are far outside the polynomial budget of the exact statement.
  - I have not found a `Z_N` version with polynomial rank. It would be a
    bilinear (more generally multilinear) polynomial Bogolyubov theorem.

### H.5 Literature for the open step, and the budget it allows

**What is now available.** Milićević,
[*A bilinear Bogolyubov argument in abelian groups*](https://arxiv.org/abs/2109.03093)
(v3 December 2024), extends bilinear Bogolyubov from `F_p^n` to arbitrary
finite abelian groups with codimension `log^O(1)(1/δ)`. His
[*General inverse theory for the U⁴ norm*](https://arxiv.org/abs/2601.01682)
(January 2026), Theorem 1.4, proves the structure theorem H.4 needs in
dimension two. Let `φ: A → H` be a Freiman bihomomorphism on
`A ⊆ G₁×G₂` with `|A| = c|G₁||G₂|`. Then there are:

- Bohr sets `B₁, B₂` of codimension `(2 log c⁻¹)^O(1)` and radius
  `exp(−(2 log c⁻¹)^O(1))`;
- a set E of rank `(2 log c⁻¹)^O(1)`;
- shifts s, t and an E-bihomomorphism Φ on `B₁×B₂` that agrees with
  `φ(x+s, y+t)` on at least `exp(−(2 log c⁻¹)^O(1))·|G₁||G₂|` points.

The groups are arbitrary, so `Z_N` is included. For the U⁴ application the
paper assumes `(|G|, 6) = 1`, which holds for primes N > 3.

**Why quasipolynomial bounds fit the exact budget.** Simultaneous unions
(H.4 (i)) change what the budget constrains. Theorem 16.2's targets are
`q(θ′/R)^R` and `c(θ′/R)^R` with `R = γ⁻²·s(θ,γ,k)`. For fixed θ′ these are
`exp(poly(1/θγ))` and `exp(−poly(1/θγ))`. In the Bohr route:

- the count is the number of maps;
- the exponent is about `1/(k·rank)`;
- the inner loss enters only through a threshold handled by regime
  splitting (E).

So the total rank and count may be as large as `exp(poly(1/θγ))`. Covering
by `1/mass = exp(polylog)` pieces of polylog rank each gives total rank
`exp(polylog)`, well inside that budget. By contrast, the sequential route
H.2 needs piece masses polynomial in θγ, because R appears in the exponent.

**What it would unlock, and what remains (heuristic assessment).**

1. *Dimension three.* If the two-dimensional slices of a structured pair
   in `Z_N³` are Freiman bihomomorphisms on dense sets, then Theorem 1.4
   makes them Bohr-structured. The stacked-slice provider of H.1 would then
   come from H.4 (i)–(ii), and the proved general-k lift would give
   `Theorem162At 3`.
   - Lemma 16.4 supplies arrangement-respecting restrictions. Whether they
     are bihomomorphisms on dense sets, with density polynomial in θγ, has
     to be checked.
   - E-bihomomorphisms rather than bihomomorphisms also need care. On a
     product of short progressions inside the Bohr sets, the rank-r error
     set E should contribute only bracket terms that do not wrap. That would
     make Φ bilinear in the progression coordinates, hence multilinear in
     the `Z_N` coordinates, since N is prime.
2. *Every dimension.* Each step from k to k+1 needs the same theorem for
   Freiman (k+1)-homomorphisms over `Z_N`, with bounds at most
   `exp(poly)`. Gowers–Milićević prove the multilinear version only over
   `F_p^n`, with iterated-exponential bounds (D). Theorem 1.4 is the case
   k+1 = 2. I know of no version for k+1 ≥ 3 over cyclic groups.
   Formalizing Theorem 1.4 itself (a paper of about 100 pages) would be a
   campaign of its own.

**Decision (2026-10-07).** Keep the printed statements of 16.2, 16.11,
18.1, 18.2 and 18.7 exact; do not restate them. The precedent for
restating, Lemma 16.10, rested on a formal refutation of the printed
encoding. Theorem 16.2 has no refutation, and the evidence above is that it
holds but needs mathematics newer than Gowers (2001). Restating it would
replace the source's quantitative theorems by weaker ones. Theorem 1.3 is
being closed as stated by the openai-math port.

## I. Why the proved structure cannot give Theorem 18.2 at length six (proved)

Written 2026-10-08, after `theorem_16_2_at_two` (`27d8419b8`). Its modulus
threshold has been made explicit (`theorem_16_2_at_two_bounded`), and so has
that of the degree-four inverse theorem (`quartic_function_inverse_explicit`).
The remaining step would compare the resulting six-term threshold with
`szemerediThreshold delta 6`. That comparison fails, for a reason that has
nothing to do with constants.

- The density iteration's threshold is
  `densityIterationClosedThreshold T c rho n = exp((1 + log T + |log c|) * (2/rho)^n)`,
  with `n = ⌈8/beta⌉` steps (`intervalDiscrepancyClosedThreshold`), where
  `beta` is the discrepancy parameter.
- At degree four, `beta = jointStructuralInverseParameter 2 alpha` contains
  `section16JointFrequencyDensity alpha 2 = (alpha/8) / section16JointPowerGraphBudget …`.
  The graph budget is `section16UniformLiftGraphBudget`, about
  `multipleQ(…)^(r*s)`. This is the number of multilinear graphs in the
  dimension-two structure, and it is `exp(poly(1/alpha))`.
- So `n = exp(poly(1/delta))`, `(2/rho)^n` is doubly exponential, and the
  threshold is `exp(exp(exp(poly(1/delta))))`.
- Theorem 18.2 allows `2^(2^(delta^(-M)))` with `M = 2^(2^15)`. Since
  `exp(poly(1/delta))` eventually exceeds `M * log(1/delta)`, no choice of
  constants rescues the comparison for small `delta`.

The five-term case succeeded only because the cubic discrepancy parameter
is polynomial in `alpha` (`fejerCubicDiscrepancyParameter_inv_le_power`).
Length six fails for the same reason as Theorem 18.1 at degree three (status
file, "degree by degree"). The source's polynomial discrepancy rests on the
unsupported estimate of Corollary 16.11. A structure theorem whose graph
count is polynomial in `1/theta` and `1/gamma` (H.3, H.5) would repair both.

## J. What dimension three needs, input by input (plan)

Written 2026-10-08, with `theorem_16_2_at_two` proved. The general-k cubic
lift (`Section16AllBoxLineCoversWith.cubic_multiplyLinearWith`, k = 2 for
`B ⊆ Z_N³`) consumes two inputs. In dimension three, both inherit
non-polynomial counts from the proved dimension-two theorem.

1. **Line covers (Lemmas 16.6 and 16.9, `…With` forms).** They take the
   spectrum relation's cover. In dimension three that relation is
   two-dimensional, and its graph count `q` comes from Theorem 16.2 in
   dimension two, which is `exp(poly)`. Lemma 16.1's width exponent
   `K^(−2^(k+1)·q)` is then doubly exponential: break B, now one dimension
   up (H.3a).
2. **Slice provider.** Stacked two-dimensional slices need controls
   polynomial in the number of slices. That is the stacking gap (H.3).

**Inputs that would close both:**

- (S) A Bohr-structured, loss-free description of two-dimensional
  product-property functions after an outer removal: finitely many maps,
  each multilinear in Bohr coordinates on translates of a product Bohr
  set, with total rank and count at most `exp(poly(1/(θγ)))` (H.5 budget).
  - Milićević's Theorem 1.4 supplies this for Freiman bihomomorphisms on
    dense sets, with quasipolynomial bounds.
  - The bridge needed is that the dimension-three structured pair's
    two-dimensional slices, and the spectrum relation, are covered by
    bihomomorphisms on dense pieces. Section 13 already produces such
    data for frequency functions (`SeparatelyFreimanEight`,
    `MostlyRespectsEight`), and Gowers's weak version is Theorem 13.12.
- (R) A Bohr readout: an E-bihomomorphism on `B₁×B₂` is multilinear on
  every product of short progressions inside the Bohr sets, with width
  exponent about `1/rank`.
- (D) A replacement for Lemma 16.1 when the forms come from (S): their
  simultaneous smallness holds on a common Bohr set whose rank is the sum
  of the ranks. That gives a width exponent polynomial in the rank instead
  of `K^(−q)`.

Given (S), (R) and (D), the existing lift and regime splitting (E) would
give `Theorem162At 3` within the budget, plausibly. Every higher dimension
repeats this with the (k+1)-linear analogue of (S), which is unknown over
`Z_N`.

**Formalization order, if pursued.** First state (S) as a `Prop` over
`ZMod N`, with Milićević's bounds as explicit functions. Then prove (R)
and (D), which are elementary Bohr-set arguments. Then build the
dimension-three slice and spectrum providers conditionally on (S), and run
the budget comparison. The result would be `Theorem162At 3` and
`Corollary1611At 3`, conditional on one published theorem. Neither Theorem
18.1 nor 18.2 would follow; they need polynomial discrepancy (Part I).

### J.1 Status: dimension three is formalized from (S) (2026-10-08)

The plan above is carried out in Lean, in a slightly different shape.
(R) and (D) are not proved separately. Instead (S) is stated directly in
the form the lift consumes: a stackable class whose n-fold unions satisfy
the dimension-one slice provider's controls (`CubicStackableClass`).
Covers by such classes are `StackableStructureAt d Q q`.

- `stackableStructureAt_one` checks the definition in dimension one.
- `theorem_16_2_at_three_of_stackable` and
  `corollary_16_11_at_three_of_stackable` prove `Theorem162At 3` and
  `Corollary1611At 3` from `StackableStructureAt 2 Q q`, with
  `Q, q ≤ (2/(γθ))^(2^64)`.
- The piece parameter is `s = U^9`, with `U = s(θ,γ,2)`. The budget is
  `s ≤ θ₂(θ₁(θ/2,γ,2))·s(θ,γ,3)`, via `U^18 ≤ s(θ,γ,3)`.

The polynomial bound matters. The lift's width exponent contains
`576^(−24n)`, where n is the spectrum count, about `Q·q`. It is absorbed
by `2^(−240U²)` only if `n ≤ U²`. A quasi-polynomial n, as in Milićević's
Theorem 1.4, is not absorbed. Two things therefore remain open:

- a polynomially bounded (S) for two-dimensional product relations;
- the bridge from bihomomorphisms on dense pieces to
  `CubicStackableClass` members.

### J.2 Input (S) stated; the readout (R) is not elementary (2026-10-08)

`Proofs16MilicevicStructure` states Milićević's Theorem 1.4
(arXiv:2601.01682), read from the paper, as `MilicevicBihomStructure D`
over `ZMod N`. Every bound is replaced by (2 + 2 log c⁻¹)^D. Since the base
is at least 2, the printed theorem, with its unspecified O(1), implies
`∃ D, MilicevicBihomStructure D`. That existence is not asserted.
`MilicevicBihomStructure.mono` records that only existence matters.

**The plan above treated (R) as elementary. It is not.**
- Theorem 1.4 outputs an **E-bihomomorphism** Φ on B₁ × B₂ with E of rank
  r = quasi-poly. In each variable, Φ respects additive quadruples only up
  to errors in E.
- Along a progression a + jd inside B₁, the second differences of Φ lie in
  E, not at 0. So Φ(a + jd) = Φ(a) + jΔ + Σᵢ nᵢ(j)·aᵢ, where a₁..a_r generate
  E and the integers nᵢ(j) are not controlled.
- Few linear functions cannot cover such a sequence.
- `CubicStackableClass` (Part J) needs covers by genuinely multilinear
  graphs on subboxes. So an E-bihomomorphism is not a stackable-class member
  as it stands.
- For cyclic groups Milićević's own description of the obstructions is
  *generalized* (bracket) trilinear polynomials (his Theorem C.3), not
  multilinear ones.

**What (R) needs.** A local linearization of E-bihomomorphisms. The
generators aᵢ of E carry Bohr-type structure: they arise as almost-periods.
Restricting to sub-Bohr sets on which the nᵢ(j) are forced to be affine in
j may give genuinely bilinear pieces of width N^(1/quasi-poly). That is a
statement about the joint geometry of E and B₁, B₂. It is not in the paper
as a black box. It is the next research step on this route; it is not a
formalization step.

**Is the detour worth it?** It feeds only Theorem 16.2 in dimension three
(Part J). By Part K it does not touch 18.2 or 18.7. Those need a trilinear
input that is polynomially or quasi-polynomially bounded, and none exists.

### J.3 Where the exponential in q comes from, and a lead for (D) (2026-10-08)

Part J's `PolyBoundedControl` hypotheses exist only because of the factor
576^(−24n) (`partJ_recurrence_lower`). It is the dimension-two instance of
Lemma 16.1's width exponent m^(K^(−2^(k+1)·q)).

**Origin.** Lemma 16.1 applies Corollary 5.11, which makes the q
(k+1)-linear forms ν_i(x, y) = μ_i(x)·y simultaneously small on subboxes.
It does so by refining one form at a time. Each refinement multiplies the
width exponent by K^(−2^(k+1)), so q forms cost K^(−2^(k+1)·q).

**Corollary 7.11 is not a substitute.** Its exponent is 2^(−14)·α²/q,
polynomial in q. But it is a one-dimensional statement about order-8
homomorphisms on a progression; it does not make multilinear forms small on
boxes.

**The lead (checked 2026-10-08).** Along a progression x₀ + t·d,
smallness of μ_i(x)·d is a question of simultaneous small fractional parts
of polynomials in d of degree k+1. That problem has exponents polynomial in
the number of polynomials:
- Schmidt (*Small fractional parts of polynomials*, CBMS 32, 1977):
  exponent c_d/K² for K polynomials of degree d.
- Maynard (arXiv:2011.12275): c_d/K, essentially optimal in K.
- Lau (arXiv:2407.01611): fully explicit. Some n < x has
  ‖f_i(n)‖ ≪ x^(−1/(10.5·K·d(d−1)) + o(1)) for all i.

Gowers's per-form iteration (K^(−2^(k+1)·q)) is therefore not forced. A
multilinear-forms version of Lemma 16.1 with width exponent poly(1/q)
should follow from these bounds. Lau's explicit exponent is the natural
input for a formalization.

**Two caveats.**
1. Lemma 16.1 needs a *partition* of a box into cells. Each cell needs
   smallness uniformly over its points. The reduction to one-variable
   polynomials in the common difference must keep the number of polynomials
   polynomial in q. Expanding a k-linear μ_i on a k-dimensional cell gives
   O(2^k) coefficient polynomials per form, so K = O(2^k·q). That is still
   polynomial in q.
2. The o(1) in Lau's bound, and the size of x relative to the cell width,
   must be made explicit.

**Consequences if (D) holds.**
- The lift's recurrence factor would become poly(1/n) instead of 576^(−24n).
- Part J's hypotheses would weaken from polynomial to quasi-polynomial
  counts (J.1).
- Theorem 16.2 in dimension three would then be conditional on a
  quasi-polynomial stackable structure, plus the readout (R) of J.2.

**Existing checked Schmidt input (2026-10-08).** The density port already
contains `OAI.Erdos3.simultaneous_monomial_recurrence` in
[`PolynomialCoordinatePartition.lean`](../../../../lib/openai-math/lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean).
For each fixed degree `j+1` it supplies constants `K >= 1`, `p > 0`,
independent of the number `d` of coefficients. If
`N >= (K*(d+1)/R)^(p*(d+1)^2)`, with `0 < R <= 1`, there is an integer
`1 <= q <= N` making all `q^(j+1)*alpha_i` within `R` of integers.
Thus the required polynomial dependence on the number of simultaneous
monomials is already formalized, including the quadratic case.

The same module proves `exists_polynomial_coordinate_partition_bound`:
for fixed degree `k`, constants `K,p` give an arithmetic-progression
partition whenever `H >= K*(d+1)` and `N >= H^(p*(d+1)^(2*k))`.
It bounds `card(labels)*H <= 2^k*N` and the coordinate error by `k/H`.
This is an average-length bound, not a minimum length for every cell.

This is manifest entry 3295, included in the completed prefix-3400 build
and axiom audit. No additional upstream port is needed to use these results.
`Proofs05SchmidtRecurrence.simultaneous_modular_monomial_recurrence` now
transfers the monomial theorem to the Gowers centered norm on `ZMod N`:
under the same bound with search limit `M`, it produces `1 <= q <= M`
and `centeredAbs(q^(j+1)*a_i) < R*N` simultaneously. The modulus and the
search limit are separate; a use requiring a nonzero modular multiplier
can impose `M < N`. Its module passed an isolated Lean check, and the
updated facade audit is queued.
The same module also proves `exists_mixed_modular_recurrence_bound`.
For fixed maximum degree `k`, constants `K,p` give a common
`1 <= q <= H^(p*(d+1)^(2*k))` making every monomial in `d` families and
degrees `1,...,k` smaller than `N/H`, provided `H >= K*(d+1)`.
The induction first makes the highest degree sufficiently small to survive
a bounded multiplier chosen for all lower degrees. Its exponent estimate
is checked in `schmidt_mixed_exponent_bound`. This strengthens the available
recurrence input, while leaving the box-partition obligation below open.
The remaining work is the bridge to a simultaneous multilinear **box**
partition satisfying Lemma 16.1's minimum-width and uniform-smallness
requirements, and adequate degree constants. The constants above are
existential; neither the bridge nor the printed final threshold follows
merely by importing the module.

## K. Where every route to Theorems 18.2 and 18.7 meets (2026-10-08)

The user's goal changed on 2026-10-08: proofs of the final results, by any
formalization path. This part records where the available paths stand. It
draws on `PORT_CONSTANTS_SURVEY.md`.

### K.1 The openai/math port cannot reach them (proved by inspection)

The port's descent increments only sets of density below about κ²/2 < 1/2.
Its relative lift needs `2a ≤ mean` and target `≤ 1`, and its amplified
levels need `H²a ≤ 1`. Its dense case is a black-box Szemerédi theorem
(hypergraph removal, tower/Ackermann constants).

Explicitizing the port therefore reduces 18.2 and 18.7 to a **quantitative
dense Szemerédi theorem**. For example, sets of density 1/2 in [N] contain
k-APs once N ≥ 2^2^2^2^2^(k+9). That statement is Gowers's.

### K.2 The paper's own chain does not supply polynomial bounds (transcription-based)

**(γ, r)-multiple multilinearity** (§16 definition, transcription line 3342)
asks for boxes of width m^(c(θ/r,γ,k)^r) and at most q(θ/r,γ,k)^r functions.

- The exponent r is forced. Lemma 16.8 (r sets of parameter s give
  parameter rs) refines partitions sequentially, so the exponents compound.
- Theorem 16.2 gives r = γ⁻²·s(θ,γ,k) = poly(1/θ).
- So Corollary 16.11's density and width exponent are
  c_* = (α/8)·c(α/(8r), α/2, k)^r = exp(−poly(1/α)).
- The printed (α/2)^(2^2^(k+8)) would need r = O(1). That is, it would need
  one (γ,1)-multiply multilinear piece of polynomial mass, which is what
  printed Lemma 16.10 asserts. That encoding is formally refuted
  (`lemma_16_10_printed_unit_encoding`, at k = θ = γ = 1).
- The transcription's editorial note at Corollary 16.11 already records
  that the printed comparison runs the wrong way.

Consequences:
- With c_* = exp(−poly), the density iteration needs n = exp(poly(1/δ))
  steps, and the threshold is triple exponential (Part I).
- So as far as this project can reconstruct it, the paper does not
  establish Theorem 18.1 at degree ≥ 3 with its printed exponent. Nor does it
  establish Theorems 18.2 and 18.7 at k ≥ 6 with their printed thresholds.
  Lengths up to 5 avoid §16 in higher dimensions and are proved
  (`theorem_18_2_le_five`).

**Published-source check (2026-10-08).** The
[published article PDF](https://www.cs.umd.edu/~gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf)
was inspected as rendered pages, not just extracted text. Printed page 567
(PDF page 103) confirms the nested `r` exponent in the width and the `r`
power in the graph count. Printed page 576 (PDF page 112) confirms those
powers in the proof of Corollary 16.11 and its stated polynomial exponent.
These locations agree with the transcription; this check does not repair
the quantitative comparison.

**Kernel-checked comparison.** `section16CorollaryExponent_lt_printed`
(`Proofs16CorollaryExponentGap`) proves the supplied exponent strictly
below the printed (α/2)^(2^(2^(k+9))), for every 0 < α ≤ 1/2 and every k.
The iteration parameter r is at least the degree A = 2^(2^(k+8)), so
c^r ≤ (α/2)^(A²).

The Lean counterexample refutes `lemma_16_10_printed_unit_encoding`, whose
premises are the two packaged cover conditions. It does not by itself
refute every formulation retaining the full preceding construction of
`phi1`, or rule out another proof of the published theorem. The present
obstruction concerns the implemented route and its stated interfaces.

Downloaded PDF SHA-256:
`6ab8e20052bd59f80f1b74d9564179da43954646f0b2cc6aa5b63d6004758866`.
Reproduce the visual check with `pdftoppm -f 103 -singlefile` and
`pdftoppm -f 112 -singlefile` on the linked PDF.

### K.3 What would close 18.2 and 18.7 for every k

- **Polynomial Corollary 16.11 in every dimension.** For φ with the γ-product
  property on a set of density α in Z_N^d, one needs a box of width
  N^(poly(α)) and a multilinear map agreeing with φ on poly(α) of it. This is
  a polynomial-bound inverse theorem for Freiman multi-homomorphisms
  over Z_N.
- **Known bounds.**
  - d = 1: polynomial; this is Gowers's §7.
  - d ≥ 2: iterated exponential (Gowers–Milićević 2020).
  - d = 2: quasi-polynomial (Milićević 2026).
- **Quasi-polynomial is not enough for 18.2.** It gives n = exp(polylog(1/δ))
  iterations. The threshold exp exp exp(polylog(1/δ)) exceeds 2^2^(δ^(−M))
  as δ → 0 whenever the polylog exponent exceeds 1.
- **Corollary 18.7 is different:** it is the single density 1/2, so for each
  fixed k it is a numerical comparison of constants with no asymptotics in
  δ. K.4 settles k = 6: the proved structure does not fit, and the input
  that would fit is a trilinear inverse theorem that is not available.

### K.4 Corollary 18.7 at k = 6 from the proved dimension-two structure: no (proved by definitions)

Route: `quartic_function_inverse_explicit`, then
`theorem_18_2_of_function_discrepancy_budget`'s mechanism at δ = 1/2, then
`corollary_18_7_at_of_half_density`.

**The discrepancy parameter.**
- The input is α = `intervalUniformityParameter (1/2) 6`
  = (2⁻⁶/(512·216))^32 ≈ 2^(−728).
- The parameter is β = `jointStructuralInverseParameter 2 α`. It is at most
  `section16JointFrequencyDensity α' 2` = (α'/8)/G with α' ≤ α
  (`jointPowerLocalizationParameter`; the other factors are ≤ 1).
- G ≥ `section16UniformLiftGraphBudget` ≥ multipleQ(x, γ, 2)^(r·s), where
  r ≥ 1, γx ≤ 1/2, so multipleQ ≥ 2^(2^1024).
- Here s = `section16PowerSliceBudget (α/4) (α/2) 2`
  = (4/α²)·multipleS(α/64, α/2, 2) ≥ (256/α²)^(2^256).
- Hence log₂(1/β) ≥ 2^1024·s ≥ 2^(1464·2^256).

**The comparison.**
- `intervalDiscrepancyClosedThreshold` ≥ exp(2^n) with n = ⌈8/β⌉, so its
  log₂ log₂ is at least 8/β, i.e. about 2^(2^(1464·2^256)).
- `szemerediThreshold (1/2) 6` = 2^2^2^M with M = 2^32768, so its
  log₂ log₂ is 2^M = 2^(2^32768).
- The shortfall is at the third exponential level. No adjustment of
  constants closes it.
- **Kernel-checked:** `lengthSix_half_density_route_exceeds`
  (`Proofs18LengthSixRouteGap`). For every σ and T,
  `szemerediThreshold (1/2) 6` is strictly below
  `intervalDiscrepancyClosedThreshold 6 (1/2) β σ T`, where
  β = `jointStructuralInverseParameter 2 (intervalUniformityParameter (1/2) 6)`.
  The proof uses only β ≤ 1/G, G ≥ 2^(2^(2^256)) (`section16JointPowerGraphBudget_ge`)
  and the threshold ≥ exp(2^⌈8/β⌉). All towers stay symbolic.

**What would close it.** G is the budget of the *joint* frequency box.

- `section16_joint_frequency_box` at k = 2 takes degree-4 non-uniformity
  to a box in Z_N^3. The frequency function there has **three** variables.
  It is built from dimension-≤ 2 structure (Theorem 16.2 at dimensions 1
  and 2) by the lift, which is where exp(poly) enters (Parts B and H).
- The needed input is therefore a structure theorem for three-variable
  (Freiman trihomomorphism-type) frequency functions. A single dense
  multilinear piece of density c(α) is enough; it does not have to be lifted
  from dimension two.
- **Polynomial** c(α) = α^D fits whenever D ≲ 2^32768/728.
- **Quasi-polynomial** c(α) = exp(−C·log^A(1/α)) fits whenever A ≲ 3400,
  with moderate C.

**Correction (same day).** An earlier version of this paragraph proposed
Milićević's 2026 theorem as that input. It is not. That theorem
(arXiv:2601.01682) is a quasi-polynomial **U⁴** inverse theorem, built on a
structure result for two-variable Freiman **bi**homomorphisms. Two
variables correspond to degree 3, i.e. five-term progressions, which are
already proved here (`theorem_18_2_le_five`). Six-term progressions need
the trilinear case, and no quasi-polynomial bound is known for it
(Gowers–Milićević 2020: iterated exponential).

Feeding a quasi-polynomial two-variable count into the lift does not
help either. Lemma 16.1's width exponent is exponential in the graph count
(Part B). Then log₂(1/β) ≈ exp(728^A) ≫ 2^32768 for every A ≥ 2.

So **Corollary 18.7 at k = 6, like the all-k statements, needs a
quasi-polynomial (or better) trilinear inverse input that the literature
does not provide.**

## F. Routes

1. **Quantitative repair (research).**
   - Strengthen the induction hypothesis to polynomial graph counts, which
     repairs B.
   - Prove a θ′-free lift with power-decaying losses, which repairs A and
     meets E.
   - Check the degree budget against `s(θ,γ,k) = (2/θγ)^(2^(2^(k+6)))`.

   Success would close 16.2 exactly. It would give 16.11 and 18.1 only if
   the exponents still fit their printed forms.
2. **Qualitative all-dimension induction (formal engineering).**
   - Replace `MultiplyLinear`'s fixed control functions by arbitrary ones in
     Lemmas 16.4–16.9, the line covers and the lift. The lift is already
     proved with explicit, non-uniform controls; see
     `Section16JointPowerCoverProfile`, which is unconditional in dimension 2.
   - Then induct on the power-cover profile itself.

   This would give a genuine all-dimension structure theorem, and with §17–18
   an all-length Szemerédi theorem by Gowers's method with explicit but
   tower-type bounds. It would not close the catalogue items as encoded
   unless their constants were migrated. It touches about 46 modules
   (about 18k lines of `Proofs16*`).
3. **Theorem 1.3 independently.** Port the openai/math headline:
   4,136-module closure, of which 128 are already vendored.
4. **Bohr-structured induction (H.4).** Carry Bohr-multilinearity rather
   than `Theorem162At` through the induction.
   - Steps (i) and (ii) are formalizable now. Step (ii) generalizes
     Corollary 7.11 from one AP to a box with common difference.
   - Preservation under the lift is the research problem.
   - With any bounds, this would give route 2's qualitative all-dimension
     theorem.
   - With polynomial rank, it would give the exact Theorem 16.2 in every
     dimension.
   - The dimension-two route alone cannot reach dimension three (H.3).
5. **Theorems 18.2 and 18.7 from openai-math with explicit constants.**
   *Proved arithmetic; the port is infeasible for now.*
   - Theorem 18.2 assumes δ ≤ 1/2 and
     `N ≥ 2^(2^X)` with `X = δ^(−2^(2^(k+9)))`, so `log log N ≥ X·log 2 − 1`.
     The openai-math bound
     `r_k(N) ≤ C·N·exp(−c·(log log N)^(1+η))` falls below `δN` as soon as
     `c·(X/2)^(1+η) > log C + log(1/δ)`. Since `log(1/δ) = (log X)/2^(2^(k+9))`
     and `X ≥ 2^(2^(2^(k+9)))`, this needs only `log C / c` to be at most
     about that size.
   - Corollary 18.7 already follows from 18.2
     (`corollary_18_7_holds_of_theorem_18_2`).
   - Upstream, however, states and proves `QuantitativeDensityBound` with
     `∃ C c η`. The headline's witness comes from an induction of
     existential powers (`exists_manuscriptRelativePatchPower`).
   - Scale of the Progressions tree: 4,774 Lean files, 128 of which use
     filter asymptotics (412 occurrences), and 4,844 `exists_*` theorems.
     Making the constants explicit would mean re-proving much of a
     million-line development. Asking upstream for an explicit-constant
     headline is the realistic form of this route.
