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

## B. The original Lemma 16.1 route loses exponentially in the graph count

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

**A route for (R), one-variable core (proposal, 2026-10-08).**

1. **Cocycle.** Let φ be an E-homomorphism on a progression. Then
   c(x, y) = φ(x+y) − φ(x) − φ(y) + φ(0) lies in E (take the quadruple
   (x+y, 0, x, y)). So c takes at most 2^r values.
2. **Bracket structure (corrected the same day).** The defect of an
   E-homomorphism lies in E ∩ (−E): reversing the quadruple negates the
   defect. So if E's generators were in general position, φ would be an
   exact Freiman homomorphism, which is the trivial case. The genuine cases
   have relations. A bracket ⌊αx⌋ has defects in {−1, 0, 1}, with
   generators 1 and −1.

   The usable structure is in the first differences
   D(j) = φ(x₀ + (j+1)u) − φ(x₀ + ju) along a progression.
   - The quadruple (j+1, j′, j, j′+1) gives D(j) − D(j′) ∈ E, so D takes at
     most |E| ≤ 2^r values.
   - The quadruple (j+h, j′, j, j′+h) gives that window sums of equal length
     differ by an element of E.

   So D is a **balanced sequence** over a finite alphabet in Z_N. For two
   letters, Morse–Hedlund applies: finite balanced binary words are exactly
   the factors of Sturmian (mechanical) words ⌊(t+1)α + β⌋ − ⌊tα + β⌋
   (Lothaire, *Algebraic Combinatorics on Words*, Ch. 2). Each letter's
   counting function is then a bracket, so φ is bracket-linear along the
   progression. For alphabets larger than two, balance per letter can fail
   (Fraenkel's problem). The quantity actually needed is the window
   discrepancy of each letter, bounded by a constant depending on r. That
   multi-letter structure is the research content of step 2.
3. **Linearization.** Take u ≤ M^r with every ‖u·α_i‖ ≤ 1/M; this is
   simultaneous Dirichlet, `simultaneous_small_multiplier` with exponent
   1/r. Along x₀ + j·u the brackets have no carries, except at most r·O(1)
   break points per window of length M. So φ is exactly affine on
   sub-progressions of length about M/(r+2), with step u. Relative to a
   length L ≥ M^(r+1), pieces have length about L^(1/(r+1)), an exponent
   polynomial in r. Milićević's r is quasi-polynomial, so this is
   exp(−polylog), within the dimension-three budget of Part H.5.
4. **Two variables.** Fix y and apply step 3 in x. The step u can be chosen
   uniformly over y in a sub-Bohr set, because the α_i come from E and not
   from y. Then repeat in y. This needs the frequencies α_i to depend
   bilinearly on (x, y). That is the E-bilinear-map setting of Milićević
   §1.1, so it should be checked against his Sections 5–11 before any
   formalization.

Status: step 3 is formalized (`Proofs16BracketWindow`:
`exists_common_constant_window`, `bracketLinear_affine_window`). Steps 2
and 4 are research. Step 2's two-letter case reduces to Morse–Hedlund.

**A better route for (R): through Milićević's bilinear Bohr varieties
(2026-10-08).** Milićević §1.1 lists three roughly equivalent classes:
almost-trilinear forms, E-bilinear maps on B × B, and Freiman-bilinear maps
on a bilinear Bohr variety. His §§5–11, with the bilinear Bogolyubov
argument, pass from E-bilinear maps to Freiman-bilinear maps
Φ : V → Ĝ, where V = {(x, y) ∈ B × B : β_j(x, y) small for j ≤ t} for
bilinear forms β_j. §12 gives the reverse direction.

- On a product box P × Q ⊆ V, a Freiman-bilinear map is genuinely bilinear
  (Lemma 7.8 in each variable), which is exactly the readout.
- Finding product boxes inside V means making the t bilinear forms β_j
  simultaneously small on boxes. That is the multilinear Lemma 16.1 with
  exponent polynomial in t: item (D), which the peer is building on
  Schmidt recurrence (`Proofs05SchmidtRecurrence`, minimum-length
  simultaneous polynomial partitions).

So **(R) reduces to (D) plus Milićević §§5–12**, with no bracket analysis.

**Direction check (from the paper's proof overview, pp. 8–11).** In
Milićević's proof, the Freiman bihomomorphism on a bilinear Bohr variety is
an intermediate object. Only his final step *extends* it, with controlled
errors, to the E-bihomomorphism on a product of Bohr sets that Theorem 1.4
states. So the natural input for (R) is the pre-extension statement.
`Proofs16BilinearBohrVariety` states it as `MilicevicVarietyStructure D`;
it is a hypothesis, extracted from the overview and not quoted from a
numbered theorem. The module also proves `freiman_on_variety_biaffine`:
on any product of progressions satisfying the variety's conditions, the map
is bi-affine. Those conditions are Bohr membership in each coordinate and
every L_i(y)·x small, i.e. simultaneously small bilinear-type quantities,
item (D).

**Progress (2026-10-08, kernel-checked).**
- `bilinearBohrVariety_contains_product` (`Proofs16VarietyBoxes`): if the
  L_k are Freiman-linear, the variety contains
  {i·u : i < L₁} × {j·v : j < L₂} with u ≤ M₁^(|Γ|+2r) and v ≤ M₂^|Ψ|,
  whenever L₂ ≤ ρM₂ and L₁(1 + L₂) ≤ ρM₁. Simultaneous Dirichlet is used
  twice; the L_k are affine along the column. Exponents are linear in
  codimension and rank.
- `freiman_on_variety_biaffine_at_origin`: any Freiman bihomomorphism on
  the variety is bi-affine on that box. This is the readout at the origin.

**Remaining gap for (R) → Part J.**
1. **Off-origin cells.** `MultiplyLinear` asks for partitions of
   *arbitrary* boxes. The variety is not translation-invariant: x ranges
   over B({L_k(y)}; ρ), which moves with y. Covering a box far from the
   origin needs the variety conditions relative to a base point. The
   L_k(y₀ + j·e)·(x₀ + i·d) expansion adds the constant terms
   L_k(y₀)·x₀, which are not small in general. So cells exist only near
   points of V, and covers must be built from V's own geometry. Gowers's
   multiply-linear framework does not ask for covers off the domain, so
   the restriction to V may suffice. The bookkeeping of
   `CubicStackableClass` against V's geometry has not been worked out.
2. **Unions (stackability).** n pieces give n varieties. Common boxes need
   the union of all their Γ, Ψ and L-families, which is still linear in
   the total rank by the exponents above. That is the (D)-type win.
3. **The pre-extension hypothesis** `MilicevicVarietyStructure D`, from
   the paper, not proved here.

Item 2 is done: `varieties_common_product` (`Proofs16VarietyUnions`)
gives one box common to n varieties, with step exponents
|⋃Γ| + 2Σr and |⋃Ψ|, linear in the total codimension and rank.

**Item 1 decomposed.** On a cell (x₀ + i·d) × (y₀ + j·e),

  L_k(y₀ + je)·(x₀ + id) = L_k(y₀)x₀ + i·L_k(y₀)d + j·Δ_k x₀ + ij·Δ_k d,

where Δ_k = L_k(e) − L_k(0) (L_k is affine along the column).
- **Variation terms** (the last three) must be ≤ εN on the cell. They are
  common-difference products of linear forms with the cell's steps. That is
  exactly the form of the peer's polynomial-exponent Lemma 16.1
  (`exists_simultaneous_commonDiff_partition_two_bound`, exponent
  p·(q+1)^(2^(k+2))), applied to the forms y ↦ L_k(y) and x ↦ Δ_k·x. The
  same holds for the Bohr frequencies Γ, Ψ.
- **The constant term** L_k(y₀)x₀, and γx₀, ψy₀, decides whether the cell
  is inside V, outside V, or straddles its boundary. Straddling cells are
  the loss. Bounding their mass by θ is Bourgain's regular-Bohr-set
  argument: choose ρ so that B(ρ(1+κ)) ∖ B(ρ(1−κ)) has relative size
  O(κ·rank). The port has it, in the audited prefix (manifest entry 780):
  `CyclicBohr.Set.IsRankRegular` puts the annulus at relative size
  ≤ 100·d·κ with d = 2·max(rank, 1), and `exists_rankRegular_ndilate`
  finds a regular dilate at some radius in [1/2, 1]
  (`OAI/.../Fourier/BohrTorusApproximation.lean`). Its `CyclicBohr.Set`
  must be matched to the corpus's `bohr K ρ`.

**A subtlety at base points away from the origin (2026-10-08).**
- At (x₀, y₀), the cross term j·(L_k(e) − L_k(0))·x₀ must be small. The
  step e must therefore make a *Freiman-linear* function of e small, not a
  linear one.
- At the origin this term is absent (x₀ = 0). That is why
  `bilinearBohrVariety_contains_product` works with Dirichlet alone.
- Off the origin, Dirichlet handles it only if L_k is affine
  (y ↦ λy + c) on the Bohr set. In Z_N a Bohr set is essentially a proper
  generalized arithmetic progression, and a Freiman-linear map on it is
  affine in the progression's *coordinates*: L(a + Σ n_i g_i) = c + Σ n_i λ_i.
  It is not affine in y.
- So off-origin cells need Bohr sets presented as generalized progressions
  (Milićević Prop. 2.13 / Thm. 2.26, Gowers §7), with Dirichlet applied per
  coordinate.
- The coordinate statement itself, that Freiman-linear maps on a proper
  GAP are coordinate-affine, is elementary: the second-difference argument
  in each coordinate, as in `affine_of_second_difference`. It is the next
  formalizable piece.

**Update (same day): single off-origin boxes need no GAP coordinates.**
`bilinearBohrVariety_contains_box_at` (`Proofs16VarietyBoxAt`) builds a
box around any deep point (x₀, y₀) of V with three nested
simultaneous-Dirichlet choices.
1. e₁ over Ψ, so that L is affine along a long run of multiples of e₁.
2. t over {δ_k·x₀}, with e = t·e₁. The quadruple (y₀ + e) + 0 = y₀ + e
   makes L(y₀ + e) − L(y₀) = L(e) − L(0) = t·δ_k.
3. d over Γ ∪ {L_k(y₀)} ∪ {t·δ_k}.

The coordinate lemma (`freiman_linear_gap_affine`, `Proofs16GapCoordinates`)
is proved too, but not needed for single boxes.

**What remains for (R)'s covers.** A packing/partition: cover all but θ of
V's points inside an arbitrary box P by disjoint such boxes. The deep
points are the bulk of V for a regular radius (port Bohr regularity). The
cells' per-point steps must tile, which is the peer's Lemma 16.1
partition machinery. This is composition, not new mathematics, plus the
pre-extension hypothesis.

**Bohr-side size control, proved (same day).**
- `bohr_card_le_four_pow` (`Proofs16BohrDoubling`):
  |B(K;ρ)| ≤ 4^|K|·|B(K;ρ/2)|.
- `bohr_exists_regular_step` (`Proofs16BohrRegularStep`): among the radii
  ρ(1 − j/(2m)), some consecutive ratio is ≤ 4^(|K|/m), which is about
  1 + θ for m ≈ |K|/θ.

These work directly with the corpus's `bohr`, without OAI.

**Next: variety doubling.** |V(ρ)| = Σ_{y ∈ B(Ψ;ρ)} |B(Γ ∪ {L_k(y)}; ρ)|.
The fibres double by `bohr_card_le_four_pow`. The y-range needs a cell
argument:
- bucket y ∈ B(Ψ;ρ) into 4^|Ψ| cells with representatives y₀, so that
  y − y₀ ∈ B(Ψ;ρ/2);
- Freiman-linearity gives L(y) = L(y − y₀) + (L(y₀) − L(0));
- so each fibre over y injects, by x ↦ x, into the fibre over y − y₀ of a
  variety with r more frequencies, namely the constants L_k(y₀) − L_k(0)
  on that cell.

Bounding the fibre at radius ρ by one at radius ρ/2 needs the radii split
between the two terms, which adds one more Bohr-doubling factor. So the
expected bound is |V(ρ)| ≤ 4^O(|Γ|+|Ψ|+r)·|V′(ρ/2)| for a slightly
enlarged variety V′, and the regular step is then taken over the enlarged
family.

**Correction (same day): naive variety doubling fails.**
- The shift L(y) = L(w) + c sends the fibre over y to
  B(Γ ∪ {L_k(w) + c_k}; ρ), a variety with *shifted* frequencies.
- Nothing compares it with the unshifted fibre B(Γ ∪ {L_k(w)}; ρ/2). The
  condition |(L(w) + c)·x| ≤ ρN neither implies nor is implied by
  |L(w)·x| ≤ ρN/2.
- So a single variety does not double with respect to itself. The natural
  object is the family of shifted varieties {V_c}. Controlling their sizes
  uniformly is the content of Milićević's §3 algebraic regularity method
  ("efficient algebraic regularity lemma", his Theorem 3.5, generalized
  from [49]).

The packing step therefore needs that regularity input, beyond the
Bohr-side lemmas proved here. It is a further hypothesis to state
precisely, or a substantial formalization in its own right. It is not
composition.

**From Milićević §2 (read 2026-10-08, pp. 30–39).**
- His equation (9) is Freiman-linearity on a coset progression in
  coordinates, φ(Σ λ_i e_i + h) = Σ λ_i φ(e_i) + φ(h). That is
  `freiman_linear_gap_affine` (`Proofs16GapCoordinates`), so the formal
  lemma matches his usage.
- **Proposition 2.37 ("Bohr–Bohr sets are Bohr")** may replace variety
  doubling. For a Freiman-linear φ : B(Γ;ρ) → 𝕋^d, with r = |Γ|, the set
  {x ∈ B : ‖φ(x)‖ ≤ σ} contains a Bohr set of codimension at most
  d + (2r log(σ⁻¹ρ⁻¹))^O(1) and radius at least σ(2r log(σ⁻¹ρ⁻¹))^(−O(1)).
- For fixed x, the variety's y-section {y ∈ B(Ψ;ρ) : ‖L(y)·x/N‖ ≤ ρ} is
  such a set, since y ↦ L(y)·x is Freiman-linear.
- So every y-section contains a genuine Bohr set, of quasi-polynomial
  codimension, where `bohr_card_le_four_pow` and `bohr_exists_regular_step`
  apply section by section.
- Packing could then proceed section by section in y, with boxes in x
  supplied by the x-direction Dirichlet argument of
  `bilinearBohrVariety_contains_box_at`. That would avoid shifted-family
  regularity. Not yet checked in detail.

**Formalized (same day, normalized interface).** `BohrBohrIsBohr D` is a
one-coordinate hypothesis motivated by Proposition 2.37, with `phi(0)=0`
explicit. Under this hypothesis and `L_k(0)=0` for every k,
`variety_full_section_contains_bohr` gives, for every x ∈ B(Γ;ρ),
{x} × B(Ψ″;ρ″) ⊆ V with |Ψ″| ≤ |Ψ| + r(1 + loss^D) and
ρ″ ≥ ρ/loss^D (`Proofs16BohrBohrSections`).

**Normalization correction.** The corpus's four-point
`IsFreimanLinearOn` identity also admits constant nonzero maps. Since every
centered Bohr set of nonnegative radius contains zero, an unnormalized
all-sublevels hypothesis would force every such map to vanish at zero and
would therefore be false. `bohr_sublevels_require_zero` proves the necessary
normalization in Lean. The conditional section lemmas now state it, rather
than silently accepting a vacuous premise. Applying this route to affine
frequency families with nonzero intercepts requires an additional centering
or translated-sublevel argument. No existence proof for the normalized
interface is asserted.

**Two observations from attempting the packing.**
1. **x-fibres need no hypothesis.** For fixed y, the x-section of V is
   exactly the Bohr set B(Γ ∪ {L_k(y)}; ρ). Proposition 2.37 is needed
   only for y-sections.
2. **The real obstruction is partial cells.** `MultiplyLinear` asks that,
   on each cell, Φ's graph over V ∩ cell ∩ H be covered by few
   multilinear functions. If V ∩ cell is not a product set, the bi-affine
   argument breaks at the boundary, because the quadruple chains leave V.
   Two options:
   - use only cells inside V, and put the boundary mass in the θ-loss set
     H^c. That needs boundary mass ≤ θ, a regularity statement for V
     itself: the shifted-family issue again, but only for the boundary;
   - prove that Φ on a "convex" V ∩ cell, an interval on each line, is
     still covered by O(1) multilinear pieces. That needs quadruples
     linking neighbouring lines inside V.

   Either is a genuine lemma, not bookkeeping.

**Linking option formalized (same day).**
- `biaffine_coeffs_eq_of_square`, `biaffine_glue`,
  `freiman_bihom_biaffine_on_chain` (`Proofs16BiaffineGluing`): one
  bi-affine function on any chain of boxes whose consecutive members share
  a 2 × 2 square.
- `bohr_row_convex` (`Proofs16BohrRowIntervals`): in a slow cell each
  row's Bohr section is an interval. It uses the no-wrap lemma
  `valMinAbs_add_of_small`.
- `freiman_bihom_biaffine_on_staircase`: height-3 boxes chained along row
  intervals whose consecutive triples and quadruples overlap in at least
  two columns. Height-2 boxes provably cannot be glued, since they share
  one row.

**Where it bottoms out.** With cell steps making every variation term
≤ εN (the peer's polynomial Lemma 16.1 supplies this):
- cells with all variety conditions ≤ (ρ − 3ε)N lie inside V;
- cells with some condition > (ρ + 3ε)N miss V;
- only boundary cells are partial. The staircase lemma covers their
  interiors.

The θ-loss budget still needs **the total mass of boundary cells** to be
small. That is a regularity statement for V: the mass of V(ρ + 3ε) ∖ V(ρ − 3ε)
relative to V(ρ), with the shifted-family issue above. So the packing
reduces exactly to variety regularity (Milićević §3), and every other
ingredient is now proved here or in the peer's lane.

**Update and audit (same day): variety regularity is proved, with a caveat
on the input.**
- `variety_exists_regular_step` (`Proofs16VarietyRegularStep`) needs no
  algebraic regularity. The telescoping argument only uses a global ratio
  bound, |V(ρ)| ≤ N² ≤ M^dim·|V(ρ/2)|, from `variety_card_lower` (Bohr lower
  bounds summed over fibres: `bohr_card_lower`, `variety_card_eq_sum`).
  The boundary-cell mass is thereby controlled: restrict to V(ρ_j) and
  take 3ε ≤ ρ/(2m). The domain points in boundary cells then lie in
  V(ρ_j) ∖ V(ρ_{j+1}), a θ-fraction of V(ρ_j).
- **Audit caveat.** `MilicevicVarietyStructure` guarantees agreement
  Φ = φ (after shifts) on many points of V(ρ), not of V(ρ_j). Those
  points could all lie in V(ρ) ∖ V(ρ_j). The packing therefore needs the
  input with agreement inside a regular sub-radius. Milićević's own proofs
  plausibly supply this, since they pick regular radii throughout, but the
  Prop as stated does not. Strengthening the hypothesis accordingly, or
  showing that agreement transfers to V(ρ_j) by averaging, is the
  remaining check on this route.
- **Source check and resolution (2026-10-08).** I read arXiv:2601.01682:
  Proposition 11.1 (pp. 73–74), Lemma 11.2 (p. 74), and the proof of
  Theorem 1.4 (§13, pp. 92–93). The paper never relates the structured map
  pointwise to φ before the very last step. Instead:
  - Proposition 11.1 gives a Freiman-bilinear ψ on a variety V′ (radius
    ρ′ ≥ Ω(ρ), base C′ ⊆ C dense). For **every** (x, y) ∈ V′, at least
    c′|C|^29|G₂|^6 of the (4,3,3)-arrangements of lengths (x, y) have all
    their arguments in V and satisfy ψ(x,y) = Σ_{i∈[36]} ν_i φ(a_i, b_i).
  - Lemma 11.2 (gap filling) gives ψ = φ̃ on a (1 − ε^{1/8}(2/ρ)^{O(r+d)})
    fraction of a shrunk domain (C/20000 × G₂) ∩ V_{ρ/20000}. Here φ̃ is an
    intermediate map, not the original φ.
  - §13 ends with an arrangement identity on C₁ × B₁ and says "the result
    follows by averaging and Theorem 2.26". Pointwise agreement
    Φ(x,y) = φ(x+s, y+t) is produced only there.

  Because the arrangement identity holds at every point of the domain, the
  final averaging can run over any sub-domain of comparable size, for
  example V(ρ/2). The loss is |V(ρ)|/|V(ρ/2)| ≤ M^dim (`variety_card_lower`),
  which the quasi-polynomial bound absorbs. **So the deep form is the right
  hypothesis:** `MilicevicDeepVarietyStructure` (`Proofs16DeepAgreement`)
  counts agreement points in V(ρ/2). Every regular-step radius
  ρ_j = ρ(1 − j/(2m)), with j ≤ m, is at least ρ/2 (`regular_radius_ge_half`).
  So `deep_regular_step` yields a step j with the ratio bound and the full
  agreement mass in **both** V(ρ_j) and V(ρ_{j+1}). The deep form implies the
  shallow one (`MilicevicDeepVarietyStructure.toShallow`). All of these are
  kernel-checked, with axioms propext, Classical.choice, Quot.sound.

  Two honest residues:
  1. Theorem 2.26 linearizes the leftover arrangement terms on a coset
     progression, which can shrink the domain once more. The paper states
     its conclusion only after extension, on B₁ × B₂, so neither variety form
     is a quoted theorem. Both remain hypotheses, and the deep one is no less
     faithful than the shallow one.
  2. The paper's varieties are transposed relative to ours: x lies in a coset
     progression C, and the y-conditions B(Θ_i(x); ρ) depend on x. Swapping
     coordinates matches them. C is a coset progression rather than a Bohr
     set; for G = ℤ/N with N prime the two are interchangeable at
     quasi-polynomial cost.
- **Deep agreement removes the θ-budget altogether (2026-10-08,
  kernel-checked).** Let Γ be the graph of Φ over S = V(ρ/2). Call a cell
  *good* if it misses S or lies inside V(ρ). On a good cell, one
  multilinear map covers Γ:
  - if the cell misses S, it carries no graph points;
  - if the cell lies inside V(ρ), Φ is bi-affine there, hence multilinear
    in the coordinates. This uses `multilinearOn_box_of_subset`, which works
    for every cell length, width-one cells included; for a zero common
    difference the box is a single point.

  So `multiplyLinearWith_of_good_partitions` (`Proofs16GoodPartition`)
  proves `MultiplyLinearWith` with q = 1 and loss set H = P. No θ is spent,
  and no regularity of V is used. The regular-step lemmas stay proved, but
  this route no longer needs them.

  A cell that meets V(ρ/2) and has pairwise oscillation at most ρN/2 in
  every variety condition lies in V(ρ) (`subset_variety_of_small_oscillation`,
  `Proofs16CellOscillation`). Hence `deep_structure_multiplyLinear`: if Φ is
  a Freiman bihomomorphism on V(ρ), and `OscillationPartitionsExist Eb Γ Ψ L ρ`
  holds, then Φ's graph over V(ρ/2) is multiply linear.
  `OscillationPartitionsExist` asks for partitions of every proper box into
  cells of width ≥ P.width^Eb(θ). Each cell must miss V(ρ/2) or oscillate by
  at most ρN/2. All of this is kernel-checked, with axioms propext,
  Classical.choice, Quot.sound.

**Correction (2026-10-08) to the paragraph that stood here.** It said
off-origin covers reduce to the peer's Lemma 16.1 plus Bohr regularity, and
that the rest is "bookkeeping with no new mathematics". Both halves were
too quick.
- Regularity is not needed, by the previous item.
- The remaining input, `OscillationPartitionsExist`, is **not** a direct
  instance of the peer's Lemma 16.1. Its conditions L_k(y)·x are only
  *Freiman*-bilinear, because L_k is Freiman-linear on B(Ψ;ρ), not linear
  on ℤ/N. On a cell (x₀ + i·c) × (y₀ + j·c), the variation terms are
  i·L_k(y₀)·c, j·Δ_k(c)·x₀ and ij·Δ_k(c)·c, where Δ_k(c) = L_k(c) − L_k(0).
  The middle term is not multilinear in (x₀, y₀, c), because
  Δ_k is Freiman-linear in c, not linear. Lemma 16.1 makes genuinely
  multilinear forms small, so it does not apply as stated.
- `Box` has one common difference c for both axes, so one step must
  satisfy all conditions at once. The nested-Dirichlet construction of
  `bilinearBohrVariety_contains_box_at` adapts to a single step
  (c = t·e₁ with e₁ chosen over Ψ ∪ Γ ∪ {L_k(y₀)}). That gives one box per
  deep point; it does not give a partition of an arbitrary box.

So what remains on the variety route is exactly two things:
1. A **partition** version of the deep-point box construction: Lemma 16.1
   for Freiman-bilinear forms on a Bohr set. Through Milićević's equation
   (9), Freiman-linear maps are coordinate-affine on a coset progression. In
   those coordinates the forms are genuinely bilinear, so the peer's lemma
   applies there. The remaining obstruction is transporting cells between
   GAP coordinates and boxes of ℤ/N.
2. ~~The translation from Φ's graph to φ's, by the shift (s, t).~~
   **Done** (`Proofs16VarietyTranslate`, kernel-checked):
   `deep_structure_multiplyLinear_phi` takes any part Γ_φ of φ's graph
   whose points, shifted back by (s, t), are deep agreement points
   (`varietyAgreement` at radius ρ/2). Given a Freiman bihomomorphism Φ on
   V(ρ) and `OscillationPartitionsExist` for the unshifted variety, Γ_φ is
   `MultiplyLinearWith` with one map per cell. It reuses the box and
   partition translation API of `Proofs16Translations`.

So, conditionally on `MilicevicDeepVarietyStructure`, the variety route's
only open input is item 1. That is `OscillationPartitionsExist`: Lemma 16.1
for Freiman-bilinear forms on a Bohr set.

**Item 1 at explicit scales, proved (2026-10-08).** The Freiman-bilinear
obstruction disappears after one preliminary partition
(`Proofs16OscillationPartition`):
1. **Linear stage.** Partition P by the |Γ| + |Ψ| linear maps x ↦ γx₀ and
   x ↦ ψx₁, to image diameter 4N/H₁ ≤ ρN/4.
2. **Bilinear stage.** A stage-1 cell that meets V(ρ/2) has its whole
   y-range in B(Ψ;ρ). There each L_k is affine along the cell's y-axis,
   since second differences vanish by Freiman-linearity. So
   x ↦ L_k(x₁)·x₀ agrees on the cell with a genuinely multilinear map
   (`freiman_column_multilinearOn`). Partition the cell again by these r
   maps, to diameter 4N/H₂ ≤ ρN/2. Cells that miss V(ρ/2) stay whole.

`oscillation_partition_of_scales` combines the two stages. Given
8 ≤ ρH₂, 16 ≤ ρH₁, K(r+1) ≤ H₂, K(|Γ|+|Ψ|+1) ≤ H₁, H₂^(p(r+1)^8) ≤ H₁ and
H₁^(p(|Γ|+|Ψ|+1)^8) ≤ P.width, it yields a partition into cells of width
≥ H₂. Each cell misses V(ρ/2) or oscillates by at most ρN/2. The width
exponent is 1/(p²(r+1)^8(|Γ|+|Ψ|+1)^8), **polynomial in the rank**, which
is the point of the peer's Schmidt-based Lemma 16.1.

The multilinear partition theorem enters as the hypothesis
`MultilinearDiameterPartition K p`, the verbatim k = 2 body of the peer's
`exists_simultaneous_multilinear_partition_bound`.
`Proofs16OscillationPartitionInst` discharges it in two lines. That module
imports the OAI port, so it is **not built on this machine** and is checked
only by the full-verification host. Everything else here is kernel-checked
locally, with axioms propext, Classical.choice, Quot.sound.

**Left for item 1: all-scale bookkeeping.** `OscillationPartitionsExist`
quantifies over every proper box, but the explicit scales need
P.width ≥ T, with T = H₀^(e₁e₂) and H₀ = ⌈max(K(r+1), K(|Γ|+|Ψ|+1), 16/ρ)⌉.
Boxes of smaller width cannot in general be cut into good cells of width
≥ P.width^E > 1. So the final `MultiplyLinearWith` should handle them
differently:
- chop the long axis into blocks of length in [w, 2w), where w = P.width;
- cover each block (fewer than 4T² points) by constant maps, using
  q ≤ 4T² maps per cell.

So Qb(θ) ≥ 4T², which is quasi-polynomial in 1/ρ and polynomial-exponent
in the rank. On wide boxes, choose H₂ as the largest h with
h^(e₁e₂) ≤ P.width, and take Eb = 1/(2e₁e₂).

**Done, by the peer (2026-10-08).** `exists_freiman_variety_cover`
(`Proofs16FreimanVarietyCover`, built on `Proofs16FreimanVarietyProfile`)
carries out this bookkeeping with the actual partition theorem, so it is
unconditional given the Freiman data. Small boxes use the existing coarse
cover (`multiplyLinearWith_of_large_box_covers`), which needs only **9**
maps. My parallel `variety_multiplyLinear_all_scales` landed two minutes
later with the weaker count 4T². It was removed as a strict duplicate;
see git history at 5758b5634. Lessons:
- On narrow boxes, cells need width only ≥ w^Eb, not w. Even the
  constant-cover route then costs about 4H₀ maps, not 4T².
- `set` on `⌈·⌉₊` makes `nlinarith` whnf-unfold `Nat.ceil` on ℝ and time
  out. Introduce such scales opaquely, with
  `obtain ⟨H₀, hH₀⟩ : ∃ H₀, H₀ = … := ⟨_, rfl⟩`.

**So item (R) of Part J is reduced to Milićević's structure alone.** Given
`MilicevicDeepVarietyStructure`, one variety's agreement graph is
multiply linear with count 9 (shift by (s, t): `MultiplyLinearWith.translate`).

**Heads-up for the stacking step (Part J's `CubicStackableClass`).** The
class fixes dimension one's controls: count 3nq and exponent
cubicBaseExponent(nq)(θ) = 2⁻²⁷θ³/(nq)⁴, which is degree 4 in the number n
of stacked members. Stacking n varieties by one joint two-stage partition
(all n(|Γ|+|Ψ|) linear phases, then all nr mixed phases) gives inverse
exponent ≈ p²(nr+1)⁸(n(|Γ|+|Ψ|)+1)⁸, degree **16** in n. Matching
2⁻²⁷/(nq)⁴ at θ = 1 needs q⁴ ≳ 2⁻²⁶p²r⁸(|Γ|+|Ψ|)⁸·n¹². No fixed q works
for all n. Sequential refinement is worse, since exponents multiply.
Possible repairs:
- (i) restate the cubic lift and `CubicStackableClass` with polynomial
  controls of general degree, (C n^a q, c θ^b/(nq)^a′);
- (ii) bound n by the lift's slice count R(θ, γ) and let q absorb poly(R).
  Then q is quasi-polynomial, and `PolyBoundedControl` has to weaken
  accordingly (J.3);
- (iii) a stacking argument that does not partition jointly.

**Correction (same night): repair (i) already exists at the lift level.**
The peer's polynomial lift `Proofs16PolynomialMultilinearCover`, unlike
the cubic packaging above, quantifies over **arbitrary** slice controls
`Section16SliceProvider B₁ φ₁ Pb Es`. It evaluates them only at
r = `samples` = ⌈6·max(1, q_Γ)/σ⌉. The count becomes
max(Pb, C(samples,2)·Pb²), and the width exponent is
`Es samples σ`. A degree-16 stacking exponent is therefore admissible as
it stands. Only Part J's packaging, `CubicStackableClass` with
`cubicBaseExponent`, is rigid. So the dimension-two slice provider for
varieties should target `Section16SliceProvider` with its own (Pb, Es),
not `CubicStackableClass`.
The bracket route above (steps 1–4) stays as a self-contained alternative
for the one-variable core, with step 3 formalized. With quasi-polynomial
t, a poly(1/t) exponent gives widths N^(exp(−polylog)), inside the
dimension-three budget (H.5).

**Is the detour worth it?** It feeds only Theorem 16.2 in dimension three
(Part J). By Part K it does not touch 18.2 or 18.7. Those need a trilinear
input that is polynomially or quasi-polynomially bounded, and none exists.

### J.4 The structure side (S) in dimension two (2026-10-08)

Part J's `StackableStructureAt 2 Q q` asks that, after removing θ of the
base, every product relation be covered by Q members of a stackable class.
The variety route splits this into three steps.

1. **Extraction (open).** From a relation with the product property,
   extract Freiman bihomomorphisms on dense sets. In dimension one this is
   `section16_extract_uniform_base_family`, which yields Freiman
   8-homomorphisms. In dimension two the analogue is a bilinear
   Balog–Szemerédi–Gowers step. It is the first stage of the U⁴ inverse
   theory, and Milićević's papers carry quasi-polynomial versions. It is
   not formalized here.
2. **Greedy covering (proved, `Proofs16VarietyGreedyCover`).**
   `greedy_variety_cover`: from `MilicevicDeepVarietyStructure D` and a
   Freiman bihomomorphism φ on A₀, cover A₀ up to fewer than θN² points by
   at most exp(B(θ)) **variety pieces**. Here B(θ) =
   `milicevicBound D θ`. A piece is a set G with variety data within
   Milićević's bounds at density θ, and a Freiman bihomomorphism Φ on V(ρ),
   such that q − (s,t) ∈ V(ρ/2) and φ q = Φ(q − (s,t)) for every q ∈ G.
   The recursion stays inside A₀ (`IsEBihomomorphism.mono`), and each step
   removes at least exp(−B(θ))N² points (`exists_variety_piece`). The count
   exp(B(θ)) is quasi-polynomial in 1/θ. Axioms: propext, Classical.choice,
   Quot.sound.
   `greedy_variety_cover_family` handles n bihomomorphisms φ_j on
   domains A_j, which is what step 1 will produce. It uses at most
   n·exp(B(θ/n)) pieces, each tagged with its owner j, and one exceptional
   set U with |U| < θN². Every point of A_j outside U lies in some piece
   owned by j. So if step 1 covers a relation Γ over J by the graphs of φ_j
   on A_j, then Γ over J ∖ U is covered by the pieces' graphs. That is the
   covering half of `StackableStructureAt 2`.
   **Assembled (`Proofs16VarietyStructureSide`, kernel-checked).** Step 1
   is now the precise Prop `BihomExtraction m`, quantified exactly as
   `StackableStructureAt`. Fix γ and θ in (0, 1]. For prime N ≥ N₀, every
   relation Γ ⊆ Z_N² × Z_N with |Γ| ≤ γ⁻²N² and the product property has
   two properties after removing θN² base points:
   - its restriction is covered by the graphs of m(γ,θ) Freiman
     bihomomorphisms on their domains;
   - each value z.2 is the value of some φ_j.

   `variety_structure_side` proves the covering clause of
   `StackableStructureAt 2` from `BihomExtraction m` and
   `MilicevicDeepVarietyStructure D`. After removing θN² base points, Γ is
   covered by K ≤ m·exp(B(θ/(2m))) variety pieces with m = m(γ, θ/2). Each
   piece is read as a partial function on `Point N 2` (via `pairPoint`), in
   `section16FinsetUnion`/`partialGraph` form. If m(γ,θ) is
   quasi-polynomial, so is K. What `StackableStructureAt 2` additionally
   asks is that the class be stackable (step 3).
   **Plausibility audit of `BihomExtraction` (2026-10-08).**
   - Its shape matches the proved dimension-one extraction: all of Γ over J
     is covered, not just a dense part.
   - Covering every value is consistent: on J, Markov bounds the
     multiplicity by γ⁻²/θ, and the product property applies to *every*
     partial function inside Γ, which rules out unstructured "junk" values
     on large sets.
   - Domains that are too sparse for Milićević's theorem go into the
     exceptional set (`greedy_variety_cover_family`).
   - Literature status, from a search only: the passage from additive
     energy to a Freiman bihomomorphism on a dense set is the bilinear
     Balog–Szemerédi–Gowers stage of the U⁴ inverse pipelines. Milićević's
     arXiv:2601.01682 states that its proof uses an abstract BSG theorem.
     See also Gowers–Milićević arXiv:2002.11667 and the F_p^n quasipolynomial
     U⁴ paper arXiv:2410.08966.
   - **Checked (same night) against arXiv:2601.01682 §15**, the proof of
     Theorem 15.1, pp. 103–104. The dense Freiman bihomomorphism there is
     produced without abstract BSG:
     - a single-valued φ on a dense A respects (c/2)^O(1) of the
       horizontal quadruples in many rows;
     - Theorem 2.26 (Sanders's bounds: many respected quadruples give
       agreement with a Freiman homomorphism on a coset progression, on an
       exp(−polylog) fraction) is applied row by row, giving a dense
       horizontally Freiman piece A′;
     - the same is repeated on columns. Domains only shrink and values are
       unchanged, so the horizontal property survives.

     For Gowers's product property, a single-valued selection of a
     relation inherits the property (`RelationProductProperty.mono`, already
     in `Proofs16GreedyRelations`). With p = 1 and θ ≡ 1 on a row of size
     ≥ βN, it has energy ≥ γ⁸β⁴N³, the input Theorem 2.26 needs.
   - **Reduction formalized (`Proofs16BihomPieceReduction`,
     kernel-checked).** `DenseBihomPiece mass` is the single step: a
     sub-relation with the product property and projection ≥ θN² contains
     the graph of a Freiman bihomomorphism on ≥ mass(γ,θ)N² points.
     `bihomExtraction_of_densePiece` derives `BihomExtraction` from it, with
     m = ⌈γ⁻²/mass⌉ + 1. It uses the corpus's peeling
     (`section16_greedy_relation_decomposition`) and pads short families with
     empty pieces (`isEBihomomorphism_empty`).
   - So step 1 is now exactly `DenseBihomPiece`. What remains in it is the
     §15 row/column argument, with Theorem 2.26 as its quasi-polynomial
     input, applied to a selection. Theorem 2.26 is Sanders-strength
     Freiman–Bogolyubov, which the corpus does not contain at quasi-polynomial
     strength.
   - **§15 argument formalized (`Proofs16DenseBihomPiece`,
     kernel-checked).** `densePiece_of_lineExtraction` proves
     `DenseBihomPiece` from `LineFreimanExtraction κ`. That hypothesis is the
     single-line consequence of Theorem 2.26: respected-quadruple energy
     ≥ δN³ on a line set E gives E′ ⊆ E with |E′| ≥ κ(δ)N on which the map is
     Freiman-linear (the agreement set with the Freiman homomorphism on Q).
     The proof:
     - selection of one value per projected point;
     - line energy ≥ γ⁸|E|⁴/N from the product property
       (`line_energy_of_productProperty`, p = 1, unit weights);
     - a generic dense pass (`dense_section_pass`);
     - a row pass, then a column pass on the survivors. The product property
       is hereditary to sub-domains, so column energy survives.

     The mass is κ(δ₂)κ(δ₁)θ/4, with δ₁ = γ⁸(θ/2)⁴ and δ₂ = γ⁸(κ(δ₁)θ/4)⁴.
   - **Chain closed.** `structure_side_of_line_and_milicevic` gives the
     covering half of `StackableStructureAt 2` from exactly two hypotheses:
     `LineFreimanExtraction κ` (Theorem 2.26: Sanders, quasi-polynomial κ)
     and `MilicevicDeepVarietyStructure D`. Both remain unproved hypotheses
     here. The line input is intended to follow from the cited theorem;
     the deep-agreement form is our reformulation, not a quoted statement,
     and its precise derivation is still a separate obligation. With a
     quasi-polynomial κ satisfying the line input, the piece count is
     quasi-polynomial in 1/(γθ).
   - **Theorem 2.26 removed (same night, `Proofs16LineExtractor`).**
     Gowers's product property is stronger than energy: it holds on every
     sub-domain, for every weight, and for p copies at once. A line
     restriction therefore inherits the one-dimensional property, and the
     corpus's own Lemma 16.3 step (`section16_product_restriction`) applies.
     It gives an order-8 Freiman restriction on ≥ α(γ,β)N points, with the
     **polynomial** α = 2⁻²⁰⁰⁰(γβ)¹⁰⁰⁰⁰. So:
     - `lineExtractor_polynomial` is unconditional;
     - `densePiece_polynomial`: `DenseBihomPiece` holds unconditionally, with
       polynomial mass;
     - `structure_side_of_milicevic`: **the covering half of
       `StackableStructureAt 2` rests on `MilicevicDeepVarietyStructure`
       alone**. That is our reformulation of Milićević's construction, not a
       quoted theorem; see the caveat above. The piece count is m·exp(B(θ/(2m))) with polynomial m, so
       it is quasi-polynomial in 1/(γθ) through Milićević's B.

     The dense-piece proof was refactored onto an abstract `LineExtractor`
     (line product property in, Freiman sub-line out). The energy route is
     now the instance `lineExtractor_of_lineFreimanExtraction`, with the
     same mass as before.

   **Remaining for `StackableStructureAt 2`:** Milićević's theorem (a
   hypothesis), and stackability of the variety class (step 3).

   **Adapter to the joint cover: done by the peer.**
   `Proofs16JointVarietyUniform` pads phases (`padFreimanPhases`,
   `bilinearBohrVariety_pad`). `Proofs16VarietyPieceFamilyCover` covers any
   finite family of `IsVarietyPiece` graphs with 9n maps.
   `Proofs16VarietySliceProvider` builds `Section16SliceProvider` from it.
   My parallel `Proofs16VarietyPieceJoint`, which landed two minutes later,
   duplicated the padding and was removed; git history keeps it.

   **Coordination note: the slice-extraction input.** The peer's
   `Proofs16VarietySliceProvider` assumes each sampled final-coordinate
   section lies in the variety-piece class. Covering two-dimensional
   product relations by such pieces, after removing θN² base points, is
   exactly the conclusion of `structure_side_of_milicevic`. Every covering
   piece satisfies `IsVarietyPiece D c` with c = θ/2/m(γ,θ/2), and the
   count is K ≤ m·exp(B). Restricting a piece to a sub-domain stays in the
   class (`IsVarietyPiece.mono`, `Proofs16VarietyGreedyCover`). What remains
   is wiring these into the dimension-three slices, the analogue of
   `Proofs16PartJSlices` for the general provider.
3. **Stacking (open; the peer's lane).** One piece is multiply linear with
   count 9 (`exists_freiman_variety_cover`, then translate). n pieces at
   once need a joint partition, with inverse exponent of degree 16 in n.
   They should feed the polynomial lift's general `Section16SliceProvider`
   controls (J.2 heads-up), not `CubicStackableClass`.

### J.5 Budget check: the variety route against `Theorem162At 3` (2026-10-08)

**Targets.** `Theorem162At 3` asks for `MultiplyLinear γ r` with
r = γ⁻²·multipleS(θ,γ,3) = γ⁻²(2/(θγ))^(2^512). That unfolds to
`MultiplyLinearWith` with, at loss θ′:
- count ≤ multipleQ(θ′/r, γ, 3)^r = (γθ′/r)^(−2^2048·r);
- width exponent ≥ multipleC(θ′/r, γ, 3)^r = (γθ′/r)^(2^2048·r).

So the count may be exp(Θ(r·log r)), and the exponent may be as small as
exp(−Θ(r·log r)), with r polynomial in 1/(θγ) of degree 2^512.

**What the structure side produces (J.4, all kernel-checked except the
Milićević hypothesis).**
- One-step mass. α(γ,β) = 2⁻²⁰⁰⁰(γβ)¹⁰⁰⁰⁰ is nested twice:
  `densePieceMassGen` ≈ α(γ, α(γ,θ/2)θ/4)·α(γ,θ/2)θ/4 ≈ (γθ)^(10⁸+O(10⁴)),
  up to 2^(−O(10⁷)) constants.
- Family size m ≈ γ⁻²/mass, so polynomial in 1/(γθ) of degree ≈ 10⁸.
- Pieces: K ≤ m·exp(B), with B = milicevicBound D (θ/(2m)) =
  (2 + 2 log(2m/θ))^D ≈ (2·10⁸·log(1/(γθ)))^D.
- Stacking n pieces (peer's joint cover): count 9n. The capped exponent is
  ≥ 1/(1024p²(4C+18)(B+2)^17) per piece, and joint covers give
  degree ≈ 17 in n·B (`Proofs16FreimanVarietyCapBound`).

**Comparison.**
- *Exponents:* 1/poly(n·B) is quasi-polynomial in 1/(γθ), far above the
  allowed exp(−Θ(r log r)).
- *Counts:* m·exp(B) = exp(O(log(1/(γθ)))^D). This sits below
  exp(Θ(r log r)) for all γθ ∈ (0,1] **provided Milićević's unspecified
  exponent D is not astronomically large**. Since
  (log y)^D ≤ (D/e)^D·y, it suffices that
  (D/e)^D·(2·10⁸)^D ≲ 2^(2^512). An explicit upper bound on D, and explicit comparisons for the
  recurrence constants C and p, are still needed to turn this heuristic
  into the printed numerical budget; O(1) alone provides no such bound.
- The lift's own losses come in on top: samples ≈ poly(1/σ), counts
  C(samples, 2)·Pb², and the threshold. In the peer's polynomial lift they
  are polynomial in the slice controls, so they do not change the
  comparison's shape.

**Caveat.** This is an order-of-magnitude comparison, not a formal
inequality. The formal obstacle stays the interface: Part J's
`CubicStackableClass` (degree-4 controls) and `PolyBoundedControl`
(polynomial bounds) are stricter than the catalogue's own `Theorem162At 3`
budget. A Part J restated with the polynomial lift's general slice
controls, plus quasi-polynomial counts, is what the variety route can feed.

**Which lift (checked same night).** It has to be the peer's polynomial
lift, not Gowers's. Gowers's lift costs a factor 576^(−24n) in the exponent
(J.3). With quasi-polynomial n = exp(L^D), where L = log(1/(γθ)), that
factor is exp(−Θ(exp(L^D))). The budget allows exp(−Θ(r log r)) with
log r ≈ 2^512·L. Once L^(D−1) > 2^512, exp(L^D) beats r, so Gowers's lift
breaks the budget for extremely small γθ. Polynomial n is exactly what
`PolyBoundedControl` encodes. The Part J chain (`Proofs16PartJ*`) is
OAI-free and builds locally, but it is wired to Gowers's lift. The
restatement on the polynomial lift imports OAI through
`Proofs05SchmidtRecurrence`, so it belongs on the full-verification host.

### J.6 Formalizing Milićević's pipeline from the leaves (2026-10-08)

The variety route now rests on `MilicevicDeepVarietyStructure` alone. That
hypothesis is a reformulation of arXiv:2601.01682's construction (J.2), so
the following dependency map describes one route to discharging it.
The work starts with
the elementary lemmas of its §2:
- **Lemma 2.5, done (`Proofs16BohrDenseDifference`, kernel-checked).**
  `bohr_dense_sub_cover`: if 4^(k+1)·|B(Γ;ρ) ∖ A| ≤ |B(Γ;ρ)| with k = |Γ|,
  then every d ∈ B(Γ;ρ/2) is a difference of two elements of A. The proof
  counts with `bohr_card_le_four_pow`. Helpers: `bohr_add_half`,
  `zero_mem_bohr`.
- Already in the corpus: Lemma 2.4-type bounds (`bohr_card_lower`,
  `bohr_card_le_four_pow`), regular radii (`bohr_exists_regular_step`), and
  Freiman-linearity in coordinates, equation (9)
  (`freiman_linear_gap_affine`).
- **Lemmas 2.7/2.8, done in ℤ/N form (`Proofs16BohrAnnulus`,
  kernel-checked).** Milićević perturbs radii only because of characters
  with a small image. In ℤ/N with N prime, every nonzero frequency is a
  bijection, and the zero frequency never leaves the band around 0. So no
  perturbation is needed. `bohr_annulus_card_le` proves
  |B(K;ρ+η) ∖ B(K;ρ−η)| ≤ |K|·(4ηN + 2) for 0 ≤ ρ − η, and
  `band_card_le` counts residues with centered value in (a, b].
  Weak regularity therefore holds at every radius, with ε = |K|(4η + 2/N).
- **Lemma 2.6, done deterministically (`Proofs16SeparatingFrequencies`,
  kernel-checked).** In ℤ/N with N ≥ 7 prime and d ≠ 0, at most
  2⌊N/5⌋ + 1 ≤ N/2 frequencies leave γd within N/5 of zero
  (`small_multiples_card_le`). Double counting gives one frequency that
  separates half of any set of nonzero differences
  (`exists_halving_frequency`). Hence |D| < 2^m differences are separated
  by m frequencies (`separating_frequencies`). For D = (S − S) ∖ {0} that
  is 2⌈log₂|S|⌉ frequencies, matching the paper's O(log k).
- **Bilinear Bogolyubov, step 1 (row Bogolyubov), done with polynomial
  bounds (`Proofs16BilinearBogolyubovRows`, kernel-checked).**
  - `bogolyubov_classical` is a new public wrapper appended to
    `Proofs07BohrHom`, extracted from Gowers's Lemma 7.8 proof: density α
    gives a spectrum K with |K| ≤ 16α⁻² and B(K; 1/(8π)) ⊆ 2A − 2A.
  - `horDiff`/`verDiff`/`rowOf` define the directional difference sets.
  - `row_bogolyubov`: every nonempty row of D_hor D_hor A contains such a
    Bohr set.

  This is OAI-free. The quasi-polynomial alternative is the port's
  `exists_quartic_bogolyubov`.
- **A polynomial Theorem 17 analogue is already in the corpus.**
  Gowers's Corollary 7.6 (`corollary_7_6_holds`) turns γ(αN)³ respected
  quadruples into a Freiman 8-homomorphism on ≥ 2⁻¹⁸⁸²γ¹¹⁶⁴αN points.
  Lemma 7.8 then extends such maps from dense sets to Bohr sets. Together
  they are the ℤ/N polynomial-bound form of [49] Theorem 17, the engine of
  Lemma 19. As a first use, `lineFreimanExtraction_holds`
  (`Proofs16LineFreimanUnconditional`, kernel-checked) proves
  `LineFreimanExtraction` with κ(δ) = 2⁻¹⁸⁸²δ¹¹⁶⁴. The identity
  `energy_eq_phiAdditiveCount` matches the two energy notions. So the
  energy route `densePiece_energy_unconditional` is unconditional too.
- **Selection averaging, done (`Proofs16SelectionAveraging`,
  kernel-checked).** `exists_good_selection`: if every requirement fixes
  at most 4 points to allowed values, some selection f ∈ Π U_y meets
  ≥ |T|/K⁴ of them. The proof double counts over `Fintype.piFinset U`.
  The selections meeting one requirement form the product with the fixed
  coordinates replaced by singletons (`card_meeting`), so they number
  ≥ K^(−4)·Π|U_y| (`card_all_le_mul_meeting`). This replaces [49]'s
  random choice.
- **[49] Lemma 19 in ℤ/N, done with polynomial bounds
  (`Proofs16Lemma19Selection`, kernel-checked).**
  `lemma19_selection_piece`: prescribed additive values on |T| quadruples,
  with |T| ≥ δN³·256K⁴, each in the "new" sets W(q i) ⊆ U(q i) with
  |U| ≤ K. Then some selection f(y) ∈ U_y is Freiman-linear on a set E′
  of size ≥ 2⁻¹⁸⁸²δ¹¹⁶⁴N, on which f(y) ∈ W_y. Each quadruple becomes a
  requirement on its image (`quadRequirement`), with at most 256
  preimages per requirement. After that come `exists_good_selection` and
  `lineFreimanExtraction_holds`. This replaces [49]'s random choice and
  Theorem 17 (Sanders).
- **Correction to the Lemma 19 shape (same night).** In [49]'s proof the
  witnesses force only **two** of a quadruple's four points into
  A′ = {f(y) ∈ U_y ∖ ℒ_y(y)}. Quadruples entirely inside A′ come from
  Cauchy–Schwarz. `lemma19_selection_piece` assumes all four points are
  new, which is stronger than [49] provides. The Cauchy–Schwarz step is now
  formalized (`Proofs16PairEnergyCS`, kernel-checked). Group pairs by the
  key (a − c, f a − f c); then `two_new_points_energy` gives
  pairEnergy(all, A′×A′)² ≤ N³·phiAdditiveCount(A′, f), via
  `pairEnergy_sq_le` (Cauchy–Schwarz), `pairEnergy_univ_le` (≤ N³), and
  `pairEnergy_self_eq_phiAdditiveCount`.
- **[49] Lemma 19 in its original shape, done
  (`Proofs16Lemma19TwoNew`, kernel-checked).** `lemma19_two_new_piece`:
  witnesses q with q₀ − q₂ = q₁ − q₃ and matching value differences, all
  values in U, new values (∈ W) only at q₁ and q₃, with
  |T| ≥ δN³·256K⁴. Then a selection f is Freiman-linear on a set E′ of
  size ≥ 2⁻¹⁸⁸²(δ²)¹¹⁶⁴N with f(y) ∈ W_y there. The chain is
  selection averaging, then matched pairs-of-pairs, then
  `two_new_points_energy`, then Corollary 7.6. It supersedes the
  four-new-points `lemma19_selection_piece`, which stays as a true but
  weaker statement.
- **Open subtlety before Corollary 20: the "WLOG" in [49] Lemma 19.** A
  failing triple (y,z,w) has witnesses a ∈ U_{y+z}, b ∈ U_z, c ∈ U_{y+w},
  d ∈ U_w with a − b = c − d. Since 0 ∈ every ℒ-family, one of a, b is new
  and one of c, d is new. That leaves four cases: (a,c), (a,d), (b,c),
  (b,d). [49] (as summarized from the ar5iv text) takes (b,d) "without
  loss of generality".
  - (a,c) ↔ (b,d) by swapping the roles of the two pairs.
  - The failing set is closed under (y,z,w) ↦ (−y, y+z, y+w), which
    exchanges (a,b) and (c,d). That maps (a,d) ↔ (b,c).
  - So the mixed cases (a,d) and (b,c) are not reduced to (b,d) by these
    symmetries. In them each Cauchy–Schwarz pair (key a − b = c − d)
    carries exactly one new point, and `two_new_points_energy` does not
    apply directly. Either a second Cauchy–Schwarz round is needed, or
    there is a different grouping.
  Check this against [49]'s full text (the WebFetch summaries cover only
  its first 100k characters) before formalizing Corollary 20.
  **Resolved (same night): the mixed cases need two Cauchy–Schwarz rounds.**
  `one_new_each_energy` (`Proofs16PairEnergyCS`, kernel-checked) treats the
  case where the first pair has its new point first and the second pair
  has it second. Then X² ≤ E(S₁,S₁)·E(S₂,S₂). Regrouping
  ((u,v),(u′,v′)) ↦ ((v,v′),(u,u′)) (`pairEnergy_regroup`) and symmetry
  (`pairEnergy_comm`) turn both factors into pairEnergy(all, A′×A′), whose
  square is ≤ N³·E(A′). So X² ≤ N³·E(A′), the same bound as the (b,d)
  case. All four cases are covered.
  `lemma19_mixed_piece` (`Proofs16Lemma19TwoNew`, kernel-checked) is
  Lemma 19 for the mixed cases: key relation q₀ − q₁ = q₂ − q₃, with new
  points at q₀ and q₃. Cases (b,d) and (a,c) regroup to
  `lemma19_two_new_piece`, and cases (a,d) and (b,c) to
  `lemma19_mixed_piece`. Every case of [49]'s Lemma 19 is now proved in
  ℤ/N with polynomial bounds.
- **[49] Corollary 20, one step, done (`Proofs16Corollary20Step`,
  kernel-checked).** A family (E_i, L_i) covers
  cov(x) = {0} ∪ {L_i x ∈ U_x : x ∈ E_i}. A distinct-point triple is bad
  if a witness a − b = c − d escapes (cov − cov) + (cov − cov).
  `corollary20_step`: if at least εN³ triples are bad, there is a new
  Freiman-linear piece (E′, f) with f(x) ∈ U_x ∖ cov(x) on E′ and
  |E′| ≥ κ(ε,K)N, where κ = 2⁻¹⁸⁸²((ε/(1024K⁴))²)¹¹⁶⁴. The proof:
  - one of each witness pair is new, since 0 ∈ cov (`bad_witness_new`);
  - pigeonhole over the four cases;
  - per-case encodings with explicit decoders;
  - the matching Lemma 19 (`case_two_new`, `case_mixed`).

  Distinct points make witness values consistent. Non-distinct triples
  number O(N²) and are excluded from the count.
- **[49] Corollary 20 in ℤ/N, done (`Proofs16Corollary20`,
  kernel-checked).** `corollary20`: after at most ⌊K/κ⌋ + 1 Freiman pieces
  (E_i, L_i), fewer than εN³ distinct triples are bad. The potential
  Σ_x |cov(x)| starts at N (`covPotential_empty`), is ≤ K·N
  (`covPotential_le`, since cov ⊆ U), and grows by ≥ |E′| ≥ κN per step
  (`potential_snoc`). **Step 2 of the bilinear Bogolyubov argument is
  complete** in ℤ/N, with polynomial bounds and maps on sub-domains rather
  than coset progressions.
- Remaining for Theorem 1.6: step 3, the columns. It needs Bogolyubov on
  the good index set, [49]'s algebraic regularity (Theorem 4), bipartite
  quasirandomness (App. B), and the lattice theorems (Theorems 5 and 6).
  Then comes the composition into the seven-fold difference set.
- **[49] Section 7 (Theorem 35), read from offset 100k.** The proof:
  1. Row Bogolyubov on dense rows Y¹ gives A¹ = D_hor D_hor A, whose rows
     contain B(Γ_y, ρ). **Done:** `row_bogolyubov`.
  2. A² = D_ver A¹ has fibre ⊇ ∪_z B(Γ_{y+z}) ∩ B(Γ_z). **Done:**
     `verDiff_rowBohr_intersection`, with `mem_verDiff`.
  3. A³ = D_hor A². By Theorem 27, a sum of Bohr sets contains
     B(⟨Γ⟩_R ∩ ⟨Γ′⟩_R; 1/4); this is lattice theory. Corollary 20 is then
     applied with U_y = ⟨Γ_y⟩_R, giving the L_i. Theorem 31 (bounded spans)
     and the Hosseini–Lovett averaging over index sets J₁…J₄ avoid
     exponential counts (Claim 36). Proposition 18 (density in a coset
     progression) and re-centering make the maps Freiman-linear on
     2C − 2C (Claim 37).
  4. A⁴ = D_ver D_ver A³. This uses algebraic regularity (Theorem 33,
     stated in the fetch) to partition C into pieces with quasirandom
     fibres, robust Bogolyubov (Corollary 16) on Y′, and quasirandomness
     (Claim 38).

  The seventh operator and the final containment fall in the part the
  fetch truncated.
- **Theorem 27, Fourier half, done (`Proofs16BohrSpectrum`,
  kernel-checked).** `bohr_fourier_annihilation`: for b ∈ B(K;ρ′),
  |1̂_B(ξ)|·|1 − e(−bξ)| ≤ 2|K|(4ρ′N + 2), with B = B(K;ρ). It rests on
  `fourier_translate`, then `bohr_escape_card_le` (escaping points lie in
  the annulus), then `bohr_annulus_card_le`. A large coefficient at ξ
  therefore forces e(bξ) ≈ 1 on the whole smaller Bohr set. What remains
  of Theorem 27 is the duality: e(bξ) ≈ 1 on B(K;ρ′) implies
  ξ ∈ ⟨K⟩_R. That is geometry of numbers.
- **Correction: the span duality is Fourier, not geometry of numbers.**
  [49]'s Proposition 26: if B(γ;ρ) is weakly regular,
  |B(ρ+η) ∖ B(ρ)| ≤ (ε/2)|G|, and |B̂(χ)| ≥ ε, then χ = Σ aᵢγᵢ with
  |aᵢ| ≤ K = O(k/(εη)). That is polynomial. The proof sandwiches 1_B
  between products of trapezoids, truncates their Fourier series
  (coefficients decay like 1/ξ²), and expands the product. Weak
  regularity follows from `bohr_annulus_card_le` when the inner radius
  is nonnegative and `|K|*(4*eta*N+2) <= (epsilon/2)*N`. The finite-size
  term `2*|K|` must be retained; the statement is not uniform over
  arbitrarily small epsilon at a fixed modulus.
  Formalization on ℤ/N, discretely:
  - **brick 1 done** (`Proofs16DirichletBound`, kernel-checked):
    `interval_exponential_sum_le` (interval sums ≤ N/(2|ξ|)). It reuses
    the corpus's `four_centeredAbs_div_le_phase_norm`
    (`Proofs05PhaseMetric`, |e(ξ) − 1| ≥ 4|ξ|/N);
  - **brick A done** (`Proofs16Trapezoid`, kernel-checked): with
    I_a = `centeredBall N a`, the trapezoid g = |{s ∈ I_a : |t−s| ≤ c}|/|I_c|
    is 1 for |t| + c ≤ a, 0 for |t| > a + c, and lies in [0,1]. So
    Π_{γ∈K} g(γx) equals 1 on B(K;(a−c)/N), vanishes off B(K;(a+c)/N),
    and lies in [0,1] (`trapezoid_product_sandwich`);
  - **brick B done** (`Proofs16TrapezoidFourier`, kernel-checked):
    `centeredBall_eq_image` (the ball is a progression when 2a < N),
    `fourier_centeredBall_le` (|Î_a(ξ)| ≤ N/(2|ξ|)), `fourier_trapezoid`
    (ĝ = Î_a·Î_c/|I_c|), and `fourier_trapezoid_le`
    (|ĝ(ξ)| ≤ (N/(2|ξ|))²/|I_c|);
  - **bricks C, D done** (`Proofs16TrapezoidTruncation`,
    kernel-checked): `fourier_inversion`, `inv_sq_tail_le`
    (Σ_{M<m≤U} 1/m² ≤ 1/M), `centeredAbs_fibre_card_le` (≤ 2 residues
    per centered value), and `residue_inv_sq_tail_le`
    (Σ_{|ξ|>M} 1/|ξ|² ≤ 2/M);
  - next: the telescoping product bound and the expansion into bounded
    spans (bricks E, F).
- **Open dependencies for step 3:** Theorem 27 (Bohr-set sums vs span
  intersections, needing lattices or duality), Theorem 31, Proposition 18,
  Theorem 33 (algebraic regularity), Corollary 16 (robust
  Bogolyubov–Ruzsa), and bipartite quasirandomness. Each is a substantial
  formalization. In ℤ/N with polynomial bounds some may simplify: in a
  prime field a span ⟨Γ⟩_R is a generalized arithmetic progression, and
  Bohr sets are close to the dual of a lattice.

- Next: [49] Corollary 20, iterating Lemma 19 from the zero map, and
  extending pieces to Bohr sets with Lemma 7.8. In [49] the L_i live on
  coset progressions; in ℤ/N with polynomial bounds, Bohr sets via
  Lemma 7.8 are the natural domains.

**Dependency map for Theorem 1.6** (Milićević, arXiv:2109.03093 [49]; read
2026-10-08 from the ar5iv text, Sections 1–6 only). Sections:
2 Coset progressions and Freiman homomorphisms; 3 Variants of Freiman's
theorem; 4 Bohr sets; 5 Quantitative fundamental theorem of lattices;
6 Quasirandomness of bilinear Bohr varieties; 7 the argument;
App. A robust Bogolyubov–Ruzsa; App. B quasirandom bipartite graphs.
- Step 1, row Bogolyubov: a quasi-polynomial one-dimensional Bogolyubov.
  **Available in the OAI port:** `exists_quartic_bogolyubov`
  (`LocalizedSiftingAlmostPeriods.lean`), with rank ≤ 1 + C(p+1)⁴ and
  radius ≥ e^(−C(p+1)) inside 2A − 2A at density e^(−p).
- Step 2, the Freiman-linear maps L_i: a random selection f(y) ∈ U_y,
  averaging, then Theorem 17 (quadruple-respecting map → Freiman
  homomorphism on a proper coset progression, via BSG and
  Plünnecke–Ruzsa), iterated up to exp(log^O(1)) times (Lemma 19,
  Corollary 20). Theorem 17 is Theorem 2.26 of the U⁴ paper.
- Step 3, columns: Bogolyubov on Y′, then the algebraic regularity lemma
  (Theorem 4), bipartite quasirandomness (App. B), and the lattice theorems
  (Theorems 5 and 6), which replace (U ∩ V)^⊥ = U^⊥ + V^⊥.
- Difference-operator order: D_hor D_ver D_ver D_hor D_ver D_hor D_hor A.

Scale: Theorem 1.6 alone is a substantial formalization project. It is
only the first of Theorem 1.4's ingredients (§§5–13 of the U⁴ paper add
abstract BSG, the extension theory, and §11's Freiman-bilinear step).
Discharging `MilicevicDeepVarietyStructure` requires these remaining
structure arguments. A weaker-bound route using classical Bogolyubov or
Gowers's Freiman lemma in `Proofs07BohrHom` may be useful, but fitting its
constants into Theorem 16.2's printed budget requires a separate proof.

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
updated facade audit passes.
The same module also proves `exists_mixed_modular_recurrence_bound`.
For fixed maximum degree `k`, constants `K,p` give a common
`1 <= q <= H^(p*(d+1)^(2*k))` making every monomial in `d` families and
degrees `1,...,k` smaller than `N/H`, provided `H >= K*(d+1)`.
The induction first makes the highest degree sufficiently small to survive
a bounded multiplier chosen for all lower degrees. Its exponent estimate
is checked in `schmidt_mixed_exponent_bound`. This strengthens the available
recurrence input. The box-partition construction is now proved below.
**Minimum cell length now proved in one dimension.**
`Proofs05MinimumPolynomialPartition.exists_minimum_polynomial_partition_bound`
strengthens the polynomial partition: for constants `K >= 2`, `p > 0`,
the same form of size condition `N >= H^(p*(d+1)^(2*k))` yields a partition
with **every** cell length at least `H`, and error at most `k/H` modulo
integers on each cell. The induction uses the already ported
`comparableResidueProgressions`: its outer blocks have lengths in `[T,2*T)`.
Degree reduction at scale `2*T` and induction on each actual block length
avoid truncating children and creating short tails. The extra factor of two
only changes the degree-dependent constant `p`, not the exponent `2*k` in
family size. The production module passed an isolated Lean check; the full
facade audit passes. Its adapted proof carries separate Apache-2.0
licensing and provenance in the adjacent `LICENSE.openai-math`.

`Proofs05MinimumModularPartition.exists_minimum_polynomialOn_partition`
now transfers this to the catalogue's modular polynomial encoding. It gives
the same minimum index-cell length and bounds the centered distance between
any two values in a cell by `(2*k/H)*N`, simultaneously for the whole family.
An integer lift of `PolynomialOn` and cancellation of the cell constant
supply the bridge; no prime-modulus assumption is used. The production
module passed Lean. The partition is still of the integer index interval;
proper modular progression transport is a further obligation.

**Simultaneous geometric height step proved.**
`Proofs05SimultaneousMultiaffineStep.simultaneous_multiaffine_box_height_step`
now generalizes the existing geometric step to a family of `q` phases.
One common coarse partition separates the same maximal square-free monomial
from all phases, and a simultaneous lower-height partition is transported
and flattened. Properness, minimum widths, and each phase's diameter bound
are preserved. The production module passed Lean. The recurrence estimate,
scale budget, and simultaneous child theorem remain explicit premises.

This allows the checked Schmidt recurrence to replace the one-coefficient
recurrence in the height induction. The number of monomial-removal stages
is bounded by `2^k`, independently of family size.
`exists_uniform_modular_monomial_recurrence` now supplies one pair of Schmidt
constants for all degrees from 1 through `k`, retaining the quadratic
family-size exponent. The multiplier may depend on the selected degree;
this is sufficient when removing one common maximal monomial. The production
module passed Lean.

**Polynomial family-size box bound now proved.**
`Proofs05SimultaneousMultiaffinePartition` discharges the scale and exponent
induction. For a downward-closed family of `h` monomials, constants `K,p`
give one proper box partition with minimum width `H` and each phase's
modular diameter at most `h*N/H`, provided `H >= K*(q+1)` and the input
width is at least `H^(p*(q+1)^(2*h))`. Removing one common maximal monomial
increases the family-size exponent by two; taking `h = 2^k` treats all
multilinear phases in dimension `k`. Rounded coarse widths are `T` or
`T+1`, so every lower-height input meets its threshold.

`Proofs16SimultaneousRecurrence.exists_simultaneous_commonDiff_partition_two_bound`
then performs the lift and slice from Lemma 16.1. For every dimension `k`
there are `K >= 2`, `p > 0`, independent of family size `q`, such that

```
H >= K*(q+1),  width(P) >= H^(p*(q+1)^(2^(k+2)))
```

give a common proper box partition with **every width at least `H`** and
`centeredAbs(mu_i(x)*cell.commonDiff) <= 2*N/H` at every point of every
cell. Rescaling by `2^k` and increasing `p` absorb the diameter coefficient.
Both production modules and the combined facade axiom audit pass.

This supplies polynomial dependence on `q` in the input-width exponent
in the stated large-width regime. It does not give explicit dimension
constants or a pointwise improvement of every previous threshold. The
root-width form is now proved in
`Proofs16PolynomialRecurrenceProfile.exists_polynomial_section16_recurrence_profile`.
For integer constants `K >= 2`, `p > 0`, set

```
epsilon(q) = 1 / (2*p*(q+1)^(2^(k+2)))
threshold(q) = (K*(q+1))^(2*p*(q+1)^(2^(k+2))).
```

For `threshold(q) <= m <= width(P)`, the partition has every width at least
`m^epsilon(q)` and common-difference error at most `2*m^(-epsilon(q))*N`.
The proof takes the ceiling of the real root; doubling the exponent
denominator covers its cost without losing the target width. The production
module and its transitive axiom check pass, with only `propext`,
`Classical.choice`, and `Quot.sound`.

**Eventual improvement under the old threshold is proved.**
`Proofs16PolynomialRecurrenceComparison` proves, for every fixed dimension
and choice of positive exponent constant, that the new reciprocal-polynomial
exponent is eventually strictly larger than `section16RecurrenceExponent`.
It also proves that the new integer threshold is eventually no larger than
`section16WidthThreshold`. The helper is the elementary asymptotic statement
`A*(q+1)^d < b^q` for all sufficiently large `q` when `b >= 2`.

`exists_eventually_stronger_section16_recurrence` combines these comparisons
with the construction: for every dimension there are integer constants
`K,p,q0` such that **under the old width threshold**, every family size
`q >= q0` has a common proper partition satisfying the new, strictly larger
width exponent and the corresponding smaller error exponent. The production
module and the follow-up full facade axiom audit pass. The crossover `q0` and dimension constants remain
existential, so this does not supply numerical improvements for small `q`.

**The improved exponent now reaches retiled linearity.**
`Proofs16PolynomialRetiledLinearity` passes a direct production-source Lean
check. Its `Section16RetiledLinearityBound` keeps frequency coverage,
local Bohr linearity, and the compatible-axis hypotheses explicit. The
new recurrence yields proper product cells of minimum width
`(zeta/2)*sqrt(m^epsilon(q))`, with a linear final-coordinate restriction
on every good base point. The generic tiling theorem accepts a supplied
recurrence partition, so the existing recurrence API is preserved.
`exists_eventually_stronger_retiled_linearity` gives this conclusion under
the old integer threshold for all sufficiently large `q`, with a strictly
larger exponent. Integer rounding and the length-minus-one margin are
included. The combined facade audit passes.

`Proofs16PolynomialProductAssembly` also passes Lean. It applies this
profile to a `MultiplyLinearWith Qb Eb` spectrum cover on short parent
boxes. For positive integer `n <= (m/8)^(Eb sigma)` above the new threshold
at `floor(Qb sigma)`, it obtains one proper product partition of minimum
width `(zeta/2)*sqrt(n^epsilon(q))`, where the actual cover count satisfies
`q <= Qb sigma`. The good base set retains at least `1-sigma` of the mass.
Monotonicity in the family size justifies testing the threshold at the
known count bound. This makes the recurrence usable in the localized
spectrum assembly; the threshold, spectrum structure, and local Bohr
linearity remain explicit. The combined facade audit passes.

`Proofs16PolynomialUniformWidth` proves antitonicity of the recurrence
exponent and resulting product width in the phase-family size, including
the zero-width case. Its uniform spectrum assembly has minimum width
`(zeta/2)*sqrt(n^epsilon(floor(Qb sigma)))`, so the bound depends only on
the supplied spectrum controls and can be shared across further partition
refinements. The production source and all three transitive axiom checks
pass. Its facade import passes the combined audit.

`Proofs16PolynomialLemma6.exists_polynomial_lemma_16_6` specializes the
uniform assembly to the exact induced-function inputs used by Lemma 16.6.
For `m >= 4` and a positive localized scale `n` below `(m/8)^(Eb sigma)`
and above the recurrence threshold, it gives proper product cells with
the uniform polynomial width bound and linear induced restrictions on
the good base set. Spectrum coverage and the induced selection are still
premises. Its production source and transitive axiom check pass; the
facade import passes the combined audit.

`Proofs16PolynomialLemma9.exists_polynomial_lemma_16_9` carries the
improved width through the remainder-cover and line-cover assembly. If
`w = m^((multipleC(sigma/(2*r),gamma,k+1))^r)` is at least four and a
positive integer `n <= (w/8)^(Eb(sigma/2))` meets the polynomial recurrence
threshold at `floor(Qb(sigma/2))`, every remainder cell admits the improved
Lemma 16.6 construction. Flattening retains one common width
`(zeta/2)*sqrt(n^epsilon(floor(Qb(sigma/2))))`, the original remainder
graph-count bound, and good mass at least `1-sigma`. The production source
passes Lean. Spectrum structure, induced selection, and the remainder
cover are explicit premises; the combined facade audit passes.

**An all-scale Lemma 16.6 bound is now proved.**
`Proofs16PolynomialAllScaleParameters` absorbs the recurrence threshold
by setting `x=m^(a/(4*E))`, rounding `H=ceil(x)`, and taking `n=H^(2*E)`.
If `(zeta/(4*b))*x > 1`, then `x > 16`, so this integer scale lies between
`b^E` and `(m/8)^a` and its retiled width dominates the target. Here
`b=C*(q+1)` and `E=2*p*(q+1)^(2^(k+2))`.

`Proofs16PolynomialAllScaleLemma6` combines that arithmetic with the
large-scale theorem and singleton partitions. For `0<a=Eb(sigma)<=1`,
it yields minimum width `(zeta/(4*b))*m^(a/(4*E))` for **every input
width**, without an additional threshold premise. The prefactor and
reciprocal exponent have polynomial dependence on the spectrum-count
bound `q=floor(Qb(sigma))`. The production sources and the combined facade audit pass. Spectrum
structure and induced selection remain
explicit inputs.

`Proofs16PolynomialAllScaleLemma9` then transfers that width through the
remainder cover for every input scale. With
`c=(multipleC(sigma/(2*r),gamma,k+1))^r` and `a=Eb(sigma/2)`, its line-cover
width is `(zeta/(4*b))*m^(c*a/(4*E))`, where `q=floor(Qb(sigma/2))`.
The original remainder graph-count and good-mass conclusions are retained.
A separate monotonicity lemma transfers the power lower bound on remainder
cell widths. The complete production source and the follow-up combined
facade audit pass. No localized threshold remains in
this result's hypotheses, but spectrum structure, induced selection, and
the remainder cover remain premises.

The remaining work is integration into the higher-dimensional lift and
its structure hypotheses, together with explicit dimension constants where
the printed thresholds require them. The printed final all-length threshold
does not follow from this recurrence theorem alone.

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

*Scope (added 2026-10-09).* Both bullets compare at the single density
δ = 1/2, which is all Corollary 18.7 needs. Theorem 18.2 at length six
must hold for every δ ≤ 1/2, with α = `intervalUniformityParameter δ 6`
= (δ⁶/(512·216))^32, so log(1/α) = 192·log(1/δ) + 32·log(110592).
- The route's log₂log₂ threshold is about 1/c(α). The allowed one,
  `szemerediThreshold δ 6`, has log₂log₂ = δ^(−M) = exp(M·log(1/δ)).
- **Polynomial** c = α^D needs D·log(1/α) ≲ M·log(1/δ). The ratio
  log(1/α)/log(1/δ) is largest at δ = 1/2, where it is about 728. So the
  half-density bound D ≲ M/728 already covers every δ.
- **Quasi-polynomial** c gives 1/c = exp(C·(192·log(1/δ))^A). For A > 1
  this exceeds exp(M·log(1/δ)) once log(1/δ)^(A−1) ≳ M/(C·192^A), so it
  fails for small δ.

So Theorem 18.2 at length six needs a dense trilinear piece of density
*polynomial* in α. Quasi-polynomial densities suffice only for the
half-density corollary.

**Correction (same day).** An earlier version of this paragraph proposed
Milićević's 2026 theorem as that input. It is not. That theorem
(arXiv:2601.01682) is a quasi-polynomial **U⁴** inverse theorem, built on a
structure result for two-variable Freiman **bi**homomorphisms. Two
variables correspond to degree 3, i.e. five-term progressions, which are
already proved here (`theorem_18_2_le_five`). Six-term progressions need
the trilinear case, and no quasi-polynomial bound is known for it
(Gowers–Milićević 2020: iterated exponential).

The original lift used in the gap calculation loses exponentially in
the graph count (Part B). That calculation does not apply unchanged to
the subsequently proved polynomial recurrence route. Its new all-scale
line exponent eventually improves the old exponent, and the improvement
now propagates through actual two-dimensional graph pieces and relation
decomposition. The dimension constants remain existential, so this does
not yet certify the printed six-term threshold.

**Corollary 18.7 at k = 6 and the all-k statements remain open in this
development.** The existing gap theorems rule out the encoded earlier
parameter choices; they do not prove that every alternative route needs
a particular external inverse theorem.

## L. Where the gap in Gowers's proof stands (synthesis, 2026-10-10)

The user's priority is Gowers's proof, not any particular source. This
section collects what every examined route needs.

- **The printed defect.** Lemma 16.10's anchor lift: `r = ⌈qσ⁻²⌉` anchors
  with `σ = ρ/4`, and unions over `r²` anchor pairs, give the parameter
  `p = 4r²γ⁻²s`. The comparison `q(σ/p, γ, k+1)^p ≤ q(ρ, γ, k+1)` fails
  because `p` grows with `1/ρ` (A). Behind it lies the union rule of
  multiply-linear sets, which costs exponentially in the number of pieces
  (B).
- **Slope relations do not avoid it (checked today).** The slope relation
  `h ↦ λ_t(h)` does inherit the product property, at parameter `γ²`, from
  pairs of `φ₁`-restrictions on linear classes. But covering all but `ρ` of
  a fibre needs `poly(1/ρ)` classes (already at `k = 1`). So the
  relation's fibre size, and with it `γ′` and `s(θ, γ′, k)`, depend on `ρ`.
  Lemma 16.8 then turns this into `exp(poly(1/ρ))`. Any exact repair needs
  a *stackable* invariant (H.4).
- **The common core.** Every route needs an inverse theorem for Freiman
  multi-homomorphisms over `ℤ/N` with good bounds.
  - Dimension 2 (degree 3, five-term APs): already sufficient here, since
    18.2 and 18.7 are proved for `k ≤ 5`. Milićević 2026 would give the
    deep form, but its Proposition 9.3 has the coherence gap (J.5c).
  - Dimension 3 (six-term APs, the first open case of 18.2 and 18.7): needs
    a dense trilinear piece of density polynomial in `α` (or
    quasi-polynomial for 18.7 only); see K.4. No such bound is known;
    Gowers–Milićević 2020 is iterated-exponential.
- **Explicit-constant alternatives.** None exist.
  - The openai/math port reduces 18.2 and 18.7 to a dense Szemerédi
    theorem at Gowers's tower scale (`PORT_CONSTANTS_SURVEY.md`).
  - Leng–Sah–Sawhney's exponent `c_k` is only shown to exist.
  - Gowers's 2001 bound is the only explicit one in the literature.
- **Consequence.** Closing the open entries for `k ≥ 6` by any known means
  needs a new multilinear inverse theorem: a structure theorem for
  three-variable frequency functions with at most quasi-polynomial loss
  in `ℤ/N`. For Theorem 16.2 in every dimension the same is needed in
  every dimension. That is an open research problem, not a formalization
  task. The Milićević Step 5 work (J.5c) bears on `Theorem162At 3` through
  the dimension-two deep structure, but by K.4 it does not reach
  Corollary 18.7 at `k = 6`.
- **The direct trilinear attack (analysed the same day).**
  - *Target.* `theorem_18_2_of_function_discrepancy_budget` reduces
    length 6 to a degree-4 `FunctionDiscrepancyBound`. Its `β` must be
    `≥ α^D` with `D ≲ 2^32768/728` for 18.2, or quasi-polynomial with
    exponent `A ≲ 3400` for 18.7.
  - *Locality is the lever.* Gowers's method needs structure only on boxes
    of width `N^(poly α)`. That is why dimension 1 → 2 kept polynomial loss
    (18.2 at `k = 5` via the polynomial cubic discrepancy).
  - *Where dimension 2 → 3 still loses.* The width loss of Lemma 16.1 is
    already removed (J.3: the Schmidt recurrence). The loss that remains is
    the dimension-two graph count `exp(poly)` entering the joint box's
    budget `G` (K.4). A single trilinear piece only needs one lift. But the
    slices' frequency relation `Δ`, with fibres `≤ δ⁻²`, must be handled
    simultaneously, which is the stackability problem (H.3, H.4).
  - *Reduction.* The trilinear piece follows from a **local**
    dimension-two structure theorem whose graph count, or Bohr rank, is
    `poly` (for 18.2) or `quasi-poly` with explicit exponent (for 18.7), via
    a single-piece lift with polynomial loss.
  - *Why the deep contract does not suffice.* It is global, and its
    density `exp(−poly)` is too weak for `k = 6`.
  - *Sources.* The only known dimension-two source with quasi-polynomial
    loss is Milićević 2026, whose Proposition 9.3 has the coherence gap of
    J.5c. Repairing that gap is therefore on the critical path for 18.7 at
    `k = 6` as well. For 18.2 at `k = 6`, no polynomial dimension-two
    source is known: a *global* one would be PFR-strength over `ℤ`. Whether
    locality makes a polynomial local dimension-two theorem accessible is
    the open question this route turns on.

### L.1 The single-piece lift: plan and first piece (2026-10-10)

The user chose to build the single-piece dimension `k → k+1` lift (Notes L).

**Plan.** Gowers's Lemma 16.10 covers all of `φ₁` and loses in three
unions:
- over `r²` anchor pairs;
- over the `2^k − 1` cross-section remainders in Lemma 16.9;
- over the graphs of each cross-section cover.

For one dense piece, make one choice in each:
- the largest class on a cell, of density `≥ 1/q`;
- one anchor pair;
- one graph per cross-section, on a common cell (synchronized retiling,
  already in the corpus).

The density is then `poly(1/q, 1/Q, θ)`, where `q` is Lemma 16.9's class
count and `Q` is the dimension-`k` count per cell. So the lift is
polynomial exactly when the dimension-`k` input has polynomial counts.
That input is Notes L's open core.

**First piece, done:** `Proofs16SinglePieceAnchor`.
- `exists_anchor_pair_capture`: on a cell `T × J` whose fibres are split
  into at most `q` classes, one anchor pair `a ≠ b` captures `W` (the
  points whose class contains `(h, a)` and `(h, b)`) with
  `|D|³ ≤ (q|T|)²(|J|²|W| + |J||D|)`. The proof uses two Cauchy–Schwarz
  steps over class sizes and averages over anchor pairs.
- `anchor_reconstruction`: if `φ(h, ·)` is affine on each class (the form
  of Lemma 16.9's `Section16LineCover`), then on `W`
  `φ(h, x) = φ(h, a) + (φ(h, a) − φ(h, b))(a − b)⁻¹(x − a)`.

So on the captured set `φ` is fixed by its cross-sections at `a` and `b`.
Two multilinear graphs, one for each cross-section, give one
`(k+1)`-multilinear piece. The `r²`-pair union, and its exponent
`p = 4r²γ⁻²s`, does not arise.

**Second piece, done:** `Proofs16SinglePieceSections`.
- The dimension-`k` input is now a named hypothesis,
  `LocalMultilinearPieceAt k γ c w`. Let `B` have density `θ` in a proper
  box `P` and carry a function with the product property. Then some proper
  sub-box `R`, with `width R ≥ w θ (width P)`, and one multilinear `μ`
  agree on `c θ·|R|` points of `B ∩ R`.
  - It is a *piece* statement, not a cover. That is the form the consumer
    needs: `section16_joint_frequency_box` outputs one box and one
    multilinear map with dense large-frequency agreement.
  - It holds trivially with `w θ L = min 1 L` (single-point boxes). Its
    content is a growing `w` at polynomial `c`.
- `single_piece_on_line_cell` proves the lift on one line-covered cell
  `T × J`. Setting: `D` has density `θ`, fibres split into `q` classes, and
  `φ(h, ·)` is affine on each class. Output: one proper `(k+1)`-box
  `S ⊆ T × J` and one multilinear `μ` with
  `θ₁·c(c(θ₁))·|S|` agreements in `D ∩ S`, where `θ₁ = θ³/(4q²)`, and
  `width S ≥ ⌊√(w(c θ₁)(w θ₁ (width T)) − 1)⌋ − 1`.
- The proof chains five steps:
  1. one anchor pair (step 1);
  2. popular fibres (`popular_fibres`: `θ₁|T|` base points, each with
     `≥ θ₁|J|` captured points);
  3. the input applied to `φ(·, a)`, then **nested** to `φ(·, b)` on the
     agreement set inside the first box. Nesting replaces "common cells"
     and costs `c∘c` instead of a union over graph pairs;
  4. `anchor_reconstruction`, giving `φ = section16TwoAnchorLift a b μ_a μ_b`;
  5. the corpus's synchronized retiling
     (`box_product_tiling_of_contained_axis`), whose cells cost only the
     square root in width, and a mediant pick of the densest cell.
- With `c t = t^D` and `w t L = L^(t^E)`:
  - the density is `θ₁^(D²+1)`;
  - the width exponent is `½·θ₁^E·c(θ₁)^E`.
  Both are polynomial in `θ` and `1/q`. **The lift itself loses only
  polynomially.** The exponential losses of Lemma 16.10 analysed in Part A
  come from covering all of `φ₁`, not from the lift step. Whether the
  line-covered cell itself (item 1 below) can be had at polynomial cost is
  still open.
- Hypotheses kept explicit: `T`'s first axis is no longer than `J` and at
  most `N/2` (as `Box.short_parent_partition` arranges), and
  `|J| ≥ 2q²/θ³`.

**Third piece, done:** `Proofs16SinglePieceSpectrum` (the spectrum half of
a single-piece Lemma 16.9).
- *Why a piece input is not enough.* Lemma 16.9 writes
  `φ₁ = (−1)^k φ′ + φ″`. `φ′(h, ·)` is linear on short progressions whose step
  lies in the Bohr set of the **whole** large spectrum `K_h`. So every
  frequency of `K_h` must lie on one of few multilinear graphs: a cover
  requirement on a dense set of `h`. Peeling the `≤ δ⁻²` spectrum layers one
  piece at a time would nest `c` up to `δ⁻²` times, at `exp(poly)` cost.
  That is the stackability problem of H.3/H.4 again.
- So the dimension-`k` open core is a **relation** statement,
  `LocalRelationCoverAt k δ Qc c w`. Take a product-property relation with
  fibres `≤ M` and a set `H` of density `θ` in a proper box. Then on one
  proper sub-box `R` (width `≥ w θ (width P)`), a set `G ⊆ H ∩ R` with
  `|G| ≥ c θ·|R|` has every value on `q ≤ Qc θ M` multilinear graphs.
  - It is trivial with `w θ L = min 1 L`.
  - Its content is polynomial `c` and `Qc` at growing `w`.
  - `LocalRelationCoverAt.localMultilinearPieceAt` derives the function
    form of step 2 at density `c/Qc`, by pigeonhole. **One hypothesis
    therefore drives the whole lift.**
- `single_piece_of_spectrum_cover` assembles step 3 with step 2.
  - *Setting.* A dense `E` in a cell `T₀ × J₀` with
    `φ = s·f + M″` on `E`, where `M″` is one multilinear map. `f(h, ·)` is
    Bohr-linear for `K_h`, and `K_h` lies in a product-property relation
    with fibres `≤ M_sp`. Both conditions are needed only at base points
    that carry points of `E`, the form Lemma 16.5's good set gives.
  - *Output.* One proper `(k+1)`-box inside `T₀ × J₀` and one multilinear
    map agreeing with `φ` on a `singlePieceDensity c ρ 1` fraction, where
    `ρ = (θ/2)·c_R(θ/2)`.
  - *Proof.* Popular fibres, the cover hypothesis, and the corpus's
    single-box Lemma 16.6 core. The core's statement shape
    `Section16RetiledLinearityBound` was moved to the light module
    `Proofs16RetiledLinearityBound`. `exists_polynomial_retiled_linearity_profile`
    supplies it at width exponent `1/(2p(q+1)^(2^(k+2)))`, polynomial in `q`.
    Then a dense cell (`exists_dense_cell`), a short-parent sub-cell, and
    step 2 with one class (`single_piece_on_affine_cell`: `M″` is affine in
    the last variable, so each fibre is affine).
- With polynomial `c`, `c_R` and `Q_c`, every density in the chain is
  polynomial in `θ`. The widths lose
  - the input widths `w`, `w_R`;
  - one square root and a factor `8` (retiling);
  - the reciprocal-polynomial exponent `ε(q)`.

**Fourth piece, done:** `Proofs16PieceCalculus` and
`Proofs16SinglePieceRemainder` (the remainder half of a single-piece
Lemma 16.9).
- *A provider calculus.* `LocalPieceFor c w Dom g` says one function has
  local pieces everywhere: every `θ`-dense `H ⊆ Dom` in every proper box
  has one proper sub-box and one multilinear map agreeing on a `c θ`
  fraction. It is closed under:
  - the input: `LocalMultilinearPieceAt.localPieceFor`, given the
    hereditary product property;
  - translation and coordinate permutation (`LocalPieceFor.transport`),
    with the same parameters;
  - an unused final coordinate (`lift_last`): density
    `c ↦ (θ/2)·c(θ/2)`, width `L ↦ ⌊√(w(θ/2)⌈L/8⌉ − 1)⌋ − 1`. The proof:
    short-parent cells, a dense cell, popular fibres, the base provider,
    synchronized retiling, and a dense retiled cell;
  - any embedded active coordinate set (`lift_prefix`, `lift_embedding`,
    mirroring the corpus's `MultiplyLinearFunction.lift_embedding`);
  - nesting (`simultaneous`, `simultaneous_finset`): several providers give
    one sub-box on which all functions agree with multilinear maps at
    once, at density `C^[r](θ)`;
  - weakening of parameters (`mono`).
- *The remainder.*
  - Each non-top vertex `φ_e(h, x) = φ(x₀ + e·h, x)` is a translated
    pullback of `φ` to the coordinate face of its active directions.
    `HasProductProperty.coordinateFace` passes the product property down,
    so the dimension-`|S_e|` input gives it a provider
    (`vertex_localPieceFor`).
  - `remainder_piece` nests the `2^k − 1` vertex providers into one
    multilinear map for `φ″ = section16PhiRemainder φ x₀`, at density
    `C^[2^k−1](θ)`.
  - Gowers's cover version sums vertex covers with Lemma 16.8, where the
    graph count becomes `q(…)^(rs)`. The piece version pays only the
    nesting depth in the density, which is polynomial for fixed `k` when
    `C` is.

**Fifth piece, done: the single-piece lift is a theorem.**
`Proofs16SinglePieceLift.single_piece_lift`.
- *Input.* A pair `(B, φ)` in `(ℤ/N)^(k+1)` with Lemma 16.4's arrangement
  conditions (ii) and (iii) and the product property.
- *Output.* One proper box `S` and one multilinear `μ` with
  `ρ·|S| ≤ |{z ∈ B ∩ S : φ z = μ z}|`, where
  `ρ = singlePieceDensity c (spectrumPieceRho c_R ρ₁) 1` and
  `ρ₁ = C^[2^k−1](θ₂)`.
- *Named inputs, all local and all pieces or local covers:*
  - `LocalRelationCoverAt k δ` for the spectrum relation;
  - `LocalMultilinearPieceAt k` for the slices of `φ₁`;
  - vertex providers `(C, W)`. `vertex_providers_of_low` supplies them
    from `LocalMultilinearPieceAt l` for `l ≤ k`.

  The rest is proved:
  - Lemma 16.5 without condition (i), via the new
    `section16_dense_induced_selection_of_arrangements`;
  - Lemma 16.7;
  - the identity `φ₁ = (−1)^k φ′ + φ″`;
  - the spectrum relation's product property (Lemma 14.3) and fibre bound;
  - the polynomial retiled linearity
    (`Section16RetiledLinearityBound`, a hypothesis with its witness
    `exists_polynomial_retiled_linearity_profile`);
  - all geometry.
- *Condition (i) is never used.* Lemma 16.4's cover-form cross-section
  hypothesis is where Gowers's induction pays exponentially. The
  single-piece route replaces it by the vertex providers.
- *Degree count for the first open case* (`k = 2`, a trilinear piece, as
  `section16_joint_frequency_box` at `k = 2` needs). Write
  `θ₁ = (θγ/4)^(2^128)` and `θ₂ = 2^(−32)θ₁^8`. Suppose the inputs are
  polynomial: `C(t) ≈ t^{D_C}`, `c_R(t) ≈ t^{D_R}`, `c(t) ≈ t^{D_c}`.
  - Then `ρ₁ ≈ θ₂^(D_C³)`.
  - The final density is about `(θγ)^E` with
    `E ≈ 2^131·D_C³·(1+D_R)·3·(1+D_c²)`.
  - With `θ, γ` polynomial in `α`, this is `α^(2^132·poly(D))`. That is far
    inside K.4's polynomial budget `D_total ≲ 2^32768/728`. The input
    exponent `D` enters six times (`D_C³·D_R·D_c²`), so `D` up to roughly
    `2^5400` would fit.
  - The widths stay polynomial in `N`: each step takes a power, a square
    root, or a factor `8`, and `ζ = 2^(−s(θ,γ,k))` costs only a threshold
    `N ≥ exp(poly(1/α))`.

  This is an order-of-magnitude count, not yet a kernel-checked
  comparison.

**Sixth piece, done: a dense frequency box from local inputs.**
`Proofs16SinglePieceFrequency.single_piece_frequency_box`, a conditional
replacement for `section16_joint_frequency_box`.
- *Statement.* Let `f` not be uniform of degree `k + 2`. Then some proper
  box `P ⊆ (ℤ/N)^(k+1)` and one multilinear `μ` have `ρ·|P|` points at which
  `μ` is a large frequency, with `ρ` the polynomial density of step 5.
- *Chain.* `section16_large_frequency_graph`, then explicit Lemma 15.6
  (`β = γ = α/2`), then `single_piece_lift`.
  - Lemma 15.6's arrangement parameter `(βγ/2)^E` equals
    `section16ThetaOne α (α/2) k` exactly.
  - So Lemma 16.4's dichotomy, and with it every cover-form
    lower-dimensional `Theorem162At`, drops out of the route.
- *Downstream.* The output has the shape
  `polynomial_localization_of_dense_frequency_box` consumes. The existing
  route (localization → `FunctionDiscrepancyBound.of_short_polynomial_localization`
  → `theorem_18_2_of_function_discrepancy_budget`) therefore applies once
  the width formula dominates `N^e`. The closing tool for the budget is
  `densityIterationClosedThreshold_le_double_exp`, as in the five-term
  case (`fejerFiveTermThreshold_le_explicit_tower`, exponents up to
  `2^73`).

**Correction (2026-10-10, same day): the box-local input hypotheses are
false; steps 2–7 are vacuous as stated.**

`LocalMultilinearPieceAt k γ c w` and `LocalRelationCoverAt k δ Qc c w` ask
for pieces or covers in *every* proper box, for *every* set with the
product property. But `HasProductProperty` is normalized by the whole
modulus: its inequality is `γ^(8p)·N⁻¹·(Σθ)⁴ ≤ energy`. The energy contains
the diagonal quadruples `(x, y, x, y)`, so
`energy ≥ (Σθ²)² ≥ (Σθ)⁴/|E|²`. Hence the inequality holds automatically
whenever every coordinate line of `B` has at most `√N` points.

*Counterexample.* Take a proper box `P` with all axes of length `≤ √N`,
`B = P` (so `θ = 1`), and `φ(x) = (x₀)²`.
- `φ` has the product property on `B` for every `γ ≤ 1`, by the diagonal
  bound above.
- A multilinear `μ` is affine along every coordinate-0 line, and a
  quadratic agrees with an affine map at no more than 2 points of a proper
  progression. So `μ` agrees with `φ` on at most `2|R|/width(R)` points of
  any sub-box `R`.
- So `c(1)·|R| ≤ 2|R|/width(R)` forces `width(R) ≤ 2/c(1)`. Since `N` is an
  arbitrary prime, `w(1, L) ≤ 2/c(1)` for every `L`.

Any growing `w` makes both hypotheses false. The theorems that assume them
remain true but are **vacuous**:
- `single_piece_on_line_cell` (the product-property corollary);
- `single_piece_of_spectrum_cover`;
- `LocalRelationCoverAt.localMultilinearPieceAt`;
- `vertex_localPieceFor` and `vertex_providers_of_low`;
- `slice_localPieceFor`;
- `single_piece_lift` and `single_piece_frequency_box`;
- `SinglePieceInputs` (step 7, not yet published).

The order-of-magnitude "fits K.4" count above is therefore withdrawn, until
the inputs are restated.

*What survives.* Everything stated in terms of *providers* stays valid and
reusable:
- `exists_anchor_pair_capture` and `anchor_reconstruction`;
- `single_piece_on_line_cell_of_slices`;
- the provider calculus `LocalPieceFor`: `transport`, `translate`,
  `reindex`, `lift_last`, `lift_embedding`, `simultaneous`,
  `simultaneous_finset`, `mono`;
- `remainder_piece`, `exists_dense_cell`, `exists_short_parent_dense_cell`,
  `section16SpectrumRelation_fibre_le`;
- the `*_of_arrangements` forms of Lemma 16.5.

A provider is a statement about one function on one domain, and it *is*
satisfiable on good domains.

*The repair.* The inputs must be **global-to-local**, as Gowers's own
Theorem 16.2 is. A relation with the (global) product property and
`|Γ| ≤ γ⁻²N^l`, after deleting `θN^l` base points, is covered on every
proper box by few multilinear graphs (`MultiplyLinearWith Qb Eb`).
- Dimension one is **proved** with polynomial controls:
  `section16_product_relation_cubic_cover` has `Qb ≤ 3(2/(γθ))^10002` and
  `Eb = 2^(−27)σ³/q⁴`.
- From such a cover, a provider follows on the good domain: a dense cell,
  then pigeonhole over the graphs.
- So the restated open core is a polynomial-control
  `MultiplyLinearWith`-cover at dimension 2. It is **non-stackable**:
  no union over members is needed, because the single-piece route never
  forms unions. That is weaker than Part J's `StackableStructureAt 2`.

**The repair (same day): global-to-local inputs and providers on good
domains.**

`Proofs16GlobalCoverProviders`:
- `PolyCoverAt l Qb Eb` is the global-to-local polynomial cover. A relation
  with the global product property and `|Γ| ≤ γ⁻²N^l`, after deleting
  `θN^l` base points, is `MultiplyLinearWith (Qb γ θ) (Eb γ θ)`-covered on
  every proper box.
  - `polyCoverAt_one` proves it in dimension one from
    `section16_product_relation_cubic_cover`. There
    `Qb = 3·section16BaseFamilyBound γ θ ≤ 3(2/(γθ))^10002`, independent of
    the loss, and `Eb = cubicBaseExponent = 2^(−27)σ³/q⁴`.
- `MultiplyLinearWith.localRelationCoverFor` turns a cover on a good set
  `J` into a per-relation local cover provider on `J`.
  `MultiplyLinearWith.localPieceFor` does the same for a function: a
  dense cell, then pigeonhole over the graphs, giving density
  `(θ/2)/Qb(θ/2)` and width `⌈L^(Eb(θ/2))⌉`.
- `card_filter_selected_not_mem_le` counts preimages: deleting `θN^l`
  points in an `l`-dimensional face costs `θN^n` points of `(ℤ/N)^n`.

Generalizations:
- `single_piece_of_spectrum_cover_for` takes a provider for the spectrum
  relation on a domain containing the base points. It needs no product
  property and no fibre bound.
- `remainder_piece_on` takes vertex providers on arbitrary domains.
- `vertex_localPieceFor_of_face` lifts any face provider to the translated
  cube vertex.

`Proofs16SinglePieceGlobal`:
- `single_piece_lift_core` is the lift from providers on explicit domains,
  for any dense part `B₁′` of Gowers's good domain `B₁` inside them.
- `single_piece_lift_global` builds every provider from `PolyCoverAt` and
  calls the core. It covers three kinds of retained objects:
  - the spectrum relation `Δ` (dimension `k`, parameter `δ`);
  - each non-top vertex face pullback (dimension `|S_e| ≤ k`);
  - each translated last-coordinate slice (dimension `k`).

  It then removes the three bad sets. Each costs at most
  `θ′N^(k+1)`, with `θ′ = θ₂/(2(2^k+1))`, so `|B₁′| ≥ (θ₂/2)N^(k+1)`.

**Where the gap now stands.** The single trilinear piece (`k = 2`) needs
only `PolyCoverAt 1`, which is proved, and `PolyCoverAt 2`.
`PolyCoverAt 2` is a polynomial-control, **non-stackable** cover theorem
for two-dimensional product relations. It is the remaining open core.
Two comparisons:
- It is weaker than Part J's `StackableStructureAt 2`, which also asks
  that unions of members stay covered.
- It is stronger than the proved `theorem_16_2_at_two`, whose controls
  are tower-type.

The kernel-checked length-6 budget comparison is still to be done.

**Step 7 (repaired route): a conditional degree-four inverse theorem.**
`Proofs18SinglePieceInverse`:
- `single_piece_localization_global`: the frequency box of width `≥ N^e`,
  localized by `polynomial_localization_of_dense_frequency_box` at
  parameter `singlePieceEta = 2^(−2(k+2)³)·(ρ/2^(k+1))·α²/4`.
- `single_piece_inverse_step_global`: a degree-`(k+1)` discrepancy bound
  gives a degree-`(k+2)` bound at parameter `η·β/4`, given the per-modulus
  conditions `SinglePieceModulusConditions` above a threshold `Tloc`.
- `single_piece_quartic_inverse_global`: `FunctionDiscrepancyBound 4` at
  parameter `η·β₃/4`, where `β₃` is the proved Fejér cubic parameter at
  input `η/(2·10⁵)`.
  - *Inputs:* `PolyCoverAt 1` (proved), `PolyCoverAt 2`, the retiled
    linearity bound (witnessed by
    `exists_polynomial_retiled_linearity_profile`), and the per-modulus
    scale conditions.
  - *Consequence:* `theorem_18_2_of_function_discrepancy_budget`'s
    mechanism then gives Theorem 18.2 at length six, once the closed
    threshold fits.

**Order-of-magnitude budget (informal; not kernel-checked).** Write
`D` for the polynomial degree of `PolyCoverAt 2`'s controls
`Qb ≈ (γθσ)^(−D)` and `Eb ≈ (γθσ)^D`, and set `k = 2`, `θ = α`, `γ = α/2`.
- *Densities.*
  - `θ₁ = (α²/8)^(2^128)`, `θ₂ ≈ θ₁⁸`, and the deletion budget is
    `θ′ = θ₂/10`.
  - Each provider density is `s ↦ s^(1+D)(γθ′)^D`; each unused coordinate
    adds one degree.
  - So `ρ₁ = C^[3](θ₂/2) ≈ θ₂^(O(D³))`, then `ρ′ ≈ ρ₁²` and
    `θ₁′ = ρ′³/4`.
  - The final density is `θ₁′·c(c(θ₁′)) ≈ θ₂^(O(D⁵)) ≈ α^(2^132·O(D⁵))`.
- *Parameters.* `η ≈` the density, and the Fejér parameter costs a power
  `2^59`, so `β₄ ≈ α^(2^191·O(D⁵))`. The length exponent `σ` is
  `exp(−poly(1/α))`. That is admissible: `densityIterationClosedThreshold_le_double_exp_of_exp_budget`
  takes `σ⁻¹ ≤ exp(X^r)`. The modulus thresholds (widths `N^(poly α)`,
  the retiling threshold `exp(poly(q))`, `q ≤ Qb`) are single
  exponential in `poly(1/α)`.
- *Threshold.* The closed threshold is about `exp(exp(α_δ^(−P)))` with
  `P ≈ 2^200·D⁵`, where `α_δ = intervalUniformityParameter δ 6 ≥ 2^(−544)·δ^192`.
  `szemerediThreshold δ 6 = 2^(2^(δ^(−2^32768)))`. The comparison holds
  when `P ≲ 2^32768/800`, i.e. `D ≲ 2^6500`.

So, up to bookkeeping that is not yet kernel-checked: **a polynomial
`PolyCoverAt 2` of degree up to about `2^6500` would give Theorem 18.2 at
length six.** The kernel-checked part ends at
`single_piece_quartic_inverse_global`. Closing the budget formally needs
explicit upper bounds for:
- `shortLocalizationThreshold` and `inverseStepThreshold`;
- the provider width chains under power-law controls.

The corpus does not have these yet (the five-term case has its own,
`fejer_five_term_step_threshold_le_double_exp`).

**On the open core `PolyCoverAt 2`.**
- It is Theorem 16.2 in dimension two with polynomial controls. The
  corpus has tower-type controls (`theorem_16_2_at_two`).
- Cover form is essential. A single piece per box is not enough, because
  every proper box needs all but `σ` of its points covered.
- Peeling global pieces cannot replace it: pieces live on boxes of width
  `N^(poly α)`, so about `N^(2−o(1))` pieces would be needed.
- It is the dimension-two analogue of the proved dimension-one
  `section16_product_relation_cubic_cover`, without the stackable-union
  requirement.
- *Relation to Part J's variety route.* J.4 splits dimension-two
  structure into three steps:
  - (1) `BihomExtraction`, open;
  - (2) Milićević's deep variety structure, behind the Prop 9.3 coherence
    gap of J.5c;
  - (3) stackability.

  Then the readout (R) turns variety pieces into multilinear maps on
  boxes. **The single-piece route removes step (3).** A
  `MultiplyLinearWith` cover per relation is all it needs, with no unions
  of members. So `PolyCoverAt 2` would follow from (1), (2) and (R) alone:
  - at quasi-polynomial strength, if (1), (2) and (R) are
    quasi-polynomial. Nesting compounds the quasi-polynomial exponent,
    though: `c∘c` turns `exp(−C·log^A(1/t))` into exponent about `A²`,
    and the route nests about five times. So only input exponents `A`
    around `3400^(1/5) ≈ 5` would meet K.4's half-density budget
    (`A ≲ 3400`) for Corollary 18.7 at `k = 6`.
  - at polynomial strength, if they are polynomial. Theorem 18.2 at length
    six needs this.

**Next.**
1. Kernel-check the budget: explicit upper bounds for
   `shortLocalizationThreshold`, `inverseStepThreshold` and the width chains
   under power-law controls, giving `Theorem182At 6` from a power-law
   `PolyCoverAt 2`.
2. The open core `PolyCoverAt 2`, via J.4's steps (1), (2) and (R), with
   no stackability needed.

### L.3 Family-uniform covers: a route to `PolyCoverAt 2` and beyond (proposal, 2026-10-10)

**Idea.** H.4 asked for a *structure-level* stackable class and called its
preservation open. Stackability can instead be made *procedural*.
- Dimension one is stackable: the covers of any family of product relations
  come from their Freiman families, and Corollary 7.11 linearizes all
  members of all relations at once.
- A dimension-`k+1` cover, built Gowers's way, is **generated by
  dimension-`≤ k` data**:
  - the spectrum relations `Δ`;
  - the cross-section remainders `φ_e`;
  - the anchor slices;
  - plus the recurrence and retilings.

  Covering the generators of *all* pieces of *all* relations in a family
  at once, then running one simultaneous recurrence, puts the whole
  family's dimension-`k+1` covers on common cells. There are no
  sequential unions (H.2), so widths are not raised to the number of
  pieces.

**Inductive statement (to be formalized): `UniformCoverAt k`.** For fixed
`γ, θ`:
- *Good sets.* Every product relation `Γ` gets a good set `J(Γ)` with
  `|J(Γ)| ≥ (1−θ)N^k`, depending only on `Γ`.
- *Covers.* For every finite family `Γ₁, …, Γ_n`, every loss `σ` and every
  proper box `P`, one partition of `P` and `≤ Qb(n,σ)` multilinear maps
  per cell cover the values of every `Γ_i` over `J(Γ_i)`, outside a
  `σ`-fraction of `P`. Cells have width `≥ width(P)^(Eb(n,σ))`.
- *Controls.* `Qb` and `Eb` are polynomial in `n`, `1/σ`, `1/(γθ)`.
- `UniformCoverAt k ⇒ PolyCoverAt k` (a family of one).

**Base case.** Dimension one is essentially proved: per-relation Freiman
families (`section16_extract_uniform_base_family`) give the good sets, and
the stackable union of members (`CubicStackableClass 1 1`) gives the
family covers.

**Step `k → k+1` (sketch).** For each relation of the family, run
Theorem 16.2's extraction loop. It yields `poly` structured pairs
`(B_j, φ_j)` (Lemma 15.6 replaces Lemma 16.4's dichotomy, as in step 6).
For each pair it fixes `H_j, Y_j, φ′_j, x₀_j`, the spectrum `Δ_j`, the
vertex cross-sections, and the slices `h ↦ φ_j(x₀_j + h, a)` for every
`a`. All are global objects, so `J(Γ)` is the set of points surviving all
their good sets. On a box `P`:
1. Cover all `Δ_j` at once by `UniformCoverAt k`. Then run one
   simultaneous recurrence for all spectrum graphs, at the reciprocal
   polynomial exponent of `exists_polynomial_section16_recurrence_profile`,
   and retile the last axis. Every `φ′_j(h, ·)` is now linear on every cell.
2. Cover all vertex cross-sections at once, lifted as cylinders, and
   retile.
3. On each cell, choose `r` anchors per pair by averaging. Cover all the
   anchor slices of all pairs at once by `UniformCoverAt k`, retile, and
   lift with `section16TwoAnchorLift`.

The cost of a step:
- the refinement depth is a constant number of dimension-`k` covers, so
  `Eb_(k+1) ≈ Eb_k^3·poly`;
- counts multiply by `poly`.

Everything stays polynomial for fixed `k`.

**Why the earlier obstructions do not apply.**
- A (inner-loss uniformity) concerned Gowers's self-referential control
  functions. `MultiplyLinearWith` allows controls polynomial in `σ`.
- B and J.3 (the exponential in `q` through Lemma 16.1) are removed by the
  polynomial simultaneous recurrence.
- H.2 (sequential unions) never arises.
- H.3's "all at once" union of slices into one relation (product property
  degrading to `γ/√r`) is not used: slices stay separate members of a
  family.
- G (anchors and losses) is handled per cell with deterministic anchors.
- The Bohr radius `ζ = 2^(−s)` costs only a polynomial factor in the
  exponent: small boxes are covered exactly by interpolation on
  width-2/3 cells, as `section16_coarse_relation_cover` does in dimension
  one.

**Risks to check before formalizing.**
- Good sets must not depend on the family or the box. All deletions above
  are global, and all per-box losses are `σ`-fractions.
- The per-cell anchor families change from cell to cell. Uniformity
  requires every slice's good set to be fixed in advance, for all `a`;
  the total deletion is then `θN^(k+1)`.
- The polynomiality of Lemma 15.6, 16.5 and 16.7 at the relevant
  parameters, already used in step 6.

If the induction holds, Theorem 16.2 has polynomial controls in every
dimension. Gowers's Section 16 would then deliver its claimed
double-exponential bound once the budget is checked, and the single-piece
route gives Theorem 18.2 at length six from `UniformCoverAt 2`.

**Where the proved dimension-two cover loses polynomiality (survey,
same day).** The general-`k` lift
`Section16AllBoxLineCoversWith.cubic_multiplyLinearWith` already has
polynomial slice controls (`3rq`, `cubicBaseExponent(rq)`), and at
`k = 1` its slice provider is proved polynomial
(`Section16FinalFreimanFamilies.cubic_slice_provider`). The losses are:
1. **The γ-side of the line covers.**
   `Section16StructuredPair.good_domain_remainder_cover` uses the printed
   `(γ, R)` face controls, with `R = section16Lemma9R ≈ (1/θγ)^(2^128)`.
   - `section16Lemma9QBound = (γσ/2R)^(−2^1024·R)` enters the graph count
     through `qGamma` and the anchor sample count.
   - `multipleC(σ/2R, γ, 2)^R` enters the width exponent
     (`lemma9WidthWithExponent`).
   - The repair (H.3a): feed the proved polynomial dimension-one face
     covers (`polyCoverAt_one`) into the remainder. The line-cover
     interface hard-wires `qGamma ≤ section16Lemma9QBound`, so it needs a
     parametrized form.
2. `128^(−12·Spec)` from the old recurrence. The polynomial variant
   (`exists_polynomial_common_base_cover`) already removes it.
3. `ζ`. It costs only a factor `1/(10·S₁)` through the threshold cap.
4. **The union of pieces** (`MultiplyLinearWith.finsetUnion`) is
   sequential, so the whole-relation cover falls back to the printed
   `MultiplyLinear γ (γ⁻²S₁¹⁰)`. The family-uniform construction above
   targets exactly this.

**Plan.**
- (A) A polynomial piece cover in dimension two: a parametrized line-cover
  interface, polynomial remainder covers from the dimension-one faces,
  and the polynomial recurrence.
- (B) The simultaneous union over the `γ⁻²/mass` pieces of one relation,
  which gives `PolyCoverAt 2`.
- (C) The same for families, which gives the stackability that dimension
  three needs.

### L.3a Progress on (A): the polynomial piece cover (2026-10-10)

Loss 1 above is repaired at the interface level. Every piece-level control
is now a parameter, and the piece cover is polynomial when its inputs are.

- **Coordinate lifts with arbitrary controls**
  (`Proofs16WithCoordinateLifts`).
  - `MultiplyLinearWith.lift_last` (count `max(Qb θ, 3^(k+1))`, width
    exponent `Eb θ/16`).
  - `MultiplyLinearWith.coordinateReindex` (controls unchanged).
  - `lift_prefix` and `lift_embedding` (count `max(Qb θ, 3^d)`, exponent
    `Eb θ/16^(d−l)`).

  These carry a face cover from `PolyCoverAt l` to the ambient dimension
  without the printed `(γ, R)`.
- **Lemma 16.9 with remainder controls** (`Proofs16Lemma9WithRemainder`).
  - The proof touches the remainder only through one cover at loss `σ/2`.
    So `AllScaleLemma169SubdomainAt` takes `MultiplyLinearWith Qr Er` on any
    sub-domain `D ⊆ B₁`, giving count `Qr(σ/2)` and exponent
    `Er(σ/2)·Eb(σ/2)`.
  - Sub-domains are needed because `PolyCoverAt` covers only off a global
    deletion (L.2): `D` is `B₁` minus that deletion.
  - Lemma 16.6 enters through its statement with an abstract width `W`
    (`AllScaleLemma166WidthAt`). `AllScalePolynomialLemma166At` is
    definitionally the polynomial instance.
  - This keeps the module off the polynomial recurrence's import closure,
    the OpenAI Schmidt stack of about 490 modules.
  - `allScaleLemma169WithAt_printed` recovers `AllScalePolynomialLemma169At`
    exactly, so nothing is lost.
- **The piece cover** (`Proofs16PieceCoverWithRemainder`,
  `section16_piece_cover_with`). The inputs are:
  - spectrum controls `(Qb, Eb)`;
  - remainder controls `(Qr, Er)` on `D`;
  - a slice provider `(Pb, Es)` on `D`, with `Pb` monotone and `Es`
    antitone in the sample size;
  - Lemma 16.6 at a power width `ζ/A(q)·m^(a/B(q))`.

  The output is `MultiplyLinearWith` for `φ₁` on `D` at every scale:
  - The count is `max(Pb(S,ρ/4), C(S,2)·Pb(S,ρ/4)², 3^(k+1))`, with
    `S = ⌈24·max(1, Qr(ρ/8))/ρ⌉`.
  - The width exponent is at least `e·a/(16 + 4 log(16A(q)/ζ))`
    (`piece_cover_exponent_lower`). Here `e = Er·Eb/B(⌊Qb⌋)` and
    `a = Es(S, ρ/4)`, all at loss `ρ/8`.
- **Bridge** (`Proofs16PolynomialLemma9WithRemainder`).
  - `exists_all_scale_power_lemma_16_6` gives the power width with
    `A(q) = 4C(q+1)` and `B(q) = 8p(q+1)^(2^(k+2))`, both polynomial.
  - This module imports the OAI closure, so it has not been elaborated on
    this machine. Its definitional step was tested on copies of the two
    width definitions.

**Item 1 done (2026-10-10): one polynomial piece in dimension two.**
- `section16_poly_piece_two` (`Proofs16PolyPieceTwo`) is kernel-checked.
  Assume `(B, φ)` in dimension two satisfies Lemma 16.4's
  arrangement-density and respect conditions and has the product property.
  Then there are `x₀` and `D` with at least `5θ′N²` points
  (`θ′ = θ₂/8`) on which `φ₁` is `MultiplyLinearWith` at every scale.
  The only other input is Lemma 16.6 at a power width.
- `section16_poly_piece_two_original` translates back: `φ` itself has the
  same cover on a subset `D′ ⊆ B` of at least `5θ′N²` points.
- All covers come from `polyCoverAt_one`, off three global deletions of
  `θ′N²` points each:
  - the spectrum relation, at `δ`, off `JΔ`;
  - the remainder, the single vertex `φ(x₀, x)`
    (`Proofs16VertexWithCovers`), off the face's good fibres;
  - the slices, through Freiman families (`Proofs16PolyPieceTwoInputs`),
    off `θ′N` points per slice.
- The controls are explicit:
  - counts `3q(δ,θ′)`, `max(3q(γ,θ′), 9)` and `3·max(1,r)·q(γ,θ′)`;
  - exponents `cubicBaseExponent`;
  - the piece count `pieceGraphBound`, polynomial in `1/ρ` and the two
    family bounds;
  - the width exponent at least
    `e·a/(16 + 4 log(16A/ζ))` (`piece_cover_exponent_lower`).

  Here `q(δ,θ′)` is polynomial in `1/θγ` of Gowers's fixed degree, through
  `δ = θ₁^O(1)` and `θ₁ = (θγ/4)^(2^64)`.

**Remaining for `PolyCoverAt 2`.**
1. **The extraction loop.** Repeatedly apply
   `section16_poly_piece_two_original` to the not-yet-covered part of a
   product relation. This is Theorem 16.2's iteration, with Lemma 15.6 in
   place of the Lemma 16.4 dichotomy, as in step 6 of L.1.
   - Each round removes `≥ 5θ′N²` points.
   - So `O(γ⁻²/θ′)` rounds suffice, polynomially many.
2. **(B), the simultaneous union** of the polynomially many piece covers.
   This is the open core:
   - `MultiplyLinearWith.union` is sequential, so its exponent is raised
     to the number of pieces.
   - The family-uniform route (L.3) runs one simultaneous recurrence over
     all pieces' generators.
   - The pieces' spectra, faces and slices are all dimension-one
     relations, which are stackable.

**(B) done at the abstract level (2026-10-10): the simultaneous union.**
All modules are kernel-checked and light (off the OAI closure).
- `Proofs16FamilyRetiledLinearity`: the recurrence partition depends
  only on the covering graphs. So one partition makes every member of a
  family `(K c, G c, A c, f c)` linear.
- `Proofs16FamilyLemma6`: Lemma 16.6 at all scales for a family, with
  one relation `Γ` covering every member's spectrum. The width is the
  single-piece polynomial width at the graph count of `Γ`.
- `Proofs16FamilyAffineLift`: the Lemma 16.10 lift for a family. One
  stacked slice cover serves every member. Per-member sampling runs at
  loss `τ/|ι|`, so the sample size grows only by the factor `|ι|`. The
  count is `|ι|·max(Pb, C(r,2)Pb²)`.
- `Proofs16FamilyLemma9` and `Proofs16FamilyPieceCover` are the same for
  Gowers's data. They are frame-limited: see below.
- `Proofs16AbstractFamily`, `abstract_family_piece_cover_with`. For
  abstract members `(H1, K, A, f, D, φ, rem)` with common relations `Γ`
  (spectra), `Γr` (remainders) and `Gs` (stacked slices), the union
  `⋃_c graph(D c, φ c)` is `MultiplyLinearWith` at every scale.
  - The width exponent is the single-piece one.
  - The count is `|ι|·max(Pb, C(S,2)Pb²)`, with
    `S ≈ 24·Qr·|ι|/ρ`.
  - `MultiplyLinearWith.union` would instead raise the exponent to the
    power `|ι|` (H.2).

*The frame lesson.* Gowers's piece structure lives in the frame
`(h, x) ↦ (x₀ + h, x)`. Pieces with different `x₀` cannot share
partitions in their own frames. In the original frame a piece has the
frequency map `Δ(· − x₀)`. This is still covered by translated
multilinear graphs, and translated Freiman families are Freiman. So the
family layer must be stated over frame-free members.

**Remaining for `PolyCoverAt 2` (B7), all assembly.**
1. A relation cylinder lift. The remainders `φ_c(x₀_c, w_last)` of all
   pieces form one cylinder over a dimension-one union of face Freiman
   families. This needs a relation version of
   `MultiplyLinearWith.lift_last`: synchronized retiling with the values
   as the family index, then a coordinate swap.
2. A cubic cover of a finite union of Freiman families, indexed by any
   finite type.
3. Per-piece data in the original frame. This is
   `section16_poly_piece_two` with its Freiman families exposed
   (spectrum, face, slices) instead of covers, and every ingredient
   translated by `x₀`.
4. The common relations for a finite family, then
   `abstract_family_piece_cover_with`.
5. The peeling loop, `section16_greedy_relation_decomposition`.
   - Sub-relations keep the product property
     (`RelationProductProperty.mono`).
   - Lemma 15.6 (`lemma_15_6_of_density_lower_explicit`) gives the
     arrangement conditions.
   - The family is padded with empty pieces to the deterministic size
     `⌊γ⁻²/mass⌋ + 1`, so the controls depend only on `(γ, θ, ρ)`.
   - Below Lemma 15.6's threshold `N₀ = poly(1/γθ)`, the coarse relation
     cover has count `3²·N < 9N₀`, which is still polynomial.

### L.3b `PolyCoverAt 2` is proved (2026-10-10)

`polyCoverAt_two_of_family_lemma6` (`Proofs16PolyCoverTwo`) is
kernel-checked and light. It states:

> `AbstractFamilyLemma166At 1 (section16PowerWidth A Bq)` with `A, B > 0`
> implies `PolyCoverAt 2 polyTwoQb (polyTwoEb A Bq)`.

The heavy bridge `exists_polyCoverAt_two`
(`Proofs16PolynomialLemma9WithRemainder`) discharges the hypothesis from
`exists_polynomial_section16_recurrence_profile`. It does so
definitionally (`familyRecThr`/`familyRecExp` are verbatim copies of the
simultaneous threshold and exponent). The bridge has not been elaborated
on this machine because it needs the OAI closure; it awaits the full
verification run.

**The proof** (B7.1–B7.5 of L.3a).
1. *Peeling.* `section16_greedy_relation_decomposition`. Each sub-relation
   with projection at least `θN²` gives a piece:
   - a one-value-per-point selection keeps the product property
     (`RelationProductProperty`, hereditary);
   - Lemma 15.6 at `β = θ/2` gives Lemma 16.4's arrangement conditions,
     since `section16ThetaOne θ γ 1 = (βγ/2)^(2^64)`;
   - `section16_poly_piece_two_data` gives the piece, in the original
     frame, with its Freiman data.

   At most `γ⁻²/(5θ′)` pieces are needed.
2. *Padding.* Pad with empty pieces (mass 0) to
   `polyTwoPieces = ⌊γ⁻²/(5θ′)⌋`, so the controls depend only on
   `(γ, θ, ρ)`.
3. *The simultaneous cover.* `section16_poly_family_two_cover`: one
   `MultiplyLinearWith` cover of the union of all pieces. The three common
   relations (spectra, a remainder cylinder, stacked slices) are unions of
   the pieces' Freiman covers (`RelFreimanCover`).
4. *Small moduli.* Below `polyTwoThreshold = max 3 (Lemma 15.6's
   threshold)`, which is polynomial in `1/θγ`, the coarse relation cover
   has count `9⌈N₀⌉`. This goes through
   `multiplyLinearWith_of_large_box_covers` with threshold `N₀`.

**The controls.**
- *Count.* `polyTwoQb = max(polyTwoFamCount, 9⌈N₀⌉)`.
  - The family count is `max(m·max(Pb, C(S,2)Pb²), 9m)`.
  - Here `m = ⌊γ⁻²/(5θ′)⌋`, `S ≈ 24·Qr·m/ρ`, and `Pb = 3(m·S·q + 1)`.
  - `q = section16BaseFamilyBound(γ, θ′)` and `θ′ = θ₂/8`.
- *Width exponent.* `polyTwoEb` is a capped product of cubic exponents
  and the recurrence divisor `8p(q+1)^8`. By
  `piece_cover_exponent_lower` and `section16_cubic_capped_exponent_lower`
  its capped parts keep a constant multiple of the product of the line
  and slice exponents, up to a factor `log(16A/ζ)`.

Everything is polynomial in `1/ρ` and in `1/θγ`. The degree is Gowers's
fixed `2^(2^6)` from `θ₁`, which `δ` and `θ₂` inherit.

**Consequences to pursue.**
- `single_piece_lift_global` at `k = 2` needs exactly `PolyCoverAt 1`
  (proved) and `PolyCoverAt 2` (now proved). Its chain ends in
  `FunctionDiscrepancyBound 4` (L.1, step 7), so it becomes unconditional
  up to the scale conditions and the budget.
- The family cover does not need a common product property, only
  per-piece data. So the pieces of a whole *family* of relations can be
  covered at once, which is plausibly the covering half of
  `StackableStructureAt 2` that Part J needs for dimension three.

### L.4 After `PolyCoverAt 2`: two routes to catalogue items (plan, 2026-10-10)

**(I) Theorem 18.2 at length six** (`Theorem182At 6`; Corollary 18.7 at
six follows).
- *Chain.* `single_piece_quartic_inverse_global` (Proofs18SinglePieceInverse)
  needs `PolyCoverAt 1` (proved) and `PolyCoverAt 2` (L.3b). It returns
  `FunctionDiscrepancyBound 4 α β σ T`.
  `FunctionDiscrepancyBound.interval_szemeredi_closed` turns that into
  six-term progressions above `intervalDiscrepancyClosedThreshold 6 δ β σ T`,
  at `α = intervalUniformityParameter δ 6`.
- *Remaining inputs.*
  1. The lift-width functions `C, W`: minima of the two lift iterates.
  2. `hretile`, from the recurrence profile through
     `Section16RecurrenceProfileWith.retiled_family` and `.single`.
  3. `hmod`, the per-modulus scale conditions
     (`SinglePieceModulusConditions`), at an explicit `Tloc`.
  4. The comparison with `szemerediThreshold δ 6 = 2^2^(δ^(−M))`,
     `M = 2^32768`.
- *Budget (K.4).* A density `β = α^D` fits whenever `D ≲ M/728`. The
  single-piece route has `D ≈ 2^132·poly(D_in)`, with `D_in ≈ c·2^64`
  from `θ₁`, so `D ≈ 2^500` at most: an enormous margin. Crude power
  bounds suffice everywhere.
- *Explicit constants.* The recurrence constants are not opaque.
  - `multilinearPartitionBoundAt_explicit` gives
    `multiaffinePartitionK/P k (2^k)`, built from the Schmidt constants.
  - `Proofs05WeylConstantBounds` bounds those Schmidt constants
    numerically.
  - So the light modules carry `K, p` as parameters with numeric upper
    bounds as hypotheses, and the heavy bridge instantiates them.
- *Template.* The five-term case:
  `fejerFiveTermThreshold_le_double_exp_alpha` (via
  `densityIterationClosedThreshold_le_double_exp`), then
  `fejerFiveTermThreshold_le_source`.

**(II) Theorem 16.2 in every dimension.** The family machinery suggests
an induction on a *stackable piece structure*: a class of `k`-dimensional
pieces with data such that
- (a) every product relation decomposes, after a `θ` deletion, into
  polynomially many pieces (peeling plus Lemma 15.6 plus piece data);
- (b) any `n` pieces have one simultaneous cover with controls
  polynomial in `n` (the family cover).

The base case is Freiman graphs. The step `k → k+1` builds `(k+1)`-pieces
whose data refers to `k`-pieces (spectra, slices) and lower faces
(remainders), and gets (b) from (b) at dimension `k` for the referenced
pieces. New ingredients:
- the remainder is a signed *sum* of `2^k − 1` vertex functions, which
  needs common-partition sums of family covers;
- relation lifts along unused coordinates in every dimension;
- piece data for general `k`.

The printed comparison per `k` would follow, if the degree recursion
`D_{k+1} ≤ poly(D_k)` fits `2^(2^(k+8))`.

**(I) progress (2026-10-10): `FunctionDiscrepancyBound 4` from the
recurrence profiles.** `length_six_function_discrepancy`
(Proofs18LengthSixScale) is kernel-checked and light. Its inputs:
- `Section16RecurrenceProfileWith 1 (familyRecThr 1 K₁ p₁) (familyRecExp 1 p₁)`;
- `Section16RecurrenceProfileWith 2 (familyRecThr 2 K₂ p₂) (familyRecExp 2 p₂)`.

It gives `FunctionDiscrepancyBound 4 α β σ T` for every `α ∈ (0, 1/2]`, at
explicit `β, σ, T`.
- The scale conditions are `ls_modulus_conditions`. Choose the largest
  allowed spectrum scale `m`. Every per-`q` condition then reduces to
  `m ≥ lsMReq` at the worst count `q = ⌊Q_max⌋`.
- The width chain is a power `N^lsF` above `lsTloc` (Proofs18WidthPowerBounds).
- `lsTloc` is a maximum of terms `c^(1/a)`, so its logarithm is
  polynomial in the reciprocal exponents.

*Remaining for `Theorem182At 6`.* For each `δ ∈ (0, 1/2]` with
`α = intervalUniformityParameter δ 6`, show
`intervalDiscrepancyClosedThreshold 6 δ β σ T ≤ szemerediThreshold δ 6`:
1. Bound `β⁻¹, σ⁻¹ ≤ X^g` and `log T ≤ K·X^p` for `X = 2/α`, with explicit
   (crude) `g, p, K`. This needs power bounds on the controls `sixQb`
   and `sixEb` (through `polyTwoFamCount`/`polyTwoFamExp`,
   `section16BaseFamilyBound`, Lemma 15.6's threshold, and
   `ζ = 2^(−multipleS)`, which enters only through logarithms), on
   `sixC`, and on the Fejér and inverse-step parameters.
2. Apply `densityIterationClosedThreshold_le_double_exp`, then compare
   `exp(exp((K+1)X^p))` with `2^2^(δ^(−2^32768))`. Since
   `X ≤ δ^(−728)·const`, this needs `728p ≲ 2^32768`.
3. Supply the recurrence constants explicitly in the heavy bridge
   (`multilinearPartitionBoundAt_explicit`), with numeric upper bounds on
   `K₁, p₁, K₂, p₂`, which enter `g, p, K` polynomially.

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
   4,134-module scoped closure, including the 128 earlier modules.
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
   *Proved arithmetic; explicit upstream constants remain unformalized.*
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

### Polynomial width through multilinear extraction

`Proofs16PolynomialMultilinearCover.exists_all_scale_polynomial_multilinear_cover`
composes the improved all-scale Lemma 16.9 with the rounded affine lift.
For total loss `rho`, let `sigma=rho/4` and let `l` be the new polynomial
linearity width evaluated at spectrum count `floor(Qb(rho/8))`. The final
proper cells have width at least
`sqrt((floor(l)/8)^(Es(samples,sigma)))/4`, where
`samples=ceil(6*max(1,qGamma)/sigma)`. The good set has relative size at
least `1-rho`, and the candidate count retains the existing slice-provider
bound. The production source and combined facade axiom audit pass.
Spectrum structure, induced selection, a remainder cover, and the slice
provider are still hypotheses. No additional upstream module is imported.

`Proofs16PolynomialCubicPowerCover.exists_polynomial_cubic_power_cover`
now specializes the lift to cubic slice controls. With the new line
prefactor `z`, line exponent `e`, uniform sample ceiling `R`, and cubic
slice exponent `a`, every `b < e*a/2` gives cell width at least `m^b` once
`section16RoundedExponentThreshold z e a b <= m`. Its candidate budget is
at most `9*R^4*q^2`, independently of the graph count chosen in the line
cover. The full production source and transitive axiom check pass. The
combined facade audit passes. The same
structural hypotheses remain; no catalogue statement closes.

`Proofs16PolynomialLineExponentComparison` proves that, for fixed positive
controls and dimension, the improved all-scale Lemma 16.9 exponent
strictly exceeds `lemma9WidthWithExponent` for all sufficiently large
spectrum counts. Apply the earlier geometric-versus-polynomial comparison
with exponent constant `2*p` to absorb the additional factor-two loss.
The production module and full facade axiom audit pass. This is a comparison
of exponents; it does not assert superiority at every small box scale or
improve the final all-length Szemeredi threshold.

### Actual pieces from the polynomial recurrence

`Proofs16PolynomialCommonBaseCover` supplies the geometric inputs from
`Section16CommonBaseDataWith` and caps the cubic lift exponent to obtain
`MultiplyLinearWith` on every proper box. `Proofs16PolynomialStructuredPiece`
constructs both the spectrum cover and the slice provider in dimension two,
then translates the selected graph into the original product-property graph.
`Proofs16PolynomialRelationDecomposition` uses graph selection and greedy
removal to cover a large base domain by a bounded family of these pieces.
The previous piece mass and family count are retained. Constants `C,p` are
independent of the density parameters, modulus, and relation, but remain
existential. All three production modules and their transitive axiom checks
pass; the full facade audit is queued. No new upstream module is imported,
and no remaining all-dimension structure statement is claimed.

### Simultaneous oscillation of multilinear variety phases

`Proofs16PolynomialVarietyOscillation` applies the same recurrence to all
`|Gamma|+|Psi|+r` defining conditions of a bilinear Bohr variety. If each
mixed phase `L_i(x_1)*x_0` is multilinear on a proper parent box, constants
`K>=2,p>0` independent of the phase count give a common proper partition
with every cell width at least `H` and oscillation at most `4*N/H`, provided
`H>=K*(|Gamma|+|Psi|+r+1)` and
`H^(p*(|Gamma|+|Psi|+r+1)^8)<=parent.width`. The global affine case
`L_i(y)=a_i*y+b_i` satisfies the phase premise. For `8<=rho*H`, every such
cell is good for the half-radius and full-radius varieties.

The complete production source and its three transitive axiom checks pass;
the combined facade audit is queued. This proves an oscillation partition
in a concrete case. Freiman linearity only on a Bohr set does not yet supply
the parent-box multilinearity premise, and an all-box positive-power
oscillation partition is not asserted. The result reuses the already
scoped Schmidt recurrence input and adds no upstream module.

`Proofs16PolynomialVarietyProfile` now chooses a rounded integer scale to
obtain good cells of width at least `W^(1/(2*p*(q+1)^8))`, where `W` is the
parent width and `q=|Gamma|+|Psi|+r`. Its integer threshold is
`max(C*(q+1),ceil(8/rho))^(2*p*(q+1)^8)`, with fixed existential `C>=2,p>0`.
`Proofs16PolynomialVarietyCover` uses one multilinear map on the good cells
and the existing nine-map coarse cover below that threshold. Capping the
positive exponent gives `MultiplyLinearWith` on every proper box, with
controls independent of the requested loss. This discharges the partition
input for globally multilinear mixed phases, including globally affine
coordinate functions. It makes no such claim for general Freiman maps
on Bohr sets. Both production modules and their five transitive axiom checks
pass; the combined facade audit remains queued behind the port build.

### All-box covers for local Freiman variety phases

The incoming two-stage construction has now been checked against the
simultaneous multilinear partition theorem on this host, including
`Proofs16OscillationPartitionInst`. `Proofs16FreimanVarietyProfile` chooses
both integer scales. Set `s=|Gamma|+|Psi|` and
`D=(p*(r+1)^8)*(p*(s+1)^8)`. Above the integer threshold
`max(C*(s+r+1),ceil(16/rho))^(2*D)`, the resulting good cells have width
at least `parent.width^(1/(2*D))`.

`Proofs16FreimanVarietyCover.exists_freiman_variety_cover` then proves
`MultiplyLinearWith` on every proper box for any subgraph of a Freiman
bihomomorphism on `V(rho)`, restricted to `V(rho/2)`. It assumes only that
the coordinate maps `L_i` are Freiman-linear on `bohr Psi rho`. Large cells
use one multilinear map; small boxes use the existing nine-map coarse
cover, with the positive exponent capped by the threshold. The controls
are independent of the requested loss. Global multilinearity and an
oscillation-partition hypothesis have both been removed from this cover
result. The stronger `OscillationPartitionsExist` predicate at every box
scale is not claimed or needed.

The complete production sources and transitive axiom checks pass; the
combined facade audit remains queued. Existence of the structured
bihomomorphism and the deep-agreement structure theorem remain hypotheses.
The new controls depend on the actual ranks and radius, with existential
universal `C,p`; comparison with the manuscript's prescribed all-dimension
controls and final explicit bounds remains separate.

### Uniform controls and the conditional deep-agreement consequence

`Proofs16FreimanVarietyUniform` proves the required comparisons explicitly:
increasing either rank bound and decreasing a positive radius lower bound
can only weaken the capped cover exponent. The resulting uniform cover
uses rank bounds `S,R` and radius lower bound `delta`, independently of the
particular variety.

`Proofs16DeepVarietyCover.exists_deep_variety_graph_cover` then sets
`B=milicevicBound D c`, `R=ceil(B)`, `S=2*R`, and `delta=exp(-B)`.
Conditional on `MilicevicDeepVarietyStructure D`, every eligible density-`c`
partial bihomomorphism has a subgraph of size at least `exp(-B)*N^2` with
nine-map all-box controls. Its positive exponent depends only on `c,D` and
the universal constants `C,p`. Encoding the agreement set and translating
to the original graph are injective, so no agreement mass is lost. Here
`B=(2+2*log(c^(-1)))^D`; the exponential appears in the mass and radius
bounds. The deep structure statement remains an explicit hypothesis.
Both production sources and all eight new transitive axiom checks pass;
the combined facade audit is queued. No new upstream module is added.

### Completed combined audit (2026-10-08)

The combined facade and port-import audit now includes all the graph-piece,
variety-partition, uniform-control, and conditional deep-agreement results
above. It checks 5,827 public Gowers theorems over a combined 2,644-module
closure, using only `propext`, `Classical.choice`, and `Quot.sound`. The
facade alone reaches 1,408 modules, including 667 OAI modules. The numbered
catalogue remains 114 companions and six open statements, with the same
source-fidelity caveats. The separate 3,700-entry quantitative port audit
checks 56,621 public OAI theorems; the full density conclusion is still
unverified. The earlier queued-audit notices above are superseded by this
checkpoint.

### Explicit inverse-polynomial variety exponent

`Proofs16FreimanVarietyCapBound` removes the opaque threshold from the
conditional cover's numerical controls. For `B=milicevicBound D c` and
`0<c<=1`, its all-box exponent is at least

`1 / (1024*p^2*(4*C+18)*(B+2)^17)`.

The proof bounds the logarithm of the integer radius threshold before
capping, so the `exp(-B)` radius costs a factor linear in `B`. The two
phase counts contribute degree sixteen. Ceiling rounding is included,
and the resulting graph-cover theorem keeps all `exp(-B)*N^2` agreement
mass and the nine-map count. Constants `C>=2,p>0` remain existential.
The deep structure assertion is still a hypothesis; this is not a new
unconditional density or all-dimension structure theorem.

The full combined audit now checks these three results and the incoming
single-map greedy variety cover: 5,838 public Gowers theorems, 1,410 facade
modules (667 OAI), and 2,646 combined modules. Only the three approved
axioms occur. The catalogue remains at 114 companions and six open
statements, with its existing source-fidelity caveats.

### Family assembly and 3,800-entry audit checkpoint

The combined Gowers audit now includes `greedy_variety_cover_family` and
`variety_structure_side`: 5,849 public Gowers theorems, a 1,411-module
facade (667 OAI modules), and 2,647 combined modules. Only the three
approved axioms occur. The structure-side result retains both
`BihomExtraction` and `MilicevicDeepVarietyStructure` as hypotheses.
The numbered ledger reproduces exactly and remains 114/6 with its
existing fidelity caveats.

The first 3,800 pinned quantitative-port entries also pass: 3,816 build
modules and 57,875 public OAI theorems in the separate 3,817-module axiom
audit. This includes the explicit empty epoch-intersection compatibility
repair. The later relative-patch finite-set repair passes its isolated
production check but is beyond this audited prefix. Provenance checks
retain all 4,134 pinned hashes, notices for 976 adapted files, and the
original license/copyright notices. The full density conclusion remains
unverified.

### One-piece reduction and 3,900-entry audit checkpoint

`Proofs16BihomPieceReduction` now passes the full audit on this host. The
combined audit checks 5,854 public Gowers theorems in 2,648 modules; the
facade reaches 1,412 modules, including 667 OAI modules. The extraction
step remains the explicit `DenseBihomPiece` hypothesis. The catalogue
remains 114/6 with its existing source-fidelity caveats.

The 3,900-entry port checkpoint passes over 3,916 build modules. Its
separate 3,917-module audit checks 58,849 public OAI theorems and the listed
compatibility declarations. Only the three approved axioms occur. This
now includes both the relative-patch finite-set repair and the redundant
CRT tactic repair. The full density conclusion remains unverified.

### Shared partitions and covers for translated variety families

The four `Proofs16JointVariety*` modules now construct a common partition
for `n` translated varieties, each with `r` mixed phases. The linear stage
uses the union of all horizontal frequencies and the union of all vertical
frequencies. Let `s` be the sum of those two union cardinalities. On each
linear-stage cell, the mixed phases of varieties whose deep translates
miss the cell are replaced by zero; all remaining phases are multilinear
there. One simultaneous partition therefore uses `n*r` mixed phases.
The cell proof handles independent translations and different radii.

For a common radius lower bound `delta>0`, set
`D0=(p*(n*r+1)^8)*(p*(s+1)^8)`. The large-box profile has exponent
`1/(2*D0)` and integer threshold
`max(C*(s+n*r+1),ceil(16/delta))^(2*D0)`. Every cell is good for every
translated variety. One multilinear map per member covers the union
on each large cell. Its fibres have cardinality at most `n`, so the
coarse small-box cover gives `9*n` maps, with the usual capped positive
exponent. This is one common partition, without sequential exponent
multiplication. The count and exponent are independent of the allowed
loss. The statement also handles the empty family.

All four production sources and all seven new transitive axiom checks
pass. The full facade audit is queued. Uniform rank padding and the
packaging as a general slice provider remain further steps; no missing
extraction or deep-structure hypothesis is asserted. These consumers
reuse the scoped recurrence and add no upstream modules.

### Uniform variety-piece families supply the general slice provider

`Proofs16JointVarietyUniform` zero-pads each member's mixed phases to a
common upper rank, proves that both full and half-radius varieties are
unchanged, and bounds the union of linear frequencies by the sum of the
member ranks. Its cover therefore depends only on common rank bounds
and a positive radius lower bound, with count `9*n` for a family of size
`n`. The original ranks may differ.

`Proofs16VarietyPieceFamilyCover` chooses the data stored by each
`IsVarietyPiece D c` and uses `R=ceil(milicevicBound D c)`, linear rank
bound `2*R`, and radius lower bound `exp(-milicevicBound D c)`. Arbitrary
finite families of their graphs receive one simultaneous cover.
`Proofs16VarietySliceProvider` then constructs `Section16SliceProvider`
for every sampled family of final-coordinate sections, assuming each
section belongs to this class. It proves `Section16SliceProviderRanges`
as well: for positive sample size, the count is at least one and the
exponent lies in `(0,1]`. This supplies the general provider used by the
polynomial affine lift, without forcing its exponent into the older
cubic class interface. Extraction of such slices is still separate.

All seven joint-family/provider production modules and the incoming
line-wise-to-bihomomorphism reduction pass the completed combined audit:
5,892 public Gowers theorems, a 1,420-module facade (667 OAI), and 2,656
combined modules. Only the three approved axioms occur. The catalogue
remains 114/6 with its source-fidelity caveats. The earlier queued-audit
notices for these modules are superseded by this checkpoint.


### Polynomial line extraction and the 4,000-entry port checkpoint

The full Gowers checker now includes the unconditional polynomial
`LineExtractor`, its dense-bihomomorphism consequence, and the resulting
structure-side reduction with only the deep-structure hypothesis.
The audit checks 5,902 public Gowers theorems in a 1,421-module facade
(667 OAI modules) and a 2,657-module combined closure. It permits only
`propext`, `Classical.choice`, and `Quot.sound`; the catalogue remains
114 companions and six open statements, with the existing fidelity caveats.

The first 4,000 pinned port entries compile in a 4,016-module closure.
Their separate 4,017-module axiom audit checks 60,327 public OAI theorems
and the listed compatibility declarations with the same three axioms.
This includes the finite local heartbeat repair in
`PreparedFiniteNestedSourceLatePowerBudget`. The full quantitative density
conclusion remains unverified and outside the Gowers facade.


### Explicit polynomial variety controls and the dimension-three lift

`Proofs16JointVarietyCapBound` bounds the common capped exponent below by
`1/(1024*p^2*(4*C+18)*(n+1)^17*(B+2)^17)`, where
`B=milicevicBound D c` and `0<c<=1`. It also retains a sharper bound in
terms of the rounded rank `ceil(B)`. Both handle the empty family.
The rational lower control transfers to actual family covers and to the
general slice provider, with count `9*n` and all required range checks.
The exponential radius threshold contributes only its logarithm.

`Proofs16VarietyUniformLiftControls` proves that this exponent decreases
with the sample count and that the interpolation candidate budget is at
most `81*R^4`, for the uniform sample ceiling `R`.
`Proofs16PolynomialVarietyPowerCover` then supplies actual
three-dimensional multilinear covers. For line coefficient `z`, line
exponent `e`, and the polynomial variety exponent `a` at sample ceiling
`R`, every `b<e*a/2` gives width at least `m^b` above
`section16RoundedExponentThreshold z e a b`. The covered good domain
has mass at least `1-rho` of the input box.

All three production sources and all ten transitive axiom checks pass,
using only propext, Classical.choice, and Quot.sound. Their combined
facade audit is queued. Spectrum structure, induced
selection, the remainder cover, and variety-piece membership of every
relevant slice remain premises. This does not close a numbered catalogue
statement or establish a new final Szemeredi threshold. These original
consumers add no upstream modules or license-scope changes.


### From deep variety structure to the actual slice provider

`Proofs16VarietyPieceClass` expresses the variety-piece class on `Point N 2`,
proves that the empty partial function belongs to it, and supplies joint
polynomial covers for arbitrary subrelations of finite unions of class
members. `Proofs16VarietyFamilySlices` then constructs the provider on
every common-base good domain whenever each original final-coordinate
slice is covered by `Q` class members. For `r` samples the count is
`9*(r*Q)` and the exponent is the polynomial variety control at `r*Q`.
The empty sample is included; positive `Q` gives all range conditions.

`Proofs16VarietyStructureSlices` pads the family from
`structure_side_of_milicevic` to the uniform count
`Q=ceil(m*exp(B(c)))+1`, where `m` is the polynomial bihomomorphism family
size at `(gamma,theta/2)` and `c=theta/(2*m)`. The padding uses empty
members. Applying the existing slice-restriction argument keeps a subset
`A` with `|A| >= |B|-theta*N^3`, on which every slice has such a cover.

`Proofs16VarietyRestrictionProvider` combines these results. Under
`MilicevicDeepVarietyStructure D` and the original product property,
the restricted set supplies the polynomial provider on every common-base
good domain. Structured slices are now a conclusion of this conditional
reduction, rather than a further hypothesis. Deep structure itself and
the subsequent printed numerical budget remain unproved.

All four production sources and their nine transitive axiom checks pass;
only propext, Classical.choice, and Quot.sound occur. The combined facade
audit is queued. No numbered catalogue claim is advanced, and these
consumers add no upstream modules.


`Proofs16VarietyFamilyLiftControls` and
`Proofs16PolynomialVarietyFamilyPowerCover` carry the slice-family count
through the actual three-dimensional cover. With `Q` pieces per slice
and uniform sample ceiling `R`, the interpolation count is at most
`81*R^4*Q^2`, and the uniform exponent is the polynomial variety control
at `R*Q`. Thus any `b<e*a/2` gives cell width `m^b` above the explicit
rounded threshold, retaining mass `1-rho`. These two production sources
and their three transitive axiom checks pass with only the three approved
axioms. The combined audit is queued. The spectral, selection, and
remainder inputs remain explicit.


### Actual dimension-three pieces and relation decomposition

`Proofs16VarietySpectrumRestriction` uses the padded variety class cover
on the two-dimensional spectrum relation. Both its graph count and its
polynomial exponent are independent of the inner covering loss.
`Proofs16VarietyStructuredExtraction` carries the variety-family slice
property through the existing proper-face and cube-respecting
restrictions, producing `Section16StructuredPair (theta/2) gamma`.
Both constructions assume deep variety structure.

`Proofs16PolynomialVarietyCommonBaseCover` supplies the spectrum,
selection, identity, and remainder inputs from common-base geometry and
extends the family power cover to every proper box. The graph count is
`max(81*R^4*Q^2,27)`. The width exponent is the cap of `e*a/4` against the
explicit rounded-power threshold, with `a` the polynomial variety control
at `R*Q`. The constants for the line recurrence, slice cover, and spectrum
cover are universal and remain existential.

`Proofs16PolynomialVarietyStructuredPiece` now constructs actual graph
pieces. For a three-dimensional product-property set of density `theta`,
it obtains a subgraph of mass at least
`eta*N^3`, where `eta=section16ThetaTwo(section16ThetaOne(theta/2,gamma,2))`.
Spectrum, slice, selection, and remainder assumptions have all been
constructed. The only additional structural hypothesis is
`MilicevicDeepVarietyStructure D`.

`Proofs16PolynomialVarietyRelationDecomposition` transfers this to arbitrary
product relations. For size at most `gamma^-2*N^3`, it covers the relation
over a base of size at least `(1-theta)*N^3` by at most `gamma^-2/eta`
pieces, each with the same polynomial-recurrence controls. This is an
actual conditional relation decomposition, not a source-fidelity claim
for Theorem 16.2. Deep structure and comparison with its printed numerical
budget remain open.

All five production sources and all eleven transitive axiom checks pass,
using only propext, Classical.choice, and Quot.sound. The combined audit
is queued. The source ledger
retains its six open statements, with the existing fidelity caveats. No
upstream modules are added by these consumers.


### Ceiling-free inner-loss bounds for the variety lift

`Proofs16VarietySampleBudget` proves that, for `0<sigma,theta,gamma<=1`,
`r=section16Lemma9R(theta/2,gamma,2)` and
`u=multipleC(sigma/(2*r),gamma,3)^r` satisfy `0<u<=1`, and the sample
ceiling is at most `7/(sigma*u)`. Consequently the interpolation graph
count is at most `81*(7/(sigma*u))^4*Q^2`. The joint slice exponent at
that sample ceiling times `Q` is bounded below by

```
(sigma*u)^17 /
  (1024*pv^2*(4*Cv+18)*(milicevicBound D c+2)^17*7^17*(Q+1)^17).
```

`Proofs16VarietyExplicitExponent` combines this with the exact line
exponent `u*E/(8*p*(q+1)^16)` and the logarithmic cap estimate. For a
fixed spectrum count `q` and exponent `E`, the actual common-base
all-box exponent is at least the product of those two displayed factors,
divided by `16+4*log(16/z)`, where
`z=section16Zeta(theta/2,gamma,2)/(4*C*(q+1))`. Thus the lower bound
contains the explicit factor `sigma^17*u^18`; neither a sample ceiling
nor a rounded threshold remains. The spectrum losses are independent of
`sigma` in the dimension-three construction above.

Both production modules and all six transitive axiom checks pass, using
only propext, Classical.choice, and Quot.sound. Facade registration and
the combined audit remain pending while the earlier full audit runs.
The constants `C,p,Cv,pv,D` remain explicit parameters. This does not
prove deep structure, the printed Theorem 16.2 budget, or a new final
Szemeredi threshold, and it adds no upstream modules.

`Proofs16VarietyCeilingFreeCover` transfers these controls to actual
multilinear covers, including their mass and partition guarantees on all
boxes. Its positive width control and graph-count bound require no
additional geometric premise. `Proofs16VarietyLossPower` separates the
inner loss exactly: writing `b=2^2048*r`, the line factor is
`(gamma/(2*r))^b*sigma^b`, and

```
u*(sigma*u)^17 = (gamma/(2*r))^(18*b)*sigma^(17+18*b).
```

Thus the power of the inner loss depends only on the outer densities.
`Proofs16VarietyCeilingFreeDecomposition` applies these controls to every
piece in the actual conditional relation decomposition, retaining the
same family-count bound, large base domain, and union cover. The slice
and spectrum counts can still involve ceilings in the outer parameters;
only ceilings and thresholds involving the inner loss have been removed.
All three further production modules and all six transitive axiom checks
pass with the same three approved axioms. Their facade registration and
combined audit also await the running audit. No catalogue claim or port
scope is changed.


### Sharper line-density extraction and smaller variety families

`Proofs16SharperLineExtractor` retains the actual density `alpha=|R|/N`
when applying Corollary 7.6. The line product property gives
`gamma^8*alpha*(alpha*N)^3` respected quadruples. The resulting extraction
mass is `2^-1882*gamma^9312*alpha^1165`, so a line of density at least
`beta` supplies the uniform bound
`2^-1882*gamma^9312*beta^1165`. Lean proves this dominates the previous
`2^-2000*(gamma*beta)^10000` over the complete density range `(0,1]`.
It also proves that the two-pass bihomomorphism mass increases and the
required bihomomorphism family count does not increase.

`Proofs16SharperVarietyStructure` constructs the variety structure side
using this improved extraction. `Proofs16SharperVarietyParameters` proves
that `milicevicBound D c` decreases with the density `c` on `(0,1]`, and
that the padded count `ceil(m*exp(B(theta/(2*m))))+1` increases with the
positive family size `m`. Thus the sharper extraction does not increase
the full variety-family budget, for every deep-structure exponent `D`.

All three new production modules and their eleven transitive axiom checks
pass with only propext, Classical.choice, and Quot.sound. They await
facade registration and integration into `section16VarietyExtractionFamily`
after the running full audit. Deep structure and the printed numerical
budget remain open, and no upstream modules are added.


### Complete density port and exact Theorem 1.3

The complete selected density closure now compiles: 4,134 pinned upstream
modules and 17 compatibility modules. Its 4,152-module axiom audit checks
63,855 public OAI theorems and the listed compatibility declarations, using
only propext, Classical.choice, and Quot.sound. The original licenses,
provenance, and modification notices are retained. The reciprocal-only
branches remain excluded; no new upstream modules were added.

`Proofs01QuantitativeDensityHeadline.theorem_1_3_holds` applies the checked
finite-set bridge to `OAI.Erdos3.manuscriptQuantitativeDensityTheorem`.
The exact companion and its upstream input pass their own transitive axiom
checks. This closes the encoded Theorem 1.3 and changes the source ledger
to 115 companions and five open statements. The existing statement-fidelity
caveats still apply to that count. The port's existential asymptotic
constants do not prove the fixed threshold in Theorem 18.2.

The earlier full Gowers audit completed with 6,023 public theorems and a
2,680-module combined closure, before the new headline and sharper-family
integration. It validates the previously queued dimension-three variety
construction and the incoming selection lemmas through `lemma19_two_new_piece`.
The source ledger at that checkpoint was still 114/6.

The sharper family is now used by `section16VarietyExtractionFamily`.
An isolated rebuild of all six affected modules on the path to the actual
ceiling-free relation decomposition passes, as do all 23 transitive axiom
checks for the new inner-loss and sharper-extraction results. All eight
modules and the density headline are registered in the facade. A new
combined audit, including the latest incoming Corollary 20 and Bohr
spectrum results, is pending; this supersedes their registration-pending
notes above, without claiming that the new full audit has completed.


### Completed combined headline and sharper-family audit

The new combined audit completes successfully: 6,125 public Gowers
theorems, a 4,940-module facade closure (including 4,152 OAI modules),
and 4,942 modules for the combined audit and import-compatibility check.
Only propext, Classical.choice, and Quot.sound occur. The OAI count in
the facade also includes the existing separately named Freiman extract;
the selected upstream density closure itself remains 4,134 upstream and
17 compatibility modules.

The audit includes the exact Theorem 1.3 companion, all 23 inner-loss and
sharper-extraction results, the updated variety-family definition, the
actual relation decomposition, and incoming Corollary 20 and Bohr spectrum
results. Their earlier pending-audit notices are superseded. The source
ledger agrees with the checked environment: 115 companions and five open
statements, with the existing source-fidelity caveats. The remaining open
entries are Theorem 16.2, Corollary 16.11, Theorems 18.1 and 18.2, and
Corollary 18.7; no completion claim is made for these.


### Dense order-eight selection pieces and actual Bohr extensions

The selection route now retains the order-eight Freiman property already
supplied by Corollary 7.6. `lineFreimanExtraction_eight`, the two
`lemma19_*_piece_eight` results, and `corollary20_step_eight` keep that
stronger conclusion. The original order-two interfaces follow from them,
with the same statements and numerical bounds.

`corollary20_dense_eight` carries three properties through the iteration:
every selected piece has size at least `kappa*N`, is an order-eight
Freiman homomorphism, and takes values in `U` on its domain. Here
`kappa=corollary20Kappa epsilon K`; the family count remains at most
`floor(K/kappa)+1`, and fewer than `epsilon*N^3` distinct triples are bad.
These properties were not all retained by the previous iteration's output.

`Proofs16Corollary20Bohr` applies Lemma 7.8 to every piece at its actual
density. Each receives a spectrum of size at most `16*kappa^-2` and an
actual `IsBHomomorphism` extension on the Bohr neighborhood of radius
`kappa/(32*pi)`. Neighborhood restriction preserves the extension.

`Proofs16Corollary20AllTriples` bounds the triples with coincident evaluation
points by `4*N^2`, using four explicit images of the two-dimensional
ambient group. Running the selection at `epsilon/2` and assuming
`N >= 8/epsilon` yields the exceptional bound `epsilon*N^3` for all bad
witness triples, including repeated points, while retaining the dense
pieces and uniform Bohr extensions.

All final sources compile in their 59-module closure, and all 27 new and
retained public theorem interfaces pass transitive axiom checks using only
propext, Classical.choice, and Quot.sound. There are 14 new theorems and
three new modules, registered in the facade. The combined audit is pending.
This supplies genuine Bohr extensions, but does not establish the remaining
bilinear structure, bounded-span duality, or printed Theorem 16.2 budget.
No upstream port modules or numbered catalogue claims are added.


The combined Bohr-selection audit now passes: 6,154 public Gowers theorems,
a 4,944-module facade (4,152 OAI modules), and a 4,946-module combined audit
closure. It includes the retained order-eight conclusions, dense selection
invariants, uniform Bohr extensions, all-triples bound, and incoming
Dirichlet character-sum estimate. Only propext, Classical.choice, and
Quot.sound occur. The catalogue remains 115/5 with its fidelity caveats;
this supersedes the pending audit notice for the selection extensions.


### A common Bohr neighborhood for the selection family

`Proofs16Corollary20CommonBohr` unions the individual spectra without
shrinking the radius. `common_bohr_extensions` bounds the common rank by
the sum of the individual rank bounds. `IsBHomomorphism.normalized_extension`
extracts a difference map that vanishes at zero and is additive whenever
its arguments and their sum belong to the neighborhood. Nonempty piece
domains provide the normalization at zero.

`corollary20_common_bohr` combines these facts with the all-triples
selection theorem. Writing `kappa=corollary20Kappa (epsilon/2) K`, its
common spectrum has size at most `(K/kappa+1)*16*kappa^-2`, radius
`kappa/(32*pi)`, and normalized difference maps for every selected piece.
It retains the order-eight property, the density and value-membership
bounds, and fewer than `epsilon*N^3` bad witness triples when
`N >= 8/epsilon`. No floor occurs in the spectrum bound.

The three new theorem declarations compile in a 60-module source closure.
They supply common parameters for the remaining bilinear argument; they
do not discharge bounded-span duality, algebraic regularity, or the deep
structure hypothesis. The combined audit is pending.

The combined audit for the common-neighborhood extension has passed:
6,169 public Gowers theorems, a 4,946-module facade (4,152 OAI modules),
and a 4,948-module combined audit closure. Only propext, Classical.choice,
and Quot.sound occur. This includes the incoming discrete trapezoid
sandwich and supersedes the pending audit notice above. The source
ledger matches the checked 115/5 catalogue, with its existing fidelity
caveats. The port scope check still passes; no upstream modules were added.


### Sharper selection count from the initial covered values

`corollary20_dense_eight_budget` retains the lower potential bound after
the iteration terminates: the covered potential is at least
`N + m*kappa*N` and at most `K*N`. Thus `m*kappa <= K-1`, improving the
previous `m <= floor(K/kappa)+1` conclusion. The initial `N` comes from
the zero value covered at every point. The termination argument and all
density and Freiman invariants remain valid.

`corollary20_bohr_pieces_budget` and
`corollary20_bohr_all_triples_budget` carry this improvement to the Bohr
extensions. `corollary20_common_bohr_budget` consequently reduces the
common spectrum bound from `(K/kappa+1)*16*kappa^-2` to
`((K-1)/kappa)*16*kappa^-2`. The radius, normalized locally additive
difference maps, and exceptional-triple estimate are retained. At `K=1`
the new budget forces the family and its common spectrum to be empty.
The original four theorem interfaces are wrappers around these stronger
results. This is a local quantitative improvement in the Section 16
selection argument; the deep structure hypothesis and the five open
numbered statements remain unresolved.

The combined audit for the tighter selection budget passes: 6,199 public
Gowers theorems, a 4,947-module facade (4,152 OAI modules), and 4,949 modules
including the audit and import-compatibility check. Only propext,
Classical.choice, and Quot.sound occur. All eight new and retained
selection interfaces also pass individual transitive axiom checks. The
audit includes the incoming trapezoid Fourier estimates. The source ledger
remains 115/5 with its existing fidelity caveats, and the selected upstream
module scope is unchanged.


### Bounded Fourier support and the trapezoid L1 bridge

`Proofs16BoundedFrequencySpan` defines the bounded frequency span using
centered coefficients of size at most `R`. Its cardinality is at most
`(2*R+1)^m` for `m` frequencies, including the case where the coefficient
interval wraps around the modulus. A product of finite character sums
expands over these coefficient choices, and its Fourier transform
vanishes outside the span. Consequently an L1 approximation error below
`epsilon*N` forces every Fourier coefficient of size at least
`epsilon*N` into that span. These results work for any finite index type.

`Proofs16TrapezoidL1` proves the actual error bound for the previously
constructed trapezoid product. A [0,1]-valued sandwich has L1 error at
most the cardinality of its boundary band. For the Bohr indicator at
radius `a/N` and the trapezoid with integer smoothing width `c <= a`,
the error is at most `|K|*(4*c+2)` in prime modulus. The finite endpoint
term `2*|K|` is retained.

`large_bohr_fourier_mem_boundedFrequencySpan` combines the two modules.
If the bounded character product approximates the trapezoid product
uniformly within `delta` and
`|K|*(4*c+2) + delta*N < epsilon*N`, then every Bohr Fourier coefficient
of size at least `epsilon*N` lies in the bounded span. The uniform
approximation remains an explicit hypothesis: deriving it from the
inverse-square Fourier decay and controlling the product error is the
remaining analytic step. No bounded-span duality or deep structure
theorem is claimed without that input.

The three new modules contain eight theorem declarations and compile
in a 44-module closure. The numbered catalogue and upstream port scope
are unchanged.

The combined bounded-span audit passes: 6,216 public Gowers theorems,
a 4,950-module facade (4,152 OAI modules), and 4,952 modules including the
audit and import-compatibility check. All eight new theorems also pass
individual transitive axiom checks. Only propext, Classical.choice, and
Quot.sound occur. The source ledger remains 115/5 with the existing
fidelity caveats, and the selected upstream module scope is unchanged.

For the remaining scalar truncation error, Mathlib already supplies
`sum_Ioc_inv_sq_le_sub` and `sum_Ioo_inv_sq_le` in `Analysis/PSeries`.
Combining the centered-frequency multiplicity bound of two with these
finite inverse-square tail bounds and `fourier_trapezoid_le` is the next
concrete analytic step. The product error must then be controlled before
applying the new large-coefficient bridge.


### Uniform truncation and an explicit bounded-span cutoff

The uniform approximation hypothesis in the previous bounded-span bridge
has now been discharged. `Proofs16FourierTail` uses the incoming
centered-frequency multiplicity lemma and Mathlib's finite inverse-square
tail bound to obtain `sum_{|r|>R} |r|^-2 <= 4/(R+1)` for every natural
cutoff, including zero. The incoming positive-cutoff `2/R` estimate is
also retained.

`Proofs16UniformTruncation` defines the actual centered Fourier truncation.
Fourier inversion bounds its error by the normalized omitted Fourier
mass. Applying the trapezoid decay gives the uniform error
`eta = N/(|I_c|*(R+1))` when `2a<N` and `2c<N`.

`Proofs16ProductApproximation` proves a finite product error bound
`(1+eta)^|K|-1`, and applies it to the explicit truncated Fourier
coefficients. `large_bohr_fourier_mem_boundedSpan_of_budget` therefore
needs only a numerical total-error inequality; it has no approximation
or structure hypothesis.

`Proofs16BohrSpectrumBudget` proves `(1+eta)^m-1 <= 2m*eta` when
`m*eta <= 1/2`. For `0<epsilon<=1`, the explicit cutoff
`R=ceil(8*(|K|+1)*N/(epsilon*|I_c|))` makes the product error at most
`epsilon/4`. If `c<=a`, `2a<N`, `2c<N`, and
`|K|*(4c+2) <= (epsilon/2)*N`, then every Fourier coefficient of the
Bohr indicator at radius `a/N` with magnitude at least `epsilon*N`
belongs to the bounded span with this cutoff. Its cardinality is bounded
by the already proved `(2R+1)^|K|`. This retains the finite endpoint
condition and is not a claim about arbitrarily small epsilon at fixed N.

These four new modules contain ten theorem declarations and compile in
a 49-module source closure. The remaining Section 16 structure work
includes the Bohr-sum containment and bounded-span selection argument,
algebraic regularity, quasirandomness, and the final difference-set
composition. No numbered statement or deep hypothesis is marked closed
by this analytic milestone.

The combined explicit-cutoff audit passes: 6,241 public Gowers theorems,
a 4,955-module facade (4,152 OAI modules), and 4,957 modules including the
audit and import-compatibility check. All ten new theorems also pass
individual transitive axiom checks. Only propext, Classical.choice, and
Quot.sound occur. Incoming Fourier inversion and positive-cutoff tail
results are included. The source ledger remains 115/5 with its existing
fidelity caveats, and the selected upstream module scope is unchanged.


### Polynomial large-spectrum cutoff independent of the modulus

`Proofs16PolynomialSpectrumSpan` removes the modulus from the coefficient
cutoff. For `k=|K|+1`, `0<rho<1/2`, `0<epsilon<=1`, and
`N >= 8*k/epsilon`, every Fourier coefficient of the Bohr indicator
`B(K;rho)` with magnitude at least `epsilon*N` belongs to the bounded
span with cutoff

`ceil(max(8*k/(epsilon*rho), 128*k^2/epsilon^2))`.

The proof chooses `sigma=min(rho,epsilon/(16*k))`,
`a=floor(rho*N)` and `c=floor(sigma*N)`. The original Bohr set equals
the one at grid radius `a/N`. Its boundary-band error satisfies the
previous budget, including endpoints. A non-wrapping centered interval
has at least `c+1` points, so `|I_c| >= sigma*N` even when `c=0`.
This cancels the modulus from the explicit cutoff. Monotonicity of the
bounded frequency span then gives the displayed common cutoff. Using
the maximum, rather than the sum of its two terms, avoids an unnecessary
additional loss. The finite-size hypothesis is still required.

The four new theorem declarations compile in a 50-module source closure.
This completes the quantitative large-spectrum inclusion needed in the
Fourier route to bounded-span duality. Bohr-sum containment, the subsequent
bounded-span selection, algebraic regularity, quasirandomness and the
final difference-set composition remain separate work; no numbered
statement is closed by this result.

The combined polynomial-cutoff audit passes: 6,254 public Gowers
theorems, a 4,956-module facade (4,152 OAI modules), and 4,958 modules
including the audit and import-compatibility check. All four new theorems
also pass individual transitive axiom checks. Only propext,
Classical.choice, and Quot.sound occur. The source ledger remains 115/5
with its existing fidelity caveats, and the selected upstream module
scope is unchanged.


### Mixed Bogolyubov and Bohr-sum containment

`Proofs16MixedCorrelation` develops the mixed fourfold correlation of
`A` and `B`. Its Fourier weights are `|Ahat(r)|^2*|Bhat(r)|^2`, which are
nonnegative. Fourier inversion gives the total-weight formula at zero,
the zero-frequency lower bound `|A|^2*|B|^2/N`, and the weighted phase
bound for displacement. A nonzero mixed correlation yields an actual
representation in `(A-A)+(B-B)`.

`Proofs16MixedSpectrum` bounds the Fourier mass outside the intersection
of large spectra at threshold `tau*N` by
`tau^2*N^3*(|A|+|B|) <= 2*tau^2*N^4`. This follows from Parseval and
the fact that at least one factor is small outside that intersection.

`mixed_bogolyubov` uses `tau=|A||B|/(4*N^2)` for nonempty sets. A point
in the Bohr set of the common large spectrum at radius `1/(4*pi)` has
phase error at most `1/2` there. The exceptional Fourier mass is small
enough to keep the mixed correlation nonzero, so the point lies in
`(A-A)+(B-B)`. This part works for every nonzero modulus.

`Proofs16BohrSumSpan` applies this to the half-radius sets
`A=B(K;rho/2)` and `B=B(L;sigma/2)`. Their differences lie in the original
Bohr sets. In prime modulus, with `0<rho,sigma<1` and
`N >= 8*(|K|+1)/tau`, `N >= 8*(|L|+1)/tau`, the polynomial large-spectrum
theorem puts the common spectrum in the intersection of the two bounded
frequency spans. The Bohr set of this intersection, at radius `1/(4*pi)`,
is therefore contained in `B(K;rho)+B(L;sigma)`. The two coefficient
cutoffs are `polynomialSpectrumCutoff |K| (rho/2) tau` and its L/sigma
counterpart. The threshold uses the actual half-radius cardinalities;
the finite-size conditions remain explicit.

The four new modules contain seventeen theorem declarations and compile
in a 54-module closure. All declarations pass individual transitive axiom
checks using only propext, Classical.choice, and Quot.sound. This is an
actual Bohr-sum containment result under its stated numerical conditions;
the bounded-span selection, algebraic regularity, quasirandomness, and
final structure composition remain unfinished. No numbered catalogue
statement is marked closed by this step.

The combined mixed Bohr-sum audit passes: 6,283 public Gowers theorems,
a 4,960-module facade (4,152 OAI modules), and 4,962 modules including the
audit and import-compatibility check. All seventeen new declarations
also pass individual transitive axiom checks. Only propext,
Classical.choice, and Quot.sound occur. The source ledger remains 115/5
with its existing fidelity caveats, and the selected upstream scope is
unchanged.


### Removing finite-size assumptions and actual-density parameters

`Proofs16UniformSpectrumSpan` removes the lower bound on N from the
polynomial large-spectrum theorem. When N is below the former threshold,
the same polynomial cutoff is at least N/2. Its coefficient interval then
contains every residue. A nonzero defining frequency spans the prime
field, so inclusion is immediate. If all defining frequencies are zero,
the Bohr set is the full group and its nonzero Fourier coefficients
vanish. This handles the remaining case without discarding endpoint errors
in the large-modulus proof.

`large_bohr_fourier_mem_uniform_boundedSpan` consequently holds for every
prime modulus, with the same polynomial cutoff and `0<rho<1/2`,
`0<epsilon<=1`. `bohr_sum_contains_span_intersection_uniform` removes
both finite-size assumptions from the previous Bohr-sum theorem. The
previous interfaces and proofs remain available.

`Proofs16BohrSumUniformParameters` then removes actual Bohr cardinalities
from the cutoff. The Dirichlet-cell lower bound gives
`tau >= 1/(4*M^|K|*P^|L|)` when `rho*M >= 2` and `sigma*P >= 2`.
The polynomial cutoff is antitone in the Fourier threshold, so this lower
threshold supplies uniform larger spans. Choosing `M=ceil(2/rho)` and
`P=ceil(2/sigma)` yields `bohr_sum_contains_radius_controlled_span`: for
all prime moduli and `0<rho,sigma<1`, the Bohr set of the intersection of
these two bounded spans, at radius `1/(4*pi)`, lies in
`B(K;rho)+B(L;sigma)`. Its cutoffs depend only on the ranks and radii.
There is no finite-size or actual-density hypothesis.

The two new modules contain twelve theorem declarations and compile in
a 57-module source closure. This strengthens the verified Bohr-sum input
to the remaining bounded-span selection and algebraic-regularity argument;
it does not close the five remaining numbered statements or their deep
structure dependency.

The combined uniform Bohr-sum audit passes: 6,301 public Gowers theorems,
a 4,962-module facade (4,152 OAI modules), and 4,964 modules including the
audit and import-compatibility check. All twelve new declarations also
pass individual transitive axiom checks. Only propext, Classical.choice,
and Quot.sound occur. The source ledger remains 115/5 with its existing
fidelity caveats, and the selected upstream module scope is unchanged.


### J.80. Dense-row alphabets and directional containment

`Proofs16BohrSumRankCap` supplies one Bohr-sum cutoff for all pairs of
spectra with a common rank cap. The Fourier threshold decreases with the
rank cap and the polynomial cutoff increases with it. Consequently the
same coefficient interval can be used for every row in the selection step.

`Proofs16BoundedSpanAlgebra` proves bounded-span symmetry and the inclusion
`Span_R(K union L) subset Span_R(K) - Span_R(L)`. Assigning the overlapping
frequencies entirely to K avoids increasing R. These are actual finite
spans with centered modular coefficients, including when R exceeds N/2.

`Proofs16DirectionalBohrSpan` puts `U_y = Span_R(Gamma_y)`. If each Gamma_y
has rank at most r, then every U_y contains zero and has cardinality at
most `(2R+1)^r`. For four rows y+z,z,y+w,w in Y, the Bohr set of
`(U_(y+z)-U_z) intersect (U_(y+w)-U_w)` at radius `1/(4*pi)` lies in row y
of `D_hor D_ver A`, provided the rows of A contain `B(Gamma_y;rho)`.
The uniform cutoff is
`R = polynomialSpectrumCutoff (2r) (rho/2) (1/(4*M^(2r)*M^(2r)))`,
where M is positive and `rho*M >= 2`. No lower bound on the prime modulus
is needed.

`Proofs16DenseRowAlphabets` discharges the row-Bohr premise for an original
set A whose rows in Y have density at least delta>0. Row Bogolyubov gives
`r=ceil(16*delta^(-2))` and `rho=1/(8*pi)`; empty spectra are assigned
outside Y. The resulting alphabet family satisfies the selection theorem's
zero and size conditions, and its common row-difference Bohr sets lie in
`D_hor D_ver D_hor D_hor A`. This supplies the geometric input to selection;
it does not yet prove the subsequent algebraic regularity or the remaining
five numbered statements. The four modules contain eleven new theorem
declarations, checked in a 63-module source closure.

### Quarter-radius mixed Bogolyubov (2026-10-08)

`Proofs16SpectrumPairSumset` sharpens `mixed_bogolyubov` and the
Bohr-sum containment of `Proofs16BohrSumSpan` in two constants.
- The radius is `1/4` instead of `1/(4*pi)`, matching [49]'s Theorem 27.
  The improvement comes from the real part: on `B(S;1/4)` every
  character in `S` has nonnegative real part (`re_exponential_nonneg`),
  so the terms in `S` need no phase-error bound at all.
- The threshold is `|A||B|/(2N^2)`, twice `tau`. The budget needed is
  `eps^2*N^3*(|A|+|B|) < |A|^2*|B|^2` (`quarter_threshold_budget`). The
  bounded-span cutoff `128(m+1)^2/eps^2` therefore shrinks by a factor
  of four.

Results:
- `sumset_contains_bohr_of_spectrum_pair`: for any `S` that contains
  every frequency at which both transforms are at least `eps*N`,
  `B(S;1/4)` lies in `(A-A)+(B-B)` under the budget above.
- `mixed_bogolyubov_quarter`: the instance where `S` is the common
  large spectrum at threshold `|A||B|/(2N^2)`.
- `bohr_sum_of_common_spectrum_quarter` and
  `bohr_sum_contains_span_intersection_quarter`: the two
  `Proofs16BohrSumSpan` containments at radius `1/4` and threshold
  `2*bohrSumThreshold`. The finite-size conditions are the same as
  before, with the threshold doubled.

Supporting lemmas:
- `norm_sq_fourier_indicator`: `|Ahat|^2` as a double character sum.
- `sum_exponential_mul_eq_ite`: orthogonality, via
  `AddChar.sum_mulShift`.
- `sum_weight_exponential`: the weighted character sum counts
  representations, with exact multiplicity `N`.
- Parseval is the corpus's `indicator_fourier_energy`.

An earlier draft carried an N-dependent cutoff variant of Theorem 27.
It was dropped because the modulus-independent
`Proofs16PolynomialSpectrumSpan` cutoff supersedes it. All nine theorems
use only propext, Classical.choice, and Quot.sound. The collision gate
passes. No numbered statement changes status.


The combined audit after merging the quarter-radius proofs and the dense-row
alphabet construction passes: 6,326 public Gowers theorems, a 4,967-module
facade (4,152 OAI modules), and 4,969 modules including the audit and import
compatibility check. All eleven new directional declarations also pass
individual transitive axiom checks. Only propext, Classical.choice, and
Quot.sound occur. The source ledger remains 115/5 with the existing fidelity
caveats; the selected upstream closure and provenance are unchanged.
The quarter-radius improvement has not yet been propagated through the
uniform rank-cap and directional-alphabet interfaces.


### J.81. Quarter-radius dense-row selection

`Proofs16UniformQuarterBohrSum` propagates the quarter-radius improvement
through the uniform large-spectrum theorem. The actual mixed threshold is
at most 1/4, so twice this threshold remains in the permitted interval.
`bohr_sum_contains_span_intersection_uniform_quarter` removes both
finite-modulus restrictions from the incoming quarter-radius theorem.
`bohr_sum_contains_rank_cap_span_quarter` uses the doubled uniform lower
threshold `2/(4*M^r*M^r)` for any pair of ranks at most r.

`Proofs16QuarterRowAlphabets` carries this into the directional construction.
The common-difference Bohr radius is 1/4 rather than 1/(4*pi), and
`directionalQuarterSpanCutoff_le` verifies that the coefficient cutoff
never increases. Before taking the maximum and ceiling, doubling the
threshold divides the linear cutoff term by two and the quadratic term
by four. The dense-row input is proved for every prime modulus.

`Proofs16SelectedRowBohr` supplies the geometric consequence of selection.
Without a bad witness, every common row difference is in the sum of the
two covered difference sets. Four selected row spectra at radius 1/16
therefore control the entire common-difference spectrum at radius 1/4.
Their union has at most 4m frequencies, even though the underlying row
alphabets can be much larger. The zero values in the covered sets require
no additional frequencies.

`Proofs16DenseRowSelection.dense_row_selected_bohr` applies this to the
original set A. For rows in Y of density at least delta>0, set
`r=ceil(16*delta^(-2))`, `R=directionalQuarterSpanCutoff r 64 (1/(8*pi))`,
`K=(2R+1)^r`, and `kappa=corollary20Kappa (epsilon/2) K`.
The fixed cell count 64 satisfies the radius condition by pi<4.
For epsilon>0 and N>=8/epsilon, there are m selected pieces and fewer than
epsilon*N^3 exceptional triples, with `m*kappa <= K-1`. Every piece has
size at least kappa*N, is Freiman of order eight, and retains its Bohr
extension with rank at most `16*kappa^(-2)` and radius `kappa/(32*pi)`.
For every nonexceptional triple whose four rows are in Y, the Bohr set of
its at most 4m selected values at radius 1/16 lies in row y of
`D_hor D_ver D_hor D_hor A`. All parameters depend only on delta and epsilon.

The four modules contain twelve theorem declarations, checked in a
91-module source closure and individually audited for transitive axioms.
This connects the previously separate geometric and selection arguments.
The later algebraic-regularity argument and the five open numbered
statements remain unresolved; the catalogue fidelity caveats still apply.


The completed combined audit checks 6,347 public Gowers theorems in a
4,971-module facade (4,152 OAI modules), and 4,973 modules including the
audit and import-compatibility check. Only propext, Classical.choice, and
Quot.sound occur. A full disk interrupted the first audit artifact write;
after clearing redundant package caches, the artifact was rebuilt and the
import check passed. The source ledger remains 115/5 and the selected
upstream module scope is unchanged. No ported sources or license notices
were changed.


### J.82. A common neighborhood and dense recentering

`Proofs16DenseRowCommonBohr.dense_row_common_bohr` puts the actual maps
selected from the original set on a common Bohr neighborhood. With K and
kappa from J.81, its rank is at most `((K-1)/kappa)*16*kappa^(-2)` and its
radius is `kappa/(32*pi)`. All normalized difference maps vanish at zero,
are Freiman of order two there, and are additive whenever both arguments
and their sum stay in the neighborhood. The earlier directional containment,
4m rank bound for selected triple spectra, and exceptional-triple count
are retained for the same maps and pieces.

`Proofs16BohrRecentering` proves an exact translation-average identity:
for finite E,B in Z/N, the sum over t of `|{x in B : t+x in E}|` is
`|E|*|B|`. Hence a set of density at least kappa retains at least
`kappa*|B|` points in some translate of B. Taking B to be the half-radius
common Bohr set and choosing one retained point as center gives a cluster
C inside E with all pairwise differences in the full-radius neighborhood.
Its size is at least kappa times the half-radius Bohr cardinality. For
any positive integer M with `rho*M >= 2`, the verified Dirichlet bound
also gives ambient density at least `kappa/M^|Gamma|` for that cluster.

`IsBHomomorphism.dense_recenter` writes a Bohr-extended map on this cluster
as `f(x)=f(a)+psi(x-a)`, with psi normalized and locally additive.
`Proofs16DenseRowRecentered.dense_row_common_bohr_recentered` does this for
every selected piece while preserving the very same common maps psi,
the original maps L, and their directional containment. It does not
replace L outside the retained cluster or assert that the entire Bohr
translate lies inside E. No additional rank or radius loss is introduced.

The three modules contain seven theorem declarations, checked in a
97-module source closure. This establishes the common-neighborhood and
cluster recentering input. The simultaneous choice of index patterns,
algebraic regularity, quasirandomness and subsequent directional steps
remain to be proved; no numbered statement changes status.


The combined recentering audit passes: 6,355 public Gowers theorems,
a 4,974-module facade (4,152 OAI modules), and 4,976 modules including
the audit and import-compatibility check. The seven new declarations
also pass individual transitive axiom checks. Only propext,
Classical.choice, and Quot.sound occur. The source ledger remains 115/5
with its existing fidelity caveats; upstream module scope and licenses
are unchanged.


### J.83. Small generators by dissociation, with unit coefficients

The next selection step requires a small set of actual row generators.
Reference [49], Section 7, uses its Theorem 31 before averaging over four
index patterns (Claim 36): https://arxiv.org/html/2109.03093#S7.
The following independent counting proof supplies this input on Z/N.

For any B inside `Span_R(K)`, `boundedSpan_small_generators` produces
`D subset B` such that `B subset Span_1(D)` and
`|D| <= ceil(16*|K|^2 + 4*|K|*log(2R+1))`.
This includes empty B, rank zero, zero cutoff, and every nonzero modulus;
primality is unnecessary. In particular the new generators are values
of the original set and every coefficient has centered size at most one.

`Proofs16SpanSumCounting` proves the counting estimate. If D is
additively dissociated, all of its subset sums are distinct. Adding at
most |D| points of `Span_R(K)` places those sums in `Span_(|D|R)(K)`.
Thus `2^|D| <= (2|D|R+1)^|K|`. `Proofs16SmallSpanGenerators` solves this
inequality explicitly: take logarithms, use `log 2 >= 1/2` and
`log d <= 2 sqrt(d)`, and absorb the square-root term using
`(sqrt(d)/2-2k)^2 >= 0`. This yields `d <= 16k^2+4k log(2R+1)`.
Mathlib's `Finset.exists_subset_addSpan_card_le_of_forall_addDissociated`
then supplies a maximal dissociated generating subset. The proof uses
Mathlib through imports; no new upstream files are ported.

`Proofs16BoundedSpanPhase` proves the matching phase bound: Bohr control
at radius rho on k generators controls their R-bounded span at radius
k*R*rho. The proof uses submultiplicativity and subadditivity of the
centered modular absolute value, including cutoffs above N/2.

`Proofs16SmallCoverIndices` applies this to the covered values of the
actual bounded-span row alphabets. It chooses at most
`ell=spanGeneratorBound r R` indices at each row. Every chosen index is
active: the row is in the selected piece and its map value is in the
row alphabet. These values span all covered values with unit coefficients.
The index lift discards zero before choosing indices, so zero costs no
index and requires no domain-membership assertion.
`covered_values_small_bohr` gives Bohr control of all covered values at
radius 1/16 from the chosen values at radius `1/(16*max(1,ell))`.
This replaces a dependence on all m selected maps by the explicit small
rank ell, without a large coefficient factor in the radius.

The four modules contain fourteen theorem declarations and compile in a
95-module closure. The subsequent averaging over four index patterns and
the final structure theorem are not yet proved. No numbered statement
changes status, and the existing paper-fidelity caveats remain in force.


The combined small-generator audit passes: 6,373 public Gowers theorems,
a 4,978-module facade (4,152 OAI modules), and 4,980 modules including the
audit and import-compatibility check. All fourteen new declarations also
pass individual transitive axiom checks. Only propext, Classical.choice,
and Quot.sound occur. The source ledger remains 115/5 with its existing
fidelity caveats. The selected upstream module closure and license notices
are unchanged.


### J.84. Fixed small patterns and quantitative row fibers

`Proofs16SmallIndexPatterns` bounds the number of subsets of [m] having
size at most ell by `(m+1)^ell`. Its induction removes one element from
a nonempty set and uses an optional index to reconstruct it. This counts
variable-size patterns directly; no inactive selected-map indices are
added to make patterns have equal cardinality.

`Proofs16IndexPatternAveraging` labels each triple by its four index sets
and its two offsets z,w. A maximal fiber has
`|T| <= (m+1)^(4ell) * N^2 * |V|`. Projection onto the remaining row
parameter is injective on the fiber because z,w are fixed. All four
index-set equalities are retained pointwise on V.

`Proofs16GoodRowTriples` supplies the triple count for an actual row set Y.
The pair-offset fibers have total size |Y|^2, and admissible quadruple
triples are counted by their squared sizes. Cauchy-Schwarz gives
`|Y|^4 <= N * |rowQuadrupleTriples Y|`. If `|Y|>=beta*N` and an exceptional
set B has size at most epsilon*N^3, the retained triples have size at least
`(beta^4-epsilon)*N^3`. Combining this with pattern averaging yields
`(beta^4-epsilon)*N <= (m+1)^(4ell)*|V|`.

`Proofs16PatternBohrContainment` proves that the four covered-row Bohr
conditions at radius 1/16 control every common difference at radius 1/4
on a nonexceptional triple. The chosen small patterns supply those four
conditions, and their union has at most 4ell frequencies.

`Proofs16FixedBohrPatterns.dense_row_fixed_bohr_patterns` applies all of
this to the original set A. Use the density parameters delta for each
row in Y and beta for Y itself; epsilon>0 requires N>=8/epsilon.
With r,R,K,kappa from J.81 and `ell=spanGeneratorBound r R`, the theorem
produces the selected order-eight Freiman pieces (including their density
and individual Bohr extensions), four fixed index sets J, fixed z,w, and
V with the density bound above. For every y in V all chosen map evaluations
are inside their original selected pieces, and the Bohr set of the at most
4ell resulting frequencies, at radius `1/(16*max(1,ell))`, lies in row y
of `D_hor D_ver D_hor D_hor A`. When epsilon<beta^4 the bound forces V to
be nonempty. This supplies the fixed-pattern geometry corresponding to
Claim 36 on prime cyclic groups, with the explicit bounds proved here.

The five modules contain fifteen theorem declarations and compile in a
101-module closure. The later common-domain construction and algebraic
regularity remain open, as do the five numbered catalogue entries.
No paper-fidelity caveat or deep structural hypothesis is discharged by
this intermediate result.

### Quasirandom bipartite graphs: [49] Appendix B (2026-10-09)

`Proofs16BipartiteQuasirandom` formalizes Lemmas 41 and 43 of [49]
(Lemma 42 is a special case), read from the published PDF (Discrete
Analysis 2024:20, pp. 37-40). Everything works for arbitrary finite
vertex classes `X`, `Y` and arbitrary finite index types `I` (the
`k` vertices) and `J` (the `m` coordinates). Nothing is specific to ℤ/N.

- `boxSum f = Σ_{x₀,x₁} (Σ_y f(x₀,y) f(x₁,y))²` is the unnormalized
  fourth power of the box norm. [49]'s `‖G−δ‖□ ≤ ε` is
  `boxSum (G−δ) ≤ ε⁴|X|²|Y|²`, so no fourth roots appear.
- Lemma 41, `box_correlation_pow_four_le`:
  `(Σ f u v)⁴ ≤ (Σu²)²(Σv²)²·boxSum f`, by Cauchy–Schwarz over `y` and
  then over pairs `(x₀,x₁)`.
- Lemma 41, `abs_box_correlation_le`: the bounded form, giving
  correlation at most `ε|X||Y|` when `|u|, |v| ≤ 1`.
- `box_swap_bound`: one edge of a product pattern. The variables are
  split with `Equiv.funSplitAt`. Factors that do not involve both
  `x i₀` and `w j₀` are then functions of one variable, so Lemma 41
  applies.
- `bipartite_counting`: the telescoping of [49]'s "repeat 2km−1 times",
  done as induction over the set of edges kept from `G` (`edgeSum`). For
  weights `0 ≤ W ≤ 1`, `Σ_{x,w} W(w) Π G(x i, w j)` is within
  `|I||J|ε|X^I||Y^J|` of `δ^{|I||J|}|X^I|Σ_w W(w)`.
- Lemma 43, `common_neighbourhood_second_moment`:
  `Σ_x (C(x) − δ^{km}|M|)² ≤ 4kmε|X^k||Y^m|²`, exactly [49]'s bound.
  Here `C(x)` is the number of `m`-tuples of `M` inside the common
  neighbourhood of `x`. The square is a count over `J ⊕ J`
  (`commonCount_sq`), and both the first and second moments come from
  `bipartite_counting`.
- Lemma 43, `common_neighbourhood_deviation_card`: Markov. At most
  `4kmεη⁻²|X^k|` tuples deviate by `η|Y^m|`, stated as
  `#·η² ≤ 4kmε|X^k|`. It needs `η ≥ 0`: for negative `η` the filter is
  everything, and the statement would be false.

All 18 theorems and 3 definitions use only the standard axioms. The
collision gate passes. No numbered statement changes status. This
supplies the quasirandomness input of [49]'s Claim 38 (step 4 of
Theorem 35).

**Lemma 44, sharpened (`Proofs16OneSidedQuasirandom`).** [49] Lemma 44
assumes degree control (19) and codegree control (20) at level `ε`. It
concludes `3ε^{1/8}`-quasirandomness via Markov on good pairs and the
box-norm triangle inequality. A direct argument does better. With
`f = G − δ`, the row correlation is
`c(x,x′) = (codeg − δ²|Y|) − δ(deg x − δ|Y|) − δ(deg x′ − δ|Y|)`
(`codegree_correlation_eq`), and `|c| ≤ |Y|` because `|f| ≤ 1`. Then
`c² ≤ |Y|·|c|`, and summing over pairs gives
`boxSum (G − δ) ≤ 3ε|X|²|Y|²` (`boxSum_le_of_codegrees`). So
`‖G − δ‖□ ≤ (3ε)^{1/4}`, with respect to the given `δ`; neither Markov
nor the triangle inequality is needed.
- `total_mass_sub_le_of_degrees` is the density part, `|δ′ − δ| ≤ ε`.
- `common_neighbourhood_deviation_of_codegrees` chains this into
  Lemma 43. Degree and codegree control alone bound the number of
  atypical `I`-tuples by `4|I||J|(3ε)^{1/4}η⁻²|X^I|`.

Four theorems, standard axioms only, collision gate clean.


The combined audit after merging the fixed-pattern and quasirandomness
work passes: 6,422 public Gowers theorems, a 4,984-module facade
(4,152 OAI modules), and 4,986 modules including both audits. The fifteen
new fixed-pattern declarations also pass individual transitive axiom
checks. Only propext, Classical.choice, and Quot.sound occur. The source
ledger remains 115 companions and five open statements, with all prior
fidelity caveats retained. No additional upstream modules were ported,
and the selected dependency closure and Apache provenance are unchanged.


### J.85. Simultaneous pattern recentering from global density

`Proofs16SelectedCommonBohr` takes a common spectrum over only a chosen
set I of maps. If each individual spectrum has rank at most Q, the common
rank is at most |I|Q. A single dense cluster of a parameter set V works
for every chosen map: its pairwise differences lie in the common Bohr
neighborhood, and each normalized difference map remains order-two
Freiman, vanishes at zero, and is locally additive there. Agreement with
the original maps is retained for all eligible original-domain pairs.

`Proofs16PatternRecentering.fixed_patterns_recentered` applies this to
I=J(0) union J(2), the two varying index sets from J.84. On a common
cluster C with anchor a, both L_i(y+z) and L_i(y+w) split as their values
at the corresponding anchor plus psi_i(y-a). The centered set W=C-a
contains zero and lies in B(T;rho). If V has density nu, then
`|W| >= nu * |B(T;rho/2)|`. The common rank is at most 2ell*Q.
The original pattern's Bohr condition follows from the separate
half-radius conditions on at most 4ell constant frequencies and at most
2ell varying frequencies. No claim that a translate of the whole
neighborhood lies inside an original selected domain is used.

`Proofs16DenseRowPatternRecentering` combines this with the actual dense
row construction. Here Q=16*kappa^(-2), rho=kappa/(32*pi), and
`nu=(beta^4-epsilon)/(m+1)^(4ell)`, with epsilon<beta^4. For t in W,
annihilating the constant and varying frequencies at radius
`1/(32*max(1,ell))` puts (d,a+t) in `D_hor D_ver D_hor D_hor A`.
The small active family, rather than all m maps, determines the common
rank. The individual map domains are handled by their actual membership
conditions on V and by the common difference neighborhood.

`Proofs16DenseRowExtraction` proves the exact first-moment row bound:
if |A|>=alpha*N^2 and theta<1, rows of density at least theta have
density at least `(alpha-theta)/(1-theta)`. At theta=alpha/2 this gives
`beta=alpha/(2-alpha)`, improving the usual alpha/2 row-set bound.
`Proofs16GlobalPatternGeometry.global_recentered_patterns` consequently
starts only from global density, 0<alpha<=1, and N>=8/epsilon, where
0<epsilon<(alpha/(2-alpha))^4. No dense-row set or independent row-density
hypothesis remains in this theorem.

The five modules contain ten theorem declarations and compile in a
110-module closure. This proves the common normalized Bohr geometry and
its quantitative density inputs. It does not establish the later proper
progression construction, algebraic regularity, or the final bilinear
structure theorem. Five numbered catalogue entries remain open, and all
existing paper-fidelity caveats remain applicable.


The merged audit passes: 6,452 public Gowers theorems in a 4,990-module
facade (4,152 OAI modules), and 4,992 modules including both audits.
All ten declarations from J.85 also pass individual transitive axiom
checks. Only propext, Classical.choice, and Quot.sound occur. The source
ledger remains 115 companions and five open statements. The incoming
one-sided quasirandomness estimates are included in this audit. No
upstream dependency or provenance changes are needed.

For the next structural step, [reference 49, Theorem 33 and Claim 37]
(https://arxiv.org/html/2109.03093) use a proper progression and maps
defined on its fourfold enlargement. The current theorem supplies a
common Bohr domain, but does not yet provide that progression. A useful
intermediate extension is to choose the parameter cluster in a smaller
neighborhood while retaining the maps on the original neighborhood,
so that the required sums remain within their domains. The degree and
codegree estimates alone do not prove the algebraic regularity input.


### J.86. Separate domain radii and four-row completion

`selected_common_bohr_cluster_radius` separates the radius sigma used
for the parameter cluster from the radius rho used for the normalized
map domains. `fixed_patterns_recentered_radius` propagates this distinction
when 0<=sigma<=rho. Both preceding equal-radius theorems remain available
as specializations. This ensures that choosing a smaller parameter set
does not discard the maps' larger domains.

`Proofs16QuarterPatternGeometry` takes sigma=rho/4 in the actual dense-row
and global-density constructions. The centered set W now lies inside
B(T;rho/4), while all active maps remain normalized order-two Freiman
maps on B(T;rho). Its size is at least nu*|B(T;rho/8)|, with nu as in
J.85. All frequency-rank bounds and the global-density input are retained.

`Proofs16BohrFourTerm` proves the corresponding domain arithmetic. Four
points of B(T;rho/4) have alternating sum in B(T;rho). The two pair sums
lie in the half-radius neighborhood, so the Freiman identities can be
applied with all arguments in B(T;rho). Hence a normalized map satisfies
`psi(x1+x2-x3-x4)=psi(x1)+psi(x2)-psi(x3)-psi(x4)` for these inputs.
The phase-error estimate accounts explicitly for all four signs.

`Proofs16FourRowCompletion` proves the geometric implication needed for
the later common-neighborhood argument. If y=x1+x2-x3-x4 with all xj in W,
and d annihilates the variable frequencies at x1,x2,x3 and y to radius
eta/4, it annihilates those at x4 to radius eta. Together with the constant
frequency condition, all four points (d,a+xj) therefore lie in the target
set. Two vertical differences cancel the anchor a and give (d,y).
The triple-witness version sets x4=x1+x2-x3-y and retains its W-membership
as an explicit hypothesis.

`Proofs16GlobalFourRowCompletion.global_four_row_completion` combines
this implication with the construction from global density. It yields
(d,y) in `D_ver D_ver D_hor D_ver D_hor D_hor A` when an actual triple
witness exists. This is a six-operator membership implication, not an
unconditional variety-containment theorem. Producing witnesses with
the required uniformity still needs the regularity and representation
arguments; the final horizontal difference step also remains.

There are thirteen new theorem declarations and two preserved wrappers.
The 114-module source closure compiles. The proper-progression and
algebraic-regularity inputs remain open, as do the five numbered entries
in the source ledger. No existing paper-fidelity caveat is removed.


### Bohr-set size from linear relations: [49] Proposition 23 (2026-10-09)

`Proofs16BohrSizeRelations` proves [49]'s Proposition 23 in `ℤ/N`.
Algebraic regularity (Theorem 33, Claim 34) runs on this formula, so it
is the next input after the quasirandomness appendix.

Let the frequencies be a tuple `γ : ι → ℤ/N`; repeats are allowed, as in
Claim 34's families `Γ ∪ {L₁(y), …, L_r(y)}`. Let
`c_r = N⁻¹·ĝ(r)` be the trapezoid coefficients
(`trapezoidRelationCoeff a c r`); they depend only on `N, a, c`. Let
`relationWeight γ a c R = Σ_{v ∈ [−R,R]^ι} (Π c_{vᵢ})·1(Σ vᵢγᵢ = 0)`.
Then:
- `bohr_card_approx_relations`: if
  `|B(γ;(a+c)/N)| ≤ |B(γ;(a−c)/N)| + εN` ([49]'s weak regularity (8))
  and the truncation error `(1 + N/(|I_c|(R+1)))^|ι| − 1` is at most `ε`,
  then `|B(γ;(a−c)/N)|` is within `2εN` of `N·relationWeight γ a c R`.
  This is exactly [49]'s `2ε|G|`.
- `bohr_card_approx_relations_explicit`: the same with an explicit
  cutoff `R + 1 ≥ 4(|ι|+1)N/(ε|I_c|)` for `0 < ε ≤ 1`. The cutoff
  depends on `|ι|` and the radii, never on the frequencies.

Supporting results:
- `sum_boundedCharacterProduct`: orthogonality turns the summed
  truncated product into `N` times the relation count.
- `trapezoid_tuple_uniform_truncation`: the tuple form of
  `trapezoid_product_uniform_truncation`.
- `trapezoid_tuple_sum_sandwich`: `|B_in| ≤ Σ_x Π g(γᵢx) ≤ |B_out|`.
- `mem_bohr_image_iff`: Bohr membership for a tuple at grid radii.

Eight declarations, standard axioms only, collision gate clean. No
numbered statement changes status. Next in this lane: Claim 34 (Bohr
sizes are determined by the relation lattice), then the iteration of
Theorem 33.


The combined audit after the four-row work and incoming Bohr-size
relation estimates passes: 6,479 public Gowers theorems, a 4,995-module
facade (4,152 OAI modules), and 4,997 modules including both audits.
The thirteen new declarations and the two equal-radius wrappers also
pass individual transitive axiom checks. Only propext, Classical.choice,
and Quot.sound occur. The numbered source ledger remains 115 companions
and five open statements, with prior fidelity caveats retained. The
selected upstream closure and license/provenance files are unchanged.


### J.87. Missing witnesses and the seventh directional operator

`Proofs16CommonNeighborhoodWitnesses` identifies Boolean common counts
with the cardinalities of the actual witness fibers, including exact
positive-count and zero-count characterizations. If M has relative size
at least tau inside Y^J, the common-neighborhood deviation estimate gives
`missing * (delta^(|I||J|)*tau)^2 <= 4|I||J|*epsilon*|X^I|`.
The threshold is the full predicted count of a zero-count fiber; it is
not halved, avoiding a further factor of four in this missing-count
bound. The single-vertex, triple-witness case is
`missing * (delta^3*tau)^2 <= 12*epsilon*|X|`.

`Proofs16PatternMissingRows` defines the actual Bohr incidence graph and
additive representation triples. Its right vertex class is any nonempty
finite set C, so the theorem applies to pieces obtained from a future
regularity decomposition, not just to the entire parameter neighborhood.
Representation triples have all three coordinates and their fourth
completion in W. The domain bounds on W ensure the four-row argument is
valid, even though the ambient graph class C is arbitrary.

With the explicit box-norm bound and at least tau*|C|^3 representations
of y, the missing part of `B(F union psi_J(y);eta/4)` after two vertical
differences has size D satisfying
`D*(delta^3*tau)^2 <= 12*epsilon*|B(F;eta)|`. The proof injects a missing
point into the graph vertices having no common witness; a common witness
would give precisely the four-row completion proved in J.86.

`Proofs16WeightedBohrFilling` combines weighted defect estimates with the
dense-Bohr difference lemma. If K has rank at most r, 1<=rho*Q, and the
missing points satisfy `D*weight <= loss*N`, then
`4^(r+1)*loss*Q^r <= weight` suffices to cover B(K;rho/2) by differences.
The Dirichlet-cell lower bound removes the actual Bohr cardinality and
modulus from this sufficient error budget.

`Proofs16PatternRowFilling` therefore fills the entire row at radius
eta/8 after the final horizontal difference, assuming
`4^(r+1)*(12*epsilon)*Q^r <= (delta^3*tau)^2` and 4<=eta*Q.
`Proofs16GlobalSevenOperatorCompletion` connects this to the original
global-density construction. The target lies in
`D_hor D_ver D_ver D_hor D_ver D_hor D_hor A`; its frequency rank is at
most 6ell and its radius is `1/(256*max(1,ell))`. The graph domain C may
be any nonempty piece. Graph quasirandomness, positive representation
density, and the numerical error budget remain explicit hypotheses.
They have not been derived from global density, so this is not a proof
of the final structural theorem or a closure of any numbered entry.

The five modules contain eleven new theorem declarations and compile
in a 120-module closure. The remaining work includes finding appropriate
regular pieces and enough representations on them, together with the
proper-progression structure and its quantitative bounds. The five open
numbered statements and all prior fidelity caveats remain unchanged.


### Claim 34's algebraic core in Z/N (2026-10-09)

`Proofs16BohrSizeFactorization`. Suppose
every bounded relation `Σνᵢγᵢ + Σμⱼℓⱼ = 0` splits as "`Σνᵢγᵢ = 0` and
`μ ∈ Λ`", and conversely. Then
`relationWeight (γ ⊔ ℓ) = relationWeight γ · W_Λ`, where
`W_Λ = Σ_{μ∈Λ} Π c_{μⱼ}` (`relationWeight_sumElim_of_split`). With
Proposition 23 on both Bohr sets,
`‖|B(γ ⊔ ℓ)| − W_Λ·|B(γ)|‖ ≤ 2εN + ‖W_Λ‖·2εN`
(`bohr_card_factor_of_split`). This is Claim 34 (i), and (ii) is the
case `κ ⊕ κ`.

[49] writes this with a real `δᵢ` and error `2η/5`. That tacitly
uses `|δᵢ| ≤ 1`, which is not evident from the definition
`δᵢ = Σ_{λ∈Λ} Π c_λ` with complex `c` in the unit disc. The formal
statement therefore keeps `‖W_Λ‖` explicit. Bounding it, for instance
via `|B(γ ⊔ ℓ)| ≤ |B(γ)|` and a lower bound on `|B(γ)|`, is left to the
point of use. Three declarations, standard axioms only.


The merged audit passes for 6,502 public Gowers theorems, a 5,001-module
facade (4,152 OAI modules), and 5,003 modules including both audits.
All eleven new declarations also pass individual transitive axiom
checks. Only propext, Classical.choice, and Quot.sound occur. The source
ledger and selected port scope pass, with 115 companions and five open
statements and all existing fidelity caveats retained. The incoming
relation-weight factorization is included; its norm factor remains
explicit. No upstream dependency or provenance changes were made.

A relevant next input already exists in the selected upstream closure:
`OAI.Combinatorics.Progressions.Fourier.QuarticBohrProgression` provides
`Erdos3.BohrProgression.exists_large_proper_progression_all`. It constructs
a proper centered progression in a cyclic Bohr set with rank at most one
more than its frequency rank and an explicit exponential size bound.
Bridging its Bohr convention and controlling progression dilations remain
to be done; discovering this input is not itself a proof of the missing
progression step. It requires no expansion of the upstream port scope.


### J.88. Actual proper progression geometry from global density

`Proofs16ProperBohrProgression` connects the two Bohr conventions.
The OAI character equals our exponential at the product of frequency and
argument. Jordan's inequality puts the upstream chord-radius Bohr set
of radius rho inside our centered-phase Bohr set of radius rho/4.
The already-ported `OAI.Erdos3.BohrProgression` progression theorem then
gives a proper centered progression Q with rank at most |T|+1 inside
B(T;rho/4), and
`|Q| >= exp(-((|T|+1)*w + 10*(|T|+1)^2))*N`
whenever w>=0 and exp(-w)<=rho. Taking the chord radius min(1,rho)
removes any upper-bound requirement on rho. The proved explicit choice
`w=log(1+rho^(-1))` works for every positive rho. Zero membership and
negation invariance of the progression carrier are also proved.

`Proofs16ProgressionParameterDensity` averages a dense set V on translates
of Q. It produces t and a nonempty W subset Q with t+W subset V,
`|W|>=nu*|Q|`, and the corresponding explicit ambient density bound.
Four-term combinations of Q's points belong to B(T;rho). The proof uses
Q's containment in the quarter-radius Bohr set; it does not assume that
a dilation of a proper progression is itself proper.

`Proofs16CommonProgressionDomain` retains the common normalized Freiman
extensions on the full Bohr domain while choosing that progression.
Original-domain agreement gives affine formulas on the dense translated
part of Q. The translate's center need not belong to any selected domain:
one point of the dense part supplies the reference value, and normalized
Freiman differences supply the correction.

`Proofs16AffinePatternGeometry` keeps at most 4ell constant frequencies
and 2ell varying ones in those affine formulas. The usual half-radius
triangle bound preserves the original directional containment.
`Proofs16FixedPatternProgression` applies this simultaneously to the
two varying fixed-pattern families and retains the density and rank
bounds. All four-term progression combinations lie in the map domains.

`Proofs16GlobalProgressionGeometry.global_proper_progression_geometry`
starts from global alpha-density of A, with the same epsilon and N
hypotheses as J.87. It produces an actual proper symmetric progression,
a nonempty subset W of relative density at least
`nu=(beta^4-epsilon)/(m+1)^(4ell)`, normalized maps on a domain containing
the progression's four-term combinations, and constant/varying Bohr
constraints at radius `1/(32*max(1,ell))` implying
`(d,t+x) in D_hor D_ver D_hor D_hor A` for x in W.
The common spectrum has rank at most `2ell*16*kappa^(-2)`, and the
progression rank is at most one more than that spectrum's actual rank.
This supplies the proper common parameter geometry previously missing
from the constructed fixed-pattern route, with the explicit bounds above.

The six modules contain fourteen new theorem declarations and compile
in a 129-module closure. The OAI progression result and its dependencies
were already part of the selected, licensed density port; no additional
upstream files or modifications are introduced. This does not prove
algebraic regularity, robust representation counts, or the final
structural theorem. It also does not certify the paper's prescribed
numerical or asymptotic bounds. Five numbered entries remain open, and
all existing source-fidelity caveats remain in force.


### Algebraic regularity in prime Z/N: Lemmas 8 and 30 become easy (2026-10-09)

Prime `ℤ/N` with Bohr-set domains removes two of the heavier ingredients
of [49] Theorem 33 (`Proofs16FreimanKernelBohr`).
- **Lemma 8 → Bogolyubov.** Let `f` be Freiman-linear on `B(Ψ;σ)`
  (`IsFreimanLinearOn`, which also covers linear combinations
  `Σ wⱼLⱼ`) and constant on `F ⊆ B(Ψ;σ/4)`, where `|F| = αN`. Then
  `f(x) = f(0)` on all of `B(Spec_α F; 1/(8π))`, and that Bohr set lies
  in `B(Ψ;σ)`. The spectrum has size at most `16α⁻²`
  (`freiman_const_on_bohr_of_dense`). The proof uses three quadruples:
  `b + (a−b) = a + 0`, `c + (e−c) = e + 0` and
  `(a−b) + (e−c) = x + 0`. So the Freiman subgroup step needs no
  coset-progression machinery. The next domain is the Bohr set with
  `Ψ ∪ Spec` adjoined.
- **Lemma 30 → linear algebra.** With coefficients in the field `ℤ/N`,
  the relations of the maps on a domain form a subspace
  (`relationSubmodule`, relative to the values at `0`). It only grows as
  the domain shrinks (`relationSubmodule_anti`). A strictly increasing
  chain of subspaces of `(ℤ/N)^κ` has at most `|κ|` steps
  (`strict_chain_length_le`). This replaces [49]'s
  `O(r²(log r + log K))` lattice-determinant bound by `r`.

Six declarations, all within the standard axioms; the linear-combination
lemma needs only propext and Quot.sound. Collision gate clean. Remaining
for Theorem 33 in this setting:
- the pigeonhole choice of a regular radius ((10)–(12));
- the averaging step, where failure of (i)/(ii) yields one relation
  holding for many pairs;
- the Cauchy–Schwarz passage to triples, and Freiman subtraction to get
  `λ·L(y₁−y₂) = 0`;
- the iteration bookkeeping, at most `r` steps, each multiplying the
  domain rank by a polynomial factor.


The merged audit passes: 6,537 public Gowers theorems, a 5,008-module
facade (4,152 OAI modules), and 5,010 modules including both audits.
All fourteen new progression declarations also pass individual transitive
axiom checks. Only propext, Classical.choice, and Quot.sound occur.
The source ledger and selected port scope pass, preserving 115 companions,
five open statements, and all existing fidelity caveats. The incoming
dense-kernel and relation-subspace results are included in this audit.
The upstream progression code was reused without changes; its existing
Apache license and provenance records remain applicable and unchanged.

After the main push encountered a concurrent update, the box-sum
transposition and right-sided codegree lemmas were merged and the combined
audit rerun. It passes for 6,540 public Gowers theorems in the same
5,010-module closure, with the same three-axiom boundary. No numbered
statement status or selected upstream port scope changed.


### Proposition 23 and Claim 34 with a radius per frequency (2026-10-09)

`global_seven_operator_completion` leaves one input as a hypothesis: box
quasirandomness of the pattern graph between `d ∈ B(F; θ/2)` and
`t ∈ C`, whose edge is `d ∈ B(V(t); θ/8)`. Its degrees and codegrees
are Bohr sets with two radii. So Proposition 23 and the Claim 34
factorization are now stated for per-frequency integer radii.

- `mixedBohr γ a = {x : |γᵢx| ≤ aᵢ}`.
- `relationWeightMixed`, `latticeWeightMixed`: per-index trapezoid
  coefficients.
- `bohr_card_approx_relations_mixed`.
- `relationWeightMixed_sumElim_of_split` and
  `bohr_card_factor_of_split_mixed`, with radii `a` on `Γ` and `b` on
  the maps.

The common-radius theorems are corollaries via `mixedBohr_const`.
`truncation_budget_of_cutoff` isolates the explicit cutoff computation.

In `Proofs16OneSidedQuasirandom`:
- `boxSum_eq_pairs`, `boxSum_transpose`: the box norm is symmetric.
- `boxSum_le_of_codegrees_right`: sharpened Lemma 44, with degree and
  codegree control over the second vertex class. That is the `t`-side in
  the pattern graph, where codegrees are Bohr sets of `F ∪ V(t) ∪ V(t′)`.

Standard axioms throughout; collision gate clean.

Remaining to feed the completion:
- express the pattern graph's degrees and codegrees as `mixedBohr`
  sizes (subtype enumeration of `F`, `bohr_floor_radius` for the real
  radii);
- the relation-splitting hypothesis for most `t`. This is the Theorem 33
  iteration, with `freiman_const_on_bohr_of_dense` and
  `strict_chain_length_le` as its two simplified steps.

### J.89. Robust witnesses on a proper target progression

The representation-count input of J.87 is now constructed from the dense
parameter set. The new modules are `Proofs16RobustCorrelation`,
`Proofs16CorrelationWitnessCount`, `Proofs16RobustPatternRepresentations`,
`Proofs16RobustRowFilling`, and `Proofs16GlobalRobustCompletion`.

For `|W| = αN`, put `τ₀ = sqrt(α³)/4` and
`S = commonLargeSpectrum W W τ₀`. Parseval gives `|S| ≤ 16/α²`.
The mixed Fourier mass outside `S` is at most `α⁴N⁴/8`. For
`y ∈ B(S; 1/(4π))`, the phase error on `S` is at most `1/2`.
The zero-frequency contribution and the triangle inequality therefore give

```
‖mixedDifferenceCorrelation W W y‖ ≥ α⁴ N³ / 4.
```

This is converted to an exact count, without using nonzero correlation
merely as an existence witness. The correlation coordinates `(t,x,z)`
are in bijection with the triples `(x,z-(t-y),z)`. Their fourth point is
`x-t`. For every containing class `W ⊆ C`, this identifies the correlation
norm with `|(patternRepresentationTriples W C y)|`.

The stronger class-relative witness density is retained:

```
robustRepresentationDensity α C = α⁴ N³ / (4 |C|³).
```

It is positive when `α > 0` and `C` is nonempty, and at least `α⁴/4`.
Compared with replacing `|C|` by `N`, this retains a factor `(N/|C|)³`
in the witness density and a factor `(N/|C|)⁶` in the squared row-filling
error budget. The coarse bound is also proved as a separate interface.
These are classical ambient-density estimates; they do not assert the
quasipolynomial bounds of the deeper structural argument.

If `W ⊆ B(T; ρ/4)`, every point of the representation Bohr set lies in
`B(T; ρ)`, by its actual four-point representation. The already-ported
proper-progression theorem supplies a symmetric proper target progression
`P`, containing zero, of rank at most `|S|+1`, with

```
|P| ≥ exp(-((|S|+1) log(1+π) + 10(|S|+1)²)) N.
```

All its points remain in the original map domain and have the quantitative
witness count above. `proper_progression_pattern_completion` combines
this construction with the row-filling theorem. It needs no assumed
representation count. It still requires the pattern graph's quasirandom
box-sum bound and the explicit numerical budget involving its density.

`global_robust_seven_operator_completion` composes this with J.88, starting
from the actual global density of `A`. It constructs the initial proper
progression `Q`, its dense subset `W`, the normalized maps, and the proper
target progression `P`. It retains both relative and ambient lower bounds
on `|W|` and sets `σ=|W|/N`, with the graph class `C=Q.carrier`. Given the
remaining graph estimate and its displayed budget, every `y ∈ P` has the
specified Bohr row contained in

```
horDiff (verDiff (verDiff (horDiff (verDiff (horDiff (horDiff A)))))).
```

The construction does not prove the remaining algebraic regularity
iteration or recover the paper's prescribed quantitative constants.
All five numbered open statements and the source-fidelity caveats remain.
No upstream source was added or changed; the existing Apache provenance
and copyright records cover the reused progression theorem.

The 140-module source closure and all fifteen individual transitive axiom
checks pass, using only `propext`, `Classical.choice`, and `Quot.sound`.

The merged full audit passes for 6,566 public Gowers theorems in a
5,013-module facade (4,152 OAI modules), or 5,015 modules including both
audits. It includes the incoming per-frequency-radius Bohr relation and
factorization results. The source ledger matches its tracked version
(115 companions, five open statements), and the selected port-scope
check passes. The full audit retains the same three-axiom boundary.


### Split relations make the bilinear Bohr variety quasirandom (2026-10-09)

`Proofs16SplitProfile.split_profile_quasirandom` composes Claim 34 with
Appendix B. It is the general form of the box-quasirandomness hypothesis
left open in `global_seven_operator_completion`. The graph has
`x ∈ X = B(γ; a−c)` (mixed radii), `y ∈ Y`, and an edge when
`x ∈ B(ℓ(y); b−c)`. Suppose that:
- for all but `η|Y|` vertices, the bounded relations of `γ ⊔ ℓ(y)` split
  with a fixed `Λ`;
- for all but `η|Y|²` pairs, those of `γ ⊔ ℓ(y) ⊔ ℓ(y′)` split with
  `Λ × Λ`;
- the corresponding mixed Bohr sets satisfy the weak-regularity band
  condition at error `εN`;
- one truncation budget holds;
- `20εN ≤ |X|`.

Then for some real `δ ∈ [0,1]`,
`boxSum (G − δ) ≤ 3(80εN/|X| + η)|X|²|Y|²`.

Ingredients:
- `mixedBohr_sumElim`: degrees and codegrees are mixed Bohr sets of
  concatenated tuples.
- `latticeWeightMixed_sumElim_prod`: the pair weight is `W·W`.
- One typical vertex bounds `‖W‖ ≤ 2`, so [49]'s tacit `|δᵢ| ≤ 1` is
  replaced by a proved bound.
- `boxSum_le_of_complex_profile` (`Proofs16ComplexProfileQuasirandom`)
  reads `δ` off a typical vertex and absorbs the complex weight.
- `boxSum_le_of_typical_codegrees` turns typical-vertex estimates into
  averaged ones.

Standard axioms throughout; collision gate clean. What remains to feed
the completion is the Theorem 33 iteration, which produces a domain where
relations split for most `y`. Its two simplified steps are
`freiman_const_on_bohr_of_dense` and `strict_chain_length_le`. Also
needed is the identification of the pattern graph (`patternEdge` on
`bohr F (θ/2)`) with this graph, via `bohr_floor_radius` and an
enumeration of `F`.

### J.90. Actual pattern degrees and the relation-density bridge

The pattern graph now has exact degree and codegree identities at its
actual real radii. `Proofs16PatternBohrDegrees` defines the fixed tuple
on `F` and the varying tuple on `J 0 ∪ J 2`. The degree is the mixed Bohr
set on their concatenation, with integer radii `floor(eta*N)` and
`floor(eta*N/4)`. The codegree uses two varying blocks and preserves
repeated frequencies. Rounding is exact because centered norms are
integers. The identities count vertices of the actual subtype graph.

`Proofs16PatternBohrQuasirandom` applies typical degree/codegree averaging:
if the exceptional vertex and pair fractions are at most `chi`, and the
typical absolute errors are at most `e*|B(F;eta)|`, then

```
boxSum (patternGraph - delta) ≤ 3(e+chi) |B(F;eta)|² |C|².
```

The budget form accepts `3(e+chi) ≤ epsilonGraph⁴` and supplies precisely
the box-sum inequality consumed by the J.89 row-filling construction.

The relation factor is no longer left with an uncontrolled complex norm.
`Proofs16RelationWeightDensity` proves that a mixed relation weight is
within the Fourier truncation error of a real `delta ∈ [0,1]`: use the
normalized average of the product of trapezoids. No annulus regularity
is required for this density fact. Setting the fixed coefficients to zero
in a splitting identity identifies the common lattice weight with the
varying tuple's relation weight. One splitting tuple therefore supplies
a common approximate density for the whole relation class.

`Proofs16PairedRelationDensity` proves exact product factorization of
lattice weights. If the single weight is within `zeta` of `delta`, the
paired weight is within `zeta*(2+zeta)` of `delta²`. Thus single and paired
estimates use the same real density, rather than unrelated approximations.

`Proofs16BohrDensityFactorization` converts the complex factor estimate
into the real error

```
|B_full - delta*B_base| ≤ (4+2*zeta)*epsilon*N + zeta*B_base.
```

The last term retains the base Bohr cardinality. `Proofs16BohrDensityAtRadii`
shifts the smoothing radii by `c`, expressing the conclusion directly at
the desired inner radii and the annulus at the radii enlarged by `2c`.
It supplies both the single and paired versions.

`Proofs16PatternRelationsQuasirandom.pattern_boxSum_of_relation_splitting`
composes these estimates with the exact pattern counts. Its hypotheses
are the typical splitting identities, the single and paired annulus
bounds, explicit truncation budgets, and the numerical conversion to
relative degree error. Its conclusion is the actual pattern graph's box
bound. This is the algebraic-to-graph implication, not a proof that those
splitting identities and regular annuli exist on a suitable domain.

`Proofs16PatternDensityLower` also removes a possible degeneracy of the
approximate density. If the union of the fixed and varying frequencies
has rank at most `r` and `4 ≤ eta*Q`, every pattern degree satisfies

```
N ≤ Q^r * degree(t).
```

A single typical degree with error `e*|B(F;eta)|` then gives
`delta ≥ Q^(-r)-e`. In particular `e < Q^(-r)` supplies the strict positive
density required by row filling.

The incoming `Proofs16ComplexProfileQuasirandom` and `Proofs16SplitProfile`
provide a complementary generic route using a typical vertex's actual
degree as the density. They are retained. The new direct-radius
intersection identity is named `mixedBohr_sumElim_radii`, while the
incoming `mixedBohr_sumElim` takes an additional radius subtraction.
Their public names and assumptions are distinct.

All 25 new declarations pass individual transitive axiom checks, using
only `propext`, `Classical.choice`, and `Quot.sound`; the final source
check covers 145 modules. No ported code was added or modified. The
algebraic regularity existence/iteration, its prescribed quantitative
budgets, all five numbered open statements, and the previously recorded
source-fidelity limitations remain unresolved.

The full merged audit passes for 6,630 public Gowers theorems in the
5,023-module facade (4,152 OAI modules), or 5,025 modules including both
audits. The source ledger matches its tracked version, with 115
companions and five open statements, and the selected port-scope check
passes. The merged typical-codegree, complex-profile, and split-profile
results are covered by the same three-axiom audit.

A concurrent main update added `Proofs16RelationAveraging`: the popular
witness pigeonhole step and the collision-pair Cauchy--Schwarz estimate.
After the rejected main push, those results were reviewed, merged, and
audited. The combined audit now passes for 6,641 public Gowers theorems
in 5,026 modules (5,024 in the facade, including 4,152 OAI modules),
with the same three allowed axioms and unchanged numbered-statement status.



### No radius selection in prime Z/N; the remaining lane (2026-10-09)

`Proofs16PrimeBandSplit`.
- `mixedBohr_band_le`: in prime `ℤ/N`,
  `|B(γ; a+c)| ≤ |B(γ; a−c)| + |ι|(4c+2)` for `c ≤ aᵢ`, at every radius.
  So [49]'s choice of a regular radius ρᵢ per piece ((10)–(12)) is not
  needed.
- `split_profile_quasirandom_prime`: the quasirandomness bridge with all
  band hypotheses discharged at `ε = m(4c+2)/N`, where
  `m = |ι ⊕ (κ ⊕ κ)|`. The remaining hypotheses are:
  - relation splitting for all but `η|Y|` vertices and all but `η|Y|²`
    pairs;
  - the truncation budget;
  - `20m(4c+2) ≤ |B(γ; a−c)|`.

  The conclusion is
  `boxSum (G − δ) ≤ 3(80m(4c+2)/|X| + η)|X|²|Y|²` for a real
  `δ ∈ [0,1]`.

`Proofs16RelationAveraging` holds the counting steps of the iteration:
`exists_popular_witness` (pigeonhole onto one relation) and
`collision_pairs_ge` (Cauchy–Schwarz from `f(y) = h(y′)` to
`f(y₁) = f(y₂)`).

**Lane note (claude session).** I am continuing with the Theorem 33
iteration itself. It produces, inside the graph class `C`, a sub-piece
on which the relations of `F ∪ V(y)` split for typical `y` and pairs.
Its parts are `freiman_const_on_bohr_of_dense`, `strict_chain_length_le`
and the two counting steps above. One input remains open: the
representation density on the chosen piece. `proper_progression_pattern_completion`
currently takes `C = Q.carrier`; a piece-relative witness count would
be needed if the piece is a proper subset.

### J.91. Quantitative strict-relation iteration on Bohr domains

The algebraic regularity refinement is now constructed, including a
modulus-independent rank recurrence and a termination proof. The result
controls the bounded bad relations on a nested Bohr domain. Transporting
the selected dense parameter set through this construction remains a
separate task; this is not a claim that the complete structural theorem
or its printed bounds have been proved.

`Proofs16StrictRelationKernel` applies the dense constant-fibre kernel
lemma to a coefficient vector `w` that is not a relation on the current
full domain `B(Gamma;sigma)`. On the new Bohr domain the combination equals
its value at zero, so `w` becomes a relation. Restriction preserves the
previous relations, giving a strict inclusion of relation subspaces.
The individual maps need not be normalized for this refinement.

`Proofs16PopularRelationFiber` fixes one coordinate of a popular matching
equation. If a fraction `theta` of `C × C` satisfies a two-sided relation,
some constant fibre has at least `theta*|C|` points. In
`Proofs16PopularKernelStep`, that fibre yields a kernel Bohr set with rank
at most

```
16 * (theta * |C| / N)^(-2).
```

Either coefficient vector may be the nonrelation: swapping the two
coordinates preserves the exact pair count. This direct fibre argument
retains `theta`, instead of first replacing it by `theta²` through the
collision-pair Cauchy--Schwarz estimate. The inverse-square rank loss is
therefore in the original matching density.

`Proofs16BadRelationKernel` first selects a popular witness from a finite
cover of bad pairs. `Proofs16BoundedBadRelations` specializes it to bounded
fixed, left, and right coefficient vectors. For fixed-frequency index
set `iota`, map index set `kappa`, and cutoff `R`, the witness count is at
most

```
M = (2R+1)^(|iota|+2|kappa|).
```

This bound holds even when the coefficient radius wraps around the cyclic
group. Too many bounded bad pairs then give a strict refinement with
spectrum rank at most `16*((theta/M)*|C|/N)^(-2)`.

`Proofs16NestedRelationKernel` adjoins the old frequencies and uses radius
`min(sigma,1/(8*pi))`. Both the full and quarter domains are contained in
their old counterparts. Full-domain containment alone would not imply
quarter-domain containment; retaining the old frequencies establishes the
needed stronger property. The strict relation increase survives this
additional restriction.

`Proofs16BadRelationSplitting` connects the stopping criterion to the
quasirandomness interfaces. For maps normalized at zero, every pair
outside `boundedBadRelationPairs` satisfies the exact bounded splitting
identity with `boundedRelationClass` of the full domain. The analogous
single-vertex identity holds outside `boundedBadRelationVertices`. Every
bad vertex makes all its pairs bad, using zero coefficients on the other
side, so a bad-pair fraction at most `theta` also bounds the bad-vertex
fraction by `theta`.

The quantitative iteration fixes `0 < sigma ≤ 1/(8*pi)` and a natural
cell count `Q > 0` with `4 ≤ sigma*Q`. The quarter Bohr domain of a rank-`d`
frequency set has density at least `Q^(-d)`. Define

```
Phi(d) = d + ceil(16*((theta/M)/Q^d)^(-2)).
```

`Proofs16RelationRankBudget` proves that `Phi` is monotone, `d ≤ Phi(d)`,
and every failed bad-pair bound has a refinement of rank at most `Phi(d)`.
There is no dependence on the ambient modulus in this recurrence.

`Proofs16BohrRelationIteration.exists_sparse_bad_relation_domain` proves
termination with an explicit bound. If the initial relation subspace has
dimension `s`, the final spectrum has rank at most
`Phi^[|kappa|-s](|Gamma|)`, contains the original frequencies, preserves
full and quarter containment, and has strictly fewer than
`theta*|B(S;sigma/4)|²` bad pairs. Every unsuccessful step strictly increases
the relation dimension, so the initial relation codimension bounds the
number of recurrence steps.

The incoming `Proofs16PrimeBandSplit` supplies mixed-Bohr annulus bounds
in prime cyclic groups and discharges the weak-regularity hypotheses of
the generic split-profile theorem. Its explicit truncation and size
budgets still need to be made compatible with the final construction.
Density retention for the selected parameter set, affine recentering,
and the paper's prescribed quantitative constants remain unresolved.
All five numbered open entries and the recorded source-fidelity caveats
remain unchanged.

The increment/splitting source check covers 55 modules, and the iteration
check covers 57. All 22 new declarations pass individual transitive axiom
checks with only `propext`, `Classical.choice`, and `Quot.sound`. No upstream
source, selected port scope, license, or provenance record was changed.

The full merged audit passes for 6,689 public Gowers theorems in a
5,034-module facade (4,152 OAI modules), or 5,036 modules including both
audits. The incoming prime mixed-Bohr band estimates are included. The
source ledger matches the tracked 115 companions and five open entries,
and the selected port-scope check passes. All audited declarations remain
within the same three-axiom boundary.

### J.92. Dense row retention through the relation iteration

The density-retention and affine-recentering gap recorded in J.91 is now
resolved by six modules. This does not close the remaining truncation,
size, and prescribed-constant compatibility obligations.

`Proofs16DenseAffineCluster` proves that any nonempty translated cluster
inside a common Freiman domain has simultaneous affine formulas
`L_j(t+x) = c_j + L_j(x)`. Choose one anchor `b` and use the Freiman
quadruple `(t+x,b,t+b,x)`. Neither the translation `t` itself nor zero
needs to lie in the cluster; the maps need not be normalized for this
step. Averaging translates retains ambient density on an arbitrary
nonempty test set inside the domain.

`Proofs16AffineTupleRows` tracks actual rows of the ambient set, not just
abstract graph statistics. Adding the offsets `c_j` to the fixed
frequencies and halving the phase radius preserves the row inclusion
after recentering. The number of added fixed frequencies is at most
`k = |kappa|`; the variable maps themselves remain unchanged.

`Proofs16DenseBohrRefinement` retains relative density `alpha` on a
refined quarter Bohr domain. If `4 ≤ sigma*Q`, its ambient density is at
least `alpha/Q^|S|`. `Proofs16DenseRelationStep` combines this with the
strict relation increase and quantitative rank bound of J.91, retaining
a nonempty set of actual rows at every failed bad-pair estimate.

The fixed frequencies change during this process, so the fixed-tuple
iteration of J.91 does not by itself establish the desired conclusion.
`Proofs16DenseRelationBudget` supplies a common budget for the Bohr rank
and the current number of fixed frequencies:

```
M(d)   = (2R+1)^(d+2k)
Psi(d) = d + ceil(16*((theta/M(d))/Q^d)^(-2)) + k.
```

This monotone recurrence is independent of the ambient modulus. In
`Proofs16DenseRelationIteration`, let `n` be the initial relation
codimension, `d = max(|Gamma|,|F|)`, and `D = Psi^[n](d)`. The theorem
`exists_dense_sparse_relation_domain` produces a refined spectrum `S`,
fixed frequencies `F'`, recentered row origin, and nonempty parameter
set `V` with all of the following proved simultaneously:

- `Gamma ⊆ S`, `|S| ≤ D`, and both full and quarter domain containment;
- `F ⊆ F'` and `|F'| ≤ |F| + n*k`;
- `V` lies in the refined quarter domain and has ambient density at least
  `alpha/Q^(n*D)`;
- the actual row geometry holds at phase radius `eta/2^n`;
- fewer than `theta*|B(S;sigma/4)|²` bounded bad pairs remain, computed
  using the final enlarged fixed-frequency set `F'`.

The induction permits early termination and restricts the phase radius
to the stated uniform bound. Each unsuccessful step strictly raises the
relation dimension, which bounds the number of steps by `n ≤ k`.
The varying maps are only restricted to smaller domains, so any initial
normalization at zero is preserved for subsequent splitting lemmas.

This is a quantitative existence result for dense row geometry with few
bad relations, not yet the final quasirandom graph or seven-operator
completion. The Fourier cutoff and size budgets still have to be made
compatible with these losses. The five numbered open entries, 115
companions, and all source-fidelity qualifications remain unchanged.
No upstream source or selected port dependency was added or modified.

Validation: all 15 newly named theorems pass individual transitive axiom
checks with only `propext`, `Classical.choice`, and `Quot.sound`. The full
consumer audit passes for 6,710 public Gowers theorems in a 5,040-module
facade (4,152 OAI modules), or 5,042 modules including both audits. The
source ledger matches the tracked 115 companions and five open entries;
the selected port-scope check also passes. The Apache provenance/license
files and the selected upstream source closure remain unchanged.

### J.93. Explicit graph cutoff and dense quasirandom domain

The truncation and base-size hypotheses left by J.92 are now discharged
for the actual tuple Bohr graph. This supplies a graph with any prescribed
box error while retaining dense row geometry. It does not yet ensure that
the error meets the seven-operator budget relative to the resulting
parameter density and representation counts.

`Proofs16SparseRelationProfile` derives all combinatorial hypotheses of
the prime split-profile estimate from a bound on bounded bad pairs.
The exceptional vertices and pairs are pulled back to the parameter
subtype; injectivity bounds their cardinalities. The existing bad-vertex
product argument bounds the exceptional vertex fraction by the pair
fraction. If this fraction is less than one, a typical reference vertex
exists. Normalization `L_j(0)=0` then supplies the single and paired
splitting identities. No exceptional sets or reference vertex remain
as additional inputs.

`Proofs16PrimeProfileBudget` takes `c = floor(tau*N)`. For `0 < tau < 1/2`,
the centered smoothing interval has at least `tau*N` points. If
`tau*N ≥ 1`, the band error satisfies

```
2*m*tau ≤ m*(4*c+2)/N ≤ 6*m*tau.
```

If `m*tau ≤ 1/2` and `R+1 ≥ tau^(-2)`, the product truncation error is at
most `2*m*tau`, hence at most the band error. If the base set has density
at least `beta` and `120*m*tau ≤ beta`, the required size condition holds
and the box-error coefficient is at most
`3*(480*m*tau/beta + theta)`. These bounds include the integer endpoints.

`Proofs16ScaledRelationProfile` combines these facts.
`Proofs16TupleBohrQuasirandom` sets the trapezoid radii to
`floor(rho*N)+c` and `floor(nu*N)+c`, so the inner graph uses the exact
prescribed real radii `rho` and `nu`. If the total frequency count is at
most `m`, `Q > 0`, and `rho*Q ≥ 1`, the base Bohr set has density at least
`Q^(-m)`. This bound does not involve the rank of the parameter domain.
The transport lemma `boxSum_finset_congr` handles equality of finite
vertex sets without treating their subtype instances as definitional.

For `0 < epsilon ≤ 1`, `Proofs16ExplicitGraphCutoff` chooses

```
tau = epsilon / (2880*(m+1)*Q^m)
R   = ceil(tau^(-2)).
```

When `N ≥ tau^(-1)`, the two graph radii are below `1/4`, and the bad-pair
fraction at cutoff `R` is at most `epsilon/6`, the actual graph satisfies
`boxSum(G-delta) ≤ epsilon*|B|²*|C|²` for some `delta` in `[0,1]`.
No analytic cutoff, annulus, or base-size hypothesis remains. Both the
cutoff and modulus threshold depend only on the prescribed accuracy,
cell count, and frequency cap.

`Proofs16DenseQuasirandomDomain.exists_dense_quasirandom_domain` combines
this with the stateful dense relation iteration. If there are `k` maps,
use the uniform frequency cap `m = |F|+k²+2k`, error threshold
`theta = epsilon/6`, and the explicit cutoff above. The fixed-frequency
cell count `H` is chosen with `2^k ≤ eta*H`; the domain cell count `Q`
satisfies `4 ≤ sigma*Q`. For initial relation codimension `n`, the final
row radius is `rho = eta/2^n`, and the graph uses fixed radius `rho` and
variable radius `rho/4`. The theorem produces a refined spectrum, a
nonempty dense parameter set, enlarged fixed frequencies, recentered
row geometry, and the actual box estimate simultaneously. The rank and
density losses remain the explicit recurrence from J.92, now evaluated
at the chosen cutoff and bad-pair threshold.

What remains: the graph density has so far only been exposed as a value
in `[0,1]`. A quantitative positive lower bound is needed for row filling.
More substantially, the required box error depends on the retained row
density and robust representation counts, which themselves deteriorate
through relation refinement. Choosing a fixed error before the iteration
does not by itself resolve that dependence. A state-dependent error
budget or the corresponding argument from the source must close it.
All five numbered open entries and source-fidelity caveats remain in
force; these results do not establish the deep variety theorem or its
printed numerical constants.

Validation: the focused final check covers 146 modules. All 11 newly
named theorems pass individual transitive axiom checks. The full audit
passes for 6,725 public Gowers theorems in a 5,046-module facade (4,152
OAI modules), or 5,048 modules including both audits, using only
`propext`, `Classical.choice`, and `Quot.sound`. The source ledger still
matches 115 companions and five open entries. The selected port-scope
check passes; upstream sources and Apache provenance/license files are
unchanged. The merged incoming work concerns topology only.

### J.94. Adaptive accuracy and the robust row-filling budget

The two quantitative gaps identified in J.93 are now resolved at the
graph-construction interface: the approximating graph density has an
explicit positive lower bound, and the graph error pays the robust
row-filling scalar budget at the actual retained density. Applying the
result to complete target rows and the proper progression remains a
separate integration step; no numbered closure is claimed here.

`Proofs16BoxDensityLower` applies the box-correlation estimate to constant
test functions. If every degree is at least `beta*|X|` and the box error
is at most `epsilon^4*|X|²*|Y|²`, then `delta ≥ beta-epsilon`. No positivity
of the approximating density is assumed. `Proofs16TupleDensityLower`
places a common smaller Bohr set in every degree, giving
`delta ≥ Q^(-r)-epsilon` when `r` bounds the fixed and varying frequency
counts and the smaller radius times `Q` is at least one.

`Proofs16AdaptiveRelationBudget` and `Proofs16AdaptiveRelationIteration`
replace the fixed cutoff and tolerance by arbitrary schedules `R(d)`
and `theta(d)>0`. The scalar state `d` bounds domain rank, fixed-frequency
count, and the density-loss exponent: the retained set has ambient
density at least `alpha/Q^d`. Define the exact update

```
Phi(d) = d + denseRelationBudget(theta(d),R(d),Q,k,d).
```

At a failed bad-pair estimate, the new rank is at most the second term,
and that term also pays for the loss in density. Strict relation growth
still forces termination within the initial relation codimension. The
final state is an actual iterate `D = Phi^[s](d)`, and the conclusion uses
`theta(D)` and `R(D)`. Neither schedule needs to be monotone. The proof
also retains the sharper frequency count `|F'| ≤ |F|+s*k` and row radius
`eta/2^s`.

For a graph-error schedule `e(d)`, `Proofs16AdaptiveGraphSchedule` sets
`theta(d)=e(d)^4/6` and `R(d)=relationProfileCutoff(e(d)^4,H,m)`. A natural
modulus threshold is the maximum of the rounded Fourier size thresholds
at the finitely many states `Phi^[s](d)`, `0 ≤ s ≤ k`. The theorem
`adaptiveGraphModulusBound_spec` supplies the required bound at any
reachable state. This threshold is explicit and requires no fixed point
or implicit feasibility assumption.

`Proofs16AdaptiveDenseGraph.exists_adaptive_dense_graph` combines the
adaptive relation theorem, Fourier cutoff, and density lower bound.
Set `m=|F|+k²+2k`, take `2^k ≤ eta*H`, and put

```
beta = (4H)^(-m).
```

Any positive schedule satisfying `e(d) ≤ beta/2` yields a retained dense
row configuration with `delta ≥ beta/2`, box error at most
`e(D)^4*|B|²*|C|²`, and ambient row density at least `alpha/Q^D`. The graph
and the error refer to the same final state `D`; the right graph class is
the final quarter Bohr domain. Both full and quarter domain containment
remain explicit.

`Proofs16AdaptiveFillingError` chooses the schedule needed by robust row
filling. Write `b=beta/2` and `a_d=alpha/Q^d`, and take

```
e(d) = min(b/2, (b³*(a_d⁴/4))² / (12*4^(m+1)*(4H)^m)).
```

This schedule is strictly positive and admissible for the adaptive graph
theorem. The existing robust witness density obeys
`robustRepresentationDensity(alpha',C) ≥ a_d⁴/4` whenever `alpha' ≥ a_d`.
The new budget theorem therefore gives

```
4^(m+1) * (12*e(d)) * (4H)^m
  ≤ (delta³ * robustRepresentationDensity(alpha',C))².
```

Finally, `Proofs16BudgetedDenseGraph.exists_budgeted_dense_graph` instantiates
the adaptive graph construction with this schedule and proves the scalar
inequality using the actual retained density `alpha'=|V|/N`. The graph
estimate and the robust filling budget are both conclusions. This removes
the dependence problem noted in J.93; it does not merely assume that a
fixed error can satisfy its own density loss.

Next, the tuple row geometry and graph must be connected to the existing
pattern row-filling and proper-progression completion theorems, including
restriction of the Freiman maps and the identification of frequency
indices. The original paper's precise constants and the deep variety
statement remain unresolved. All five numbered open entries, 115
companions, and source-fidelity qualifications remain unchanged. No
upstream source or selected port dependency was changed.

Validation: the final focused build covers 167 modules. All 12 newly
named theorems pass individual transitive axiom checks. The full audit
passes for 6,748 public Gowers theorems in a 5,054-module facade (4,152
OAI modules), or 5,056 modules including both audits. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The source ledger matches
the unchanged 115 companions and five open entries, and the selected
port-scope check passes. Apache provenance/license files and upstream
sources are unchanged. Subsequent merged main changes concern topology
only and do not alter the audited Gowers dependency closure.



### Theorem 33 on translated pieces: constants must be absorbed (2026-10-09, design)

[49]'s proof of Theorem 33 partitions `C` into pieces
`Sᵢ = C ∩ (xᵢ + Q′_s)`, translates of a shrunk progression. The lattice
`Λ_s` is constructed so that `λ·L(y) = 0` for `y ∈ Q_s` and `λ ∈ Λ_s`.
On a translated piece, Freiman-linearity gives
`λ·L(y) = λ·L(xᵢ) + λ·L(y − xᵢ) = λ·L(xᵢ)` for `y ∈ Sᵢ`. That is a
constant `c_λ`, in general nonzero.

Claim 34's evaluation
`Σ 1(Σνγ + Σaⱼ Lⱼ(y) = 0) Π c = δ₀δᵢ` uses both directions of the
splitting. The converse direction (ν ∈ M and λ ∈ Λ_s imply that the
relation holds at `y`) needs `c_λ = 0`. With constants the weight
becomes `Σ_{λ∈Λ} w_λ·V(−c_λ)`, where `V(s)` weights the solutions of
`ν·γ = s`. Degrees on the piece are still approximately constant. The
codegree weight `Σ w_λ w_{λ′} V(−c_λ − c_{λ′})` is not in general the
square, so quasirandomness can fail.

The formal factorization (`relationWeightMixed_sumElim_of_split`)
assumes the two-sided splitting and so cannot be applied blindly to
translated pieces.

**Resolution in this corpus's architecture.** Re-center each piece:
- write `L(xᵢ + q) = L(xᵢ) + ψ(q)`;
- move the constant frequencies `L(xᵢ)` into the fixed set `Γ`, as
  `fixed_patterns_recentered` (J.85) already does for the pattern
  frequencies.

The normalized maps `ψ` vanish at `0`. On the centered piece, `λ ∈ Λ`
gives `λ·ψ ≡ 0`, and the two-sided splitting is the right hypothesis.
Each re-centering adds at most `|κ|` fixed frequencies. The relation
chain has at most `|κ|` strict steps (`strict_chain_length_le`). So the
fixed set grows by at most `|κ|²` frequencies over the whole iteration.

Whether [49]'s proof needs this repair, or handles the constants in a
step this reading missed, is not settled here. The formal route avoids
the question by working only on centered pieces.

**Annuli discharged; one iteration step (2026-10-09).**
- `Proofs16PatternPrimeAnnuli.pattern_boxSum_of_relation_splitting_prime`
  is J.90's `pattern_boxSum_of_relation_splitting` with its three
  annulus hypotheses replaced by one budget,
  `|F ⊕ (I ⊕ I)|·(4c+2) ≤ εN`, in prime `ℤ/N`. The step is
  `mixedBohr_shift_band_le`, which applies `mixedBohr_band_le_budget` at
  the centre `a + c`.
- `Proofs16RegularityStep` and `Proofs16RegularityStepPairs` (one
  iteration step, vertices and pairs, via `collision_pairs_ge`) were
  retired in the same session. J.91's `Proofs16PopularKernelStep` and
  `Proofs16StrictRelationKernel`, written concurrently, prove the same
  step with a better loss: one popular fibre keeps `θ`, where the
  collision route gives `θ²`. J.91–J.94 then build the full adaptive
  iteration.

### J.95. Filled target rows and uniform global initialization

`Proofs16TuplePatternBridge` connects additive-quadruple linearity to
Mathlib's order-two Freiman homomorphism property. An arbitrary finite
tuple is reindexed by `Fin (card kappa)`, with all four pattern index sets
chosen as the full index set. The varying frequency sets and graph
indicators are proved equal to the original tuple versions. In particular,
no inactive maps are assumed to be Freiman on an unsupported domain.

`Proofs16TupleRowCompletion` transfers robust row filling and proper
progression completion through this bridge. Its graph estimate and
scalar budget are the same as the established pattern interfaces.
`Proofs16AdaptiveSevenOperator.exists_adaptive_seven_operator_progression`
then supplies those hypotheses from the adaptive construction of J.94.
It produces a proper symmetric progression containing zero, with every
target row satisfying

```
y in P, d in B(F' union {L_j(y)}; rho/8)
  ==> (d,y) in horDiff(verDiff(verDiff(A))).
```

Thus the final three directional operations are completed from the dense
tuple geometry. Applying this to the four-operation set supplied by the
global initialization gives the intended seven-operation expression.
There is no graph, witness-count, or scalar-filling-budget assumption
left in this completion theorem.

If `D` is the exact adaptive state and the retained ambient density is
at least `alpha/Q^D`, the extracted spectrum `U` has
`|U| ≤ 16/(alpha/Q^D)^2`. The progression has rank at most `|U|+1`, is
proper, symmetric, and lies in the final full Bohr domain. Its size is
at least

```
exp(-((|U|+1)*log(1+pi) + 10*(|U|+1)^2))*N.
```

The final domain still lies inside the initial one, and all varying maps
remain the original maps restricted to it. The affine offsets are
tracked in the enlarged fixed-frequency set and row origin.

`Proofs16UniformCompletionThreshold` takes finite maxima over bounded
frequency counts and initial states. It discharges the adaptive modulus
threshold from caps on the initial fixed frequencies, domain frequencies,
and number of maps. `Proofs16UniformCompletionState` similarly bounds all
reachable exact states, and converts this into a uniform spectrum-rank
bound. These constructions do not assume monotonicity of the adaptive
accuracy schedule.

`Proofs16UniformGeometryDensity` supplies a positive lower bound for the
ambient mass of the initial parameter set using upper bounds for its
tuple count and domain rank. The bound is antitone in those caps. It also
checks that `corollary20Kappa` is at most one on the parameter range used
by the global construction.

`Proofs16GlobalUniformTupleGeometry.global_uniform_tuple_geometry` now
turns global density into initial data with uniform caps. In the notation
of J.89--J.94, set

```
M = ceil(K/kappa)
t = ceil(2*ell * 16*kappa^(-2))
width = log(1+sigma^(-1))
a0 = ((beta^4-epsilon)/(M+1)^(4*ell))
     * exp(-((t+1)*width + 10*(t+1)^2)).
```

The theorem proves `a0>0`, `0<sigma≤1/(8*pi)`, and `0<eta<1/4`, and
extracts a tuple with at most `2*ell` maps, a domain with at most `t`
frequencies, at most `4*ell` fixed frequencies, and a nonempty parameter
set of ambient density at least `a0`. Every retained map is normalized
and Freiman-linear on the common full domain. Its actual row geometry
lies in `horDiff(verDiff(horDiff(horDiff(A))))`. Only the selected indices
`J(0) union J(2)` are reindexed into the output tuple.

The next composition is now numerical and explicit: choose cell counts
from these uniform radii, impose the finite uniform completion threshold,
and apply adaptive completion to this four-operation geometry. The
uniform state cap will give final progression rank and size bounds that
depend only on the original density parameters. That global composition
and comparison with the precise printed theorem remain to be proved;
none of the five numbered open entries is closed by this checkpoint.

Incoming `main` contributes the prime pattern-annulus specialization.
Its duplicate collision-based regularity-step modules were subsequently
retired upstream in favor of the stronger direct-fibre step already used
by this adaptive construction. The merged facade retains the annulus
specialization and does not import the retired modules.

Validation: all 14 newly named theorems pass individual transitive axiom
checks. The full merged audit passes for 6,782 public Gowers theorems in
a 5,062-module facade (4,152 OAI modules), or 5,064 modules including both
audits. Only `propext`, `Classical.choice`, and `Quot.sound` occur. The
incoming prime pattern-annulus specialization is included. The source
ledger remains equal to the tracked 115 companions and five open
entries, and the selected port-scope check passes. Upstream port sources
and Apache provenance/license files remain unchanged.



### Milićević's Theorem 1.4, Step 1 (Proposition 5.1) in Z/N (2026-10-09)

**Lane note (claude session).** With [49]'s bilinear Bogolyubov being
integrated in J.91–J.94, I am starting on the upstream end of
Milićević's own proof of Theorem 1.4 (arXiv:2601.01682). Sections 5–7
pass from a Freiman bihomomorphism to row maps with bounded-image
alternating sums, then to 16-tuples, then to a progression index set.
The source was read from the arXiv PDF: Proposition 5.1 is on pp. 53–54,
Proposition 6.1 on p. 55, and the overview of Steps 1–8 on pp. 11–13.

`Proofs16MilicevicColumns` proves the column step of Proposition 5.1 in
prime `ℤ/N`, with polynomial losses in place of Milićević's
quasi-polynomial Theorem 2.26.
- `pairKey_fst_injOn`: for a Freiman 2-homomorphism, a pair's key
  `(a − c, f a − f c)` is determined by `a − c`.
- `phiAdditiveCount_ge_of_freimanHom2`: `|A|⁴ ≤ N·phiAdditiveCount A f`,
  by Cauchy–Schwarz over at most `N` key fibres.
- `column_freiman_bohr`: suppose `|A| = αN` and `f` is a Freiman
  2-homomorphism on `A`. Corollary 7.6 (via
  `lineFreimanExtraction_eight` at energy density `α⁴`) gives `B ⊆ A`
  with `|B| ≥ 2⁻¹⁸⁸²α⁴⁶⁵⁶N` on which `f` is a Freiman 8-homomorphism.
  Lemma 7.8 at constant radius then gives a spectrum `K` with
  `|K| ≤ 16β⁻²`, where `β = |B|/N`, and a Freiman-linear `ψ` on
  `B(K; 1/(8π))` with `f x − f y = ψ(x − y)` whenever `x − y` lies in
  that Bohr set.

Applied to the columns `y ↦ φ(x, y)` of a Freiman bihomomorphism, this
is Proposition 5.1 (i)–(ii). Part (iii), bounded images of
`φ_{x₁} − φ_{x₂} + φ_{x₃} − φ_{x₄}` for many quadruples of columns,
comes next. It needs the Cauchy–Schwarz chain of p. 54 and Lemma 2.42,
which says that a Freiman-linear map vanishing on a dense part of a Bohr
set has a small image. Standard axioms only; collision gate clean.

**Lemma 2.42 without regular radii (`Proofs16FreimanFewValues`).**
Milićević's "many zeroes imply small range" (p. 35) picks a regular
radius `ρ′` with a small annulus. In `ℤ/N` a translate-averaging argument
avoids that step, and it works for any level set.
- `exists_dense_level_translate`: some `t` has
  `|Z ∩ (t + B)|·N ≥ |Z|·|B|`.
- `freiman_image_card_mul_le`: let `φ` be Freiman-linear on `B(Γ;ρ)` and
  constant on `Z ⊆ B(Γ;ρ)`. Then
  `#φ(B(Γ;ρ/2)) · |Z| · |B(Γ;ρ/4)| ≤ N·|B(Γ;ρ)|`.

The differences of the level set inside one translate `t + B(ρ/4)` form a
set `W ⊆ B(ρ/2)` on which `φ = φ(0)`. Distinct values of `φ` on `B(ρ/2)`
then give disjoint translates `x + W ⊆ B(ρ)`. Standard axioms; collision
gate clean.


### J.96. Global seven-operator progression and bilinear Bohr variety

The adaptive construction now composes with global dense tuple extraction.
For every density `0 < alpha <= 1`, and every prime modulus above the
explicit density-only threshold `densitySevenModulusBound alpha`, a set
`A` of cardinality at least `alpha * N^2` has both a proper-progression
family of filled rows and an entire bilinear Bohr variety inside

```
horDiff (verDiff (verDiff (horDiff (verDiff (horDiff (horDiff A))))))
```

These are proved conclusions, with no assumed graph quasirandomness,
representation-count estimate, row-filling budget, or structure oracle.
The construction needs no additional `openai/math` ports.

`Proofs16CompletionParameters` packages fixed-frequency, domain-frequency,
and map-count caps, the two initial radii, and the initial density. Its
cell counts are `Q = ceil(4 / sigma)` and `H = ceil(2^K / eta)`. Finite
suprema over the bounded initial ranks and adaptive iteration lengths
provide the modulus threshold and final state cap `D`. The spectrum cap
is `ceil(16 / (alpha0 / Q^D)^2)`; the uniform target row radius is
`eta / 2^K / 8`. These quantities depend only on the initial numerical
parameters, rather than on a chosen tuple configuration or on `N`.

`Proofs16UniformSevenOperatorCompletion` applies these bounds to the last
three operators. `Proofs16GlobalSevenOperatorTheorem` composes it with the
first four operators and retains properness, symmetry, zero, a rank cap,
a positive progression-density bound, and Freiman linearity of every
variable frequency on the progression. `Proofs16DensitySevenOperator`
fixes the extraction error to `(alpha / (2 - alpha))^4 / 2`, eliminating
the auxiliary error parameter from the statement.

The stronger domain conclusion comes from
`Proofs16AdaptiveBohrCompletion`: the whole robust representation Bohr
set, at radius `1 / (4*pi)`, lies inside the preceding map domain and
carries filled target rows. Restricting the maps to this set preserves
Freiman linearity. `Proofs16UniformBohrCompletion` bounds the spectrum
and row frequencies uniformly. `Proofs16GlobalBilinearBohrTheorem` then
uses the common radius `rho = min(targetRadius, 1 / (4*pi))` to obtain

```
V = bilinearBohrVariety F U L rho
```

inside all seven operators, with `#F <= f + K^2`, `#U <= S`, and at most
`K` variable maps. Each map is Freiman-linear on `bohr U rho` and takes
zero to zero. The radius is strictly positive.

Finally, `Proofs16SevenOperatorVarietySize` defines

```
M = ceil(1 / rho)
Dsize = M^(S + (f + K^2 + K))
```

and proves `0 < Dsize` and `N*N <= Dsize * #V`. Thus the produced variety
has a positive proportion of the ambient product controlled solely by
the input density. The proof applies the existing fibrewise Bohr size
bound and enlarges only its frequency exponent.

**Limits.** These explicit finite adaptive bounds are not proved to
satisfy the printed or Milićević quasipolynomial estimates. Geometric
containment does not provide the bihomomorphism extension or shifted
map-value agreement required by `MilicevicVarietyStructure` and
`MilicevicDeepVarietyStructure`. The five open numbered companions and
the statement-fidelity caveats therefore remain unchanged. In particular,
this checkpoint does not close Theorem 16.2 or Corollary 16.11.

**Verification.** The focused variety-size closure checks 189 modules.
All 20 newly named theorems pass individual axiom checks. The merged
facade audit checks 6,842 public Gowers theorems in 5,073 modules (4,152
OAI modules), or 5,075 modules with both audit consumers. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The merged column extraction
and dense-level small-image lemmas, plus the later common-witness
counting core, are included. The source ledger is
identical to the tracked 115 companions and five open entries; the
selected-port scope check passes. All upstream sources and Apache
provenance/license files remain unchanged.


**Proposition 5.1 (iii), counting core (`Proofs16CommonWitnesses`).** Each
column `x ∈ X` has a witness set `T x` of size at least `cM` in a type of
size `M`. In Proposition 5.1 these are the quadruples `(z₁,…,z₄)`
representing `φ_x`. A double count replaces Milićević's Cauchy–Schwarz
chain (p. 54):
- `commonWitness_sum_eq`: the weighted count of additive column
  quadruples, weighted by their common witnesses, is `Σ_w E(S_w)`, where
  `S_w = {x : w ∈ T x}`.
- `additiveCount_ge`: `E(S) ≥ |S|⁴/N`.
- `sum_pow_four_le`: power mean.
- `commonWitness_sum_ge`: the total is `≥ c⁴|X|⁴M/N`.
- `additive_quadruples_card_le`: there are at most `N³` additive
  quadruples.
- `many_quadruples_common_witnesses`: at least `(c⁴|X|⁴ − θN⁴)/N`
  additive quadruples in `X` share `θM` common witnesses.

On a shared witness `(z₁,…,z₄)` the alternating sum
`Σ(−1)ⁱφ_{xᵢ}(z₁+z₂−z₃−z₄)` vanishes by row-Freiman-linearity of the
bihomomorphism. With `freiman_image_card_mul_le` this bounds its image.
That assembly is the next step. Standard axioms; gate clean.


### J.97. Prime-target small-image rigidity without new frequencies

The previous checkpoint constructs the seven-operator geometric domain;
it does not yet control the values of an original bihomomorphism on it.
The next argument addresses bounded-image relations among column maps.
It gives a prime-cyclic simplification of the transition from small
images to exact identities, relevant to the structure route discussed
in [Milićević, Sections 6–8](https://arxiv.org/pdf/2601.01682).
The following radius bounds are proved directly here; they are not
claimed to be the bounds printed in that paper.

**Small image implies constancy after a radius shrink.** Let `f` satisfy
the Freiman quadruple identity on `bohr T rho`, where `rho >= 0`, and
suppose its image has at most `K` elements in the prime cyclic target
`ZMod N`, with `K < N`. Then

```
y in bohr T (rho / K)  ==>  f y = f 0.
```

The image bound itself forces `K > 0`, because the original domain
contains zero. For such a `y`, all multiples `j*y`, `0 <= j <= K`, lie
in the original Bohr set. Freiman linearity gives

```
f(j*y) = j * (f(y) - f(0)) + f(0).
```

If `f(y) != f(0)`, prime-field cancellation makes these `K+1` values
distinct, contradicting the image cap. This is
`Proofs16PrimeSmallRange.freiman_small_image_constant`; its normalized
version concludes `f y = 0`. The auxiliary multiple and affine-formula
lemmas are public. No additional frequencies are introduced.

**Families and column identities.** `Proofs16SmallImageRelations` applies
the argument to linear combinations of maps with different Bohr domains,
using the union of their frequencies for the common domain. Every
bounded-image combination becomes constant on the radius-`rho/K`
intersection. Normalized maps give exact zero relations. For maps on a
single common domain, an arbitrary collection of coefficient vectors
with image bound `K` lies in the relation submodule after this one
shrink; there is no dependence on the number of relations.

`Proofs16PrimeColumnIdentities` specializes to the defect

```
L(q 0)(y) + L(q 1)(y) - L(q 2)(y) - L(q 3)(y).
```

A bounded-image defect vanishes on the smaller common domain. In
particular, if every additive quadruple of indices in `X` has image
size at most `K`, the map `(x,y) |-> L x y` is an actual Freiman
bihomomorphism on

```
{(x,y) : x in X and y in bohr (T x) (rho/K)}.
```

Horizontal identities follow from the new rigidity result; vertical
identities follow by restricting the original column maps. This theorem
is conditional on the stated image bounds for all additive quadruples;
it does not assert that the required index family has already been
extracted from an arbitrary input bihomomorphism.

**A quantitative dense-level consequence.** Suppose `Z` lies in
`bohr T rho`, `f` is constant on `Z`, and `#Z >= alpha*N`, with `alpha > 0`.
Set `d = #T`. For a positive integer `M` with `1 <= (rho/4)*M`, the
existing dense-level packing bound and Bohr cardinality lower bound give

```
#f(bohr T (rho/2)) <= M^d / alpha.
```

For `rho > 0`, `Proofs16DenseLevelKernelRadius` discharges the cell
condition with `M = ceil(4/rho)` and sets `K = ceil(M^d/alpha)`. If the
prime modulus satisfies `K < N`, the resulting positive-radius Bohr set
at `rho/(2K)` lies in the original domain and satisfies `f y = f 0`
throughout. The frequency set is exactly `T`. Thus this route eliminates
the added spectrum frequencies in the existing dense-level kernel
construction, at the cost of an explicit radius shrink and a modulus
threshold. It does not claim a simultaneous improvement of every bound.

**Remaining scope.** The field cancellation and `K < N` are substantive
hypotheses. This does not establish the all-modulus, quasipolynomial
`MilicevicDeepVarietyStructure` contract, nor the dense shifted agreement
with the original map. The five numbered open statements remain open.
No additional `openai/math` code is ported by this checkpoint.

**Verification.** The focused column-family and dense-level closures pass
in 42 and 43 modules. All 14 new named theorems pass individual axiom
checks. The full merged facade audit checks 6,893 public Gowers theorems
in 5,079 modules (4,152 OAI modules), or 5,081 modules with both audit
consumers. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
The incoming public represented-map and robust column-witness
constructions are included. The source
ledger matches the tracked 115 companions and five open entries, and
the selected-port scope check passes. Upstream source bytes and Apache
provenance/license files are unchanged.


### J.98. Global density gives many exact column identities

The small-image rigidity argument of J.97 now composes all the way from
a dense Freiman bihomomorphism. The final theorem
`global_many_exact_column_quadruples` assumes only `0 < alpha <= 1`,
`#A >= alpha*N^2`, `IsEBihomomorphism A phi {0}`, and an explicit
lower bound on the prime modulus depending on `alpha`. It constructs
the column family and witness system, rather than assuming them.

**Shared witnesses preserve map values.**
`Proofs16WitnessProjection` proves that a represented four-sum and the
first three entries determine the fourth entry. Consequently,

```
#W <= #(W.image fourSum) * N^3.
```

Thus `theta*N^4` witnesses give at least `theta*N` represented points.
`Proofs16SharedWitnessZeros` defines `IsColumnWitnessSystem`, retaining
membership of every witness point in the original `A` and the exact
identity between each column-map value and the four original values of
`phi`. For an additive index quadruple, a shared witness makes the
column defect vanish by horizontal Freiman linearity of `phi`. Projecting
all shared witnesses produces a dense zero set inside the intersection
of the four original column domains. This is a value identity, not
merely a containment statement about the difference set.

**Uniform kernel radius and quadruple count.** If each column spectrum
has rank at most `d` and the original radius is `rho`, the common spectrum
of any four columns has rank at most `4*d`. Define

```
M = ceil(4/rho)
K = ceil(M^(4*d)/theta)
r = rho/(2*K).
```

For primes `N > K`, `Proofs16SharedWitnessKernel` applies J.97 to the
projected zero set. Every additive quadruple sharing `theta*N^4`
witnesses satisfies its exact column identity at the same radius `r`.
No new frequencies are introduced.

`Proofs16ManyExactColumnQuadruples` combines this with the common-witness
double count. If `#X >= b*N` and each column has at least `c*N^4`
witnesses, choose `theta = c^4*b^4/2`. At least `theta*N^3` additive
quadruples of indices in `X` then satisfy the exact identity throughout
the intersection of their radius-`r` domains. The count is of distinct
index quadruples; witness multiplicities have been eliminated.

**Constructing the input family from global density.**
`Proofs16DenseColumnEightFamily` first transposes the dense-row averaging
lemma to columns. It obtains at least `alpha/(2-alpha)*N` indices whose
columns have density at least `alpha/2`. Apply the already proved
Freiman-eight extraction to each column of the original bihomomorphism.
The resulting subsets `B x` lie in the original columns and have density
at least

```
beta = 2^(-1882) * ((alpha/2)^4)^1164.
```

`Proofs16UniformColumnRepSystem` builds each normalized column map as
`repMap (B x) (phi(x, ·))`, using the robust representation spectrum.
The uniform rank and witness-density parameters are

```
d = ceil(16/beta^2)
c = beta^4/(4*13^d).
```

The maps are Freiman-linear on their Bohr domains of radius `1/(4*pi)`,
take zero to zero, and each has at least `c*N^4` witnesses. Rank and
witness-density bounds depend on the lower density `beta`, rather than
the individual column cardinalities. `Proofs16GlobalColumnWitnessSystem`
assembles these maps and witnesses into an `IsColumnWitnessSystem` for
the original `A` and `phi`, preserving their value equations.

Finally, `Proofs16GlobalExactColumnQuadruples` sets

```
b = alpha/(2-alpha)
theta = c^4*b^4/2
rho = 1/(4*pi)
K = sharedWitnessImageCap d rho theta
N0 = K+1
r = sharedWitnessKernelRadius d rho theta.
```

For prime `N >= N0`, the constructed family has at least `theta*N^3`
exact additive column quadruples at the strictly positive radius `r`.
Both `theta` and `r` are proved positive. The conclusion also retains
the dense index set, rank bounds, full-domain Freiman linearity,
normalization, witness counts, and the original-map witness system.
There is no column-extraction, witness-system, image-bound, or
zero-set-density hypothesis in this global theorem.

**Limits.** This gives many exact additive index quadruples; it does not
yet give a dense structured family where every additive quadruple is
exact. That strengthening, the bilinear-variety organization, and the
final shifted agreement remain open. The all-modulus and
quasipolynomial requirements of the deep structure contract are also
unproved. None of the five open numbered companions is closed here.
The construction reuses the selected upstream closure without any new
ports or changes to Apache provenance.

**Verification.** The focused global construction checks 136 modules.
All 21 new named theorems pass individual axiom checks. The combined
facade audit checks 6,935 public Gowers theorems in 5,087 modules (4,152
OAI modules), or 5,089 modules with both audit consumers. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The source ledger matches
the tracked 115 companions and five open entries; the selected-port
scope check passes. Upstream source bytes and license files are unchanged.

**Proposition 5.1 (ii)–(iii) per column and per quadruple.**
- `Proofs16RepresentedMap`: the public induced map `repMap` of a
  Freiman 8-homomorphism. `repMap (a+e−b−c) = f a + f e − f b − f c` for
  every representation, and the map is Freiman-linear on represented
  points.
- `Proofs16ColumnRepSystem.column_rep_system` covers one column. Take
  `S = commonLargeSpectrum B B (√β³/4)`. Then `|S| ≤ 16/β²`, `repMap` is
  Freiman-linear on `B(S;1/(4π))`, and every point there has at least
  `β⁴N³/4` representing four-tuples (the peer's robust self-correlation
  count). `column_witness_card_ge` turns this into a witness density.
- `Proofs16MilicevicQuadrupleImage` (`alternating_repMap_vanishes`, an
  image bound for one column quadruple via Lemma 2.42) was retired in the
  same session. J.98's `Proofs16SharedWitnessZeros` and
  `Proofs16SharedWitnessKernel`, written concurrently on top of
  `Proofs16CommonWitnesses` and `Proofs16RepresentedMap`, prove the same
  vanishing for abstract column-witness systems over `IsEBihomomorphism`.
  With the prime small-image rigidity they then go further, to exact
  column identities, and `many_exact_column_quadruples` does the count.


### Proposition 5.1 assembled (2026-10-09): duplicate retired

`Proofs16BihomWitnessSystem` assembled Proposition 5.1 from
`Proofs16MilicevicColumns` and `Proofs16ColumnRepSystem`
(`bihom_many_exact_column_quadruples`, with `(δ/2)N` dense columns). It
landed in the same hour as `Proofs16GlobalExactColumnQuadruples`
(`global_many_exact_column_quadruples`), which proves the same statement
with the slightly better column count `α/(2−α)·N`. The duplicate was
removed before merging; git history keeps it.

### J.99. Removing intermediate frequencies and composing column relations

**Verified 2026-10-09.** Six modules extend J.98 from many exact
quadruples to a dense relation system with a finite quantitative
composition hierarchy. This addresses the changing domains of the
partially defined column maps.

`Proofs16RefinementKernel` proves `freiman_zero_remove_frequencies`.
Let `|T| <= d`, `|U| <= e`, `0 < r <= rho`, and let `f` be normalized
Freiman-linear on `B(T;rho)`. Put

```
P = ceil(4/rho), Q = ceil(1/r)
K = P^d * Q^(d+e).
```

If `f` vanishes on `B(T union U;r)` and the prime modulus satisfies
`N > K`, then it vanishes on `B(T;(rho/2)/K)`. The proof combines the
Bohr cardinality lower bound, the dense-level image bound, and prime
small-image rigidity. No frequency from `U` remains in the conclusion.

`Proofs16ColumnPairComposition` encodes a relation between `(a,b)` and
`(c,d)` as equality of `L(a)-L(b)` and `L(c)-L(d)` on the four endpoint
Bohr domains. Two such identities through an intermediate pair compose
at `refinementKernelRadius (4*d) (2*d) rho r`. Only the four endpoint
frequency sets occur in the result; the two intermediate sets are
removed by the preceding theorem.

`Proofs16ColumnIdentityLevels` defines a positive decreasing schedule
`r[0]=rho` and

```
r[j+1] = min(r[j], refinementKernelRadius (4*d) (2*d) rho r[j])
N0(n) = 1 + max_{j<n} refinementKernelCap (4*d) (2*d) rho r[j].
```

The finite maximum is implemented by `Finset.sup`, including `n=0`.
For `N >= N0(n)`, paths of at most `n` identities compose on the
corresponding endpoint radius. `Proofs16ColumnRelationSystem` also
requires equal index differences and proves the three symmetries:
interchanging the pairs, reversing both pairs, and exchanging the
middle entries. Positive levels `i,j` compose to level `i+j` when
`i+j <= n`. A single intermediate pair suffices.

This is a stronger qualitative transitivity condition than the
many-bridge hypothesis of the abstract BSG argument in
[Milićević, Theorem 4.1](https://arxiv.org/pdf/2601.01682), but it comes
with the explicit prime-modulus threshold and radius costs above.
No quasipolynomial estimate follows here.

`Proofs16ColumnRelationCounting` identifies the pair relations with
J.98's exact quadruples using `(p,q) -> (p.1,q.2,p.2,q.1)` and proves
equality of their cardinalities. `Proofs16GlobalColumnRelations` takes
the maximum of J.98's threshold and the composition threshold. Its
`global_dense_column_relations` then constructs the dense level-one
relations and all the stated compositions directly from `A`, `phi`,
and their original density/bihomomorphism assumptions. The witnesses,
normalization, column rank, and witness counts are retained. There is
no assumed relation density or transitivity hypothesis.

**Limits and next step.** This does not yet extract a dense set of
indices on which every additive quadruple satisfies the local identity.
The dense graph extraction, bilinear organization, and shifted agreement
remain open, as do the all-modulus and quasipolynomial parts of the deep
structure contract. One possible next step is to select a maximal-degree
star in each difference fibre: single-bridge composition would make its
leaves coherent. Establishing a dense index set still requires a further
argument; naive symmetrization may combine unrelated stars.

**Verification.** All 23 new named theorems pass individual axiom checks.
The global construction checks 142 modules. The combined audit checks
6,969 public Gowers theorems in 5,095 modules (5,093 for the facade,
including the unchanged 4,152 OAI modules), with only `propext`,
`Classical.choice`, and `Quot.sound`. The numbered catalogue remains
115 companions and five open entries; this count does not certify
fidelity to every printed statement. No upstream code or provenance
files were changed and no new upstream modules were ported.



### The deep contract: any bound, prime moduli, eventually (2026-10-09)

`MilicevicDeepVarietyStructure D` asks for more than its consumers use,
in two ways.
- **Moduli.** It quantifies over every modulus. The greedy cover applies
  it at one density, and the structure side concludes only for prime
  `N ≥ N₀`. The formalization of Milićević's proof (J.91–J.99) produces
  prime, large-modulus statements.
- **Bound.** It fixes the quasi-polynomial
  `milicevicBound D c = (2 + 2 log c⁻¹)^D`. The corpus pipeline loses
  `13^d` with `d = poly(1/c)` (`columnWitnessDensity`), which is a
  polynomial bound `poly(1/c)`, and no fixed `D` dominates it. By J.5,
  `Theorem162At 3` allows counts up to `exp(Θ(r log r))`, with `r`
  polynomial of degree `2⁵¹²` in `1/(γθ)`. So polynomial bounds of modest
  degree still fit that budget, and the quasi-polynomial form is not what
  the dimension-three target needs.

`Proofs16DeepEventuallyPrime` makes the chain parametric in both:
- `IsVarietyPieceB Bnd c φ G`, a variety piece with bound `Bnd c`.
  `IsVarietyPiece D` is the case `Bnd = milicevicBound D`,
  definitionally.
- `DeepStructureAt Bnd N c`, the contract's conclusion at one modulus and
  one density.
- `MilicevicDeepEventuallyPrime Bnd`: for each `c > 0`, there is a
  threshold `N₁(c)` such that `DeepStructureAt Bnd N c` holds for every
  prime `N ≥ N₁(c)`. The all-moduli contract implies it
  (`MilicevicDeepVarietyStructure.eventuallyPrime`).
- `exists_variety_piece_at`, `greedy_variety_cover_at` and
  `greedy_variety_cover_family_at` are the greedy cover at the single
  density they use.
- `variety_structure_side_eventually`,
  `structure_side_of_milicevic_eventually` and
  `structure_side_of_milicevic_sharper_eventually` are the structure side
  for any bound. Its threshold is `max N₀ N₁`, with `N₁` taken at the
  single density `θ/2/m(γ, θ/2)`.
- `structure_side_of_milicevic_of_eventually` is the original
  `IsVarietyPiece D` statement from the weaker hypothesis.

So a proof of Milićević's theorem in prime `ℤ/N` above an explicit,
density-dependent threshold now suffices for the structure side and
everything downstream. The original theorems and statements are
unchanged; the new chain duplicates their proofs with the weakened
hypothesis. Standard axioms; collision gate clean.

### J.100. Dense coherent column pairs without another density loss

**Verified 2026-10-09.** `Proofs16FibreStars` proves a finite selection
lemma for arbitrary finite fibre and vertex types. For each fibre choose
a vertex with maximum relation degree. Summing the degree bounds shows
that the total edge count is at most the vertex-type cardinality times
the total number of chosen leaves. No symmetry or transitivity is
assumed in this counting lemma.

`Proofs16DifferenceStars` applies this to ordered pairs in `ZMod N`.
The parametrization `(d,a) -> (d+a,a)` identifies a difference fibre
with `ZMod N`. Explicit bijections prove that relations respecting
equal differences are counted by triples `(d,a,b)`, while selected
leaves are counted by `(d,b)`. Thus `exists_difference_stars` constructs
`P` with

```
|R| <= N * |P|,
for every p in P there is z with R(z,p),
for p,q in P with equal differences, there is z with R(z,p) and R(z,q).
```

The second property transfers endpoint membership, and the third is
exactly the common-centre hypothesis needed for J.99's composition.

`Proofs16CoherentColumnPairs.global_coherent_column_pairs` starts with
only the original density and bihomomorphism assumptions. For prime
`N >= globalColumnCompositionModulusBound alpha 2`, it constructs
`X,T,L,W,P`, retaining the original-map witness system, density of `X`,
column rank bounds, normalized maps, and their local Freiman linearity.
Writing `theta = globalColumnQuadrupleDensity alpha`,
`rho = globalColumnIdentityRadius alpha`, and
`d = columnSpectrumCap (columnEightDensity alpha)`, it proves

```
theta*N^2 <= |P|,       P subset X × X,
0 < theta,             0 < columnIdentityRadius d rho 1,
```

and every two pairs in `P` with equal index difference have identical
column-map differences on their four endpoint Bohr domains at the last
radius. The common centre is removed using the prime-target frequency
removal theorem. There is no additional power of `theta` lost in this
selection.

**Remaining gap.** A dense family of coherent pairs is not a dense set
of columns on which all additive quadruples agree. Graph extraction and
bilinear organization are still required. In particular, this proof
does not assert that `P` is symmetric or that `P` contains a product of
dense index sets. The eventual-prime interface merged above is also
conditional: neither its quasipolynomial rank/radius bounds nor its
shifted agreement conclusion has been supplied by this construction.
The original all-moduli contract is unchanged and remains open.

**Verification.** The focused construction checks 145 modules. All five
new named theorems and all eight named theorems of the incoming
`Proofs16DeepEventuallyPrime` module pass individual axiom checks with
only `propext`, `Classical.choice`, and `Quot.sound`. No upstream code,
selected-port scope, or Apache provenance files were changed.

The combined audit checks 6,995 public Gowers theorems in 5,099 modules
(5,097 for the facade, including 4,152 OAI modules), with the same axiom
boundary. The source ledger is identical to the tracked 115 companions
and five open entries; the selected-port scope check passes. Companion
counts do not establish fidelity to every printed statement.


So a proof of Milićević's structure in prime `ℤ/N`, above an explicit
density-dependent threshold, with a polynomial bound, now yields the
structure side. Whether the polynomial degree then fits the full
dimension-three budget is the remaining numerical check. That check
concerns the peer's polynomial lift and `PolyBoundedControl`, not the
interface. The original theorems are unchanged. Standard axioms;
collision gate clean.

### J.101. Symmetric loopless graph of coherent column pairs

**Verified 2026-10-09.** J.100 gives a dense pair family, but it does not
make that family symmetric. Reflecting the entire family could join
unrelated selected stars in opposite difference fibres. The new
orientation step resolves this before applying graph extraction.

`Proofs16OrientedPairs.exists_oriented_pair_subset` partitions the pairs
according to whether `val(a-b) <= val(-(a-b))` and chooses the larger
part. It retains at least half the original cardinality. If two selected
pairs have opposite differences, those differences must equal their own
negatives. `prime_self_opposite_zero` proves that such a difference is
zero when the prime modulus exceeds two.

`Proofs16SymmetricColumnPairs` reflects the selected part and proves
coherence for the resulting union. Pairs with the same orientation use
the previous coherence theorem; reversing both pairs negates both map
differences. Mixed orientations meet only at zero index difference,
where both pairs are diagonal and both map differences vanish. The
union is symmetric, stays inside `X × X`, and has at least half the
original pair count. No radius shrink is needed for this step.

`Proofs16ColumnGraph` removes diagonal pairs, proving that at most `N`
ordered pairs are lost. Its global theorem starts from the original
`A,phi,alpha` assumptions. Put

```
theta = globalColumnQuadrupleDensity alpha
Ngraph = max(globalColumnCompositionModulusBound alpha 2,
             ceil(4/theta) + 3).
```

For prime `N >= Ngraph`, `global_coherent_column_graph` constructs
`X,T,L,W,E`, retaining the original witness system, the dense index set,
uniform rank bounds, normalized maps, and local Freiman linearity.
Its ordered edge set satisfies

```
(theta/4)*N^2 <= |E|,
E subset X × X,
(a,b) in E implies a != b and (b,a) in E.
```

Every two edges with equal differences have equal column-map differences
on their four endpoint Bohr domains, at J.100's positive radius
`columnIdentityRadius d rho 1`. The threshold ensures that the diagonal
loss is at most `(theta/4)*N^2`.

This supplies a graph for the vertex-set extraction stage, corresponding
to the second graph in the abstract BSG argument of
[Milićević, Theorem 4.1](https://arxiv.org/pdf/2601.01682). It does not yet
prove that a dense vertex set has all required additive identities.
The path-counting step, bilinear organization, and shifted agreement
remain open. The newly merged bound-parametric eventual-prime interface
is still conditional; no deep structure theorem is claimed here.

**Verification.** The focused construction checks 148 modules. All seven
new named theorems pass individual axiom checks with only `propext`,
`Classical.choice`, and `Quot.sound`. No additional upstream modules or
changes to Apache provenance were needed.

After merging the generalized eventual-prime interface, the full audit
checks 7,012 public Gowers theorems in 5,102 modules (5,100 for the facade,
including 4,152 OAI modules), with the same approved axiom boundary.
The numbered catalogue remains 115 companions and five open statements;
this does not certify fidelity to every printed statement.

### J.102. Dense column vertices joined by many four-walks

**Verified 2026-10-09.** Seven modules now carry out the graph extraction
from J.101. The graph argument is valid for any finite nonempty vertex
type and any symmetric relation; the global application uses the
symmetric loopless column graph.

`Proofs16GraphCodegrees` counts marked pairs in neighbourhoods by their
common neighbours. For `n` vertices, threshold `tau >= 0`, and ordered
pairs with codegree below `tau`, it proves

```
sum_x (# deficient ordered pairs in N(x)^2) <= tau*n^2.
```

`Proofs16GraphNeighbourSelection` sets `tau = delta^2*n/64`, assuming
ordered-edge density at least `delta > 0`. It maximizes the score
`delta*n*degree(x) - 32*bad(x)`. The resulting neighbourhood `S` satisfies
`|S| >= delta*n/2` and contains at most `|S|^2/16` deficient ordered
pairs. This follows from the total degree lower bound and the preceding
double count, without assuming regularity of degrees.

`Proofs16GraphPruning` deletes vertices with more than `|S|/4` marked
neighbours. Its generic finite-set lemma retains at least `3|S|/4`
vertices. `Proofs16GraphCommonCodegrees` then proves that every pair of
retained vertices has at least `|S|/2 >= delta*n/4` vertices with codegree
at least `tau` to both endpoints.

`Proofs16GraphFourWalks` defines four-walks as triples `(a,z,b)` giving
edges `u-a-z-b-v`. Repeated vertices are allowed. It proves the exact
counting identity

```
# four-walks(u,v) = sum_z codegree(u,z)*codegree(v,z).
```

Consequently, `exists_dense_four_walk_set` gives a vertex set `B` with

```
|B| >= 3*delta*n/8,
# four-walks(u,v) >= delta^5*n^3/16384   for every u,v in B.
```

`Proofs16GraphEdgeExtraction` converts an explicit finite edge set to
this interface and proves that `B` lies in its prescribed vertex
carrier. The latter follows from positivity of the walk count: every
selected vertex occurs in an edge of the original graph.

`Proofs16ColumnFourWalkSet.global_column_four_walk_set` applies the
result directly to the construction from `A,phi,alpha`, under the same
prime-modulus threshold `globalColumnGraphModulusBound alpha`. It takes
`delta = globalColumnQuadrupleDensity alpha/4`, retains `X,T,L,W,E`,
the original witness system, rank and normalization bounds, local
Freiman linearity, and all coherent equal-difference edge identities.
It supplies `B subset X` with the displayed cardinality and walk bounds.
There is no additional size threshold for this graph extraction.

**Next step and limits.** The walk count does not yet prove all additive
identities on `B`. The next step is to count pairs of walks with the
same edge-difference sequence and transport the edge identities to their
endpoints, producing additive richness inside dense subsets. This is
analogous to the change-of-variables stage of
[Milićević, Claim 4.4](https://arxiv.org/pdf/2601.01682), with four-walks
here. The present theorem makes no claim about simple paths with all
vertices distinct. Bilinear organization, shifted agreement, and the
final quantitative structure budget remain open.

**Verification.** The global construction checks 155 modules. All 11
new named theorems pass individual axiom checks using only `propext`,
`Classical.choice`, and `Quot.sound`. No additional upstream code or
changes to Apache provenance were required.


### Robustly connected pieces of dense graphs (2026-10-09): duplicate retired

`Proofs16RobustWalks` proved Milićević's Lemma 4.2 for walks of length
six (`robust_walks`, `robust_walks_explicit`: `|X| ≥ cn/3` and order
`c⁸n⁵` walks between every pair, by dependent random choice). It was
written in the same hour as J.102's `exists_dense_four_walk_set`, which
gives walks of length four with `δ⁵N³/16384` walks between every pair
of a set of size `3δN/8`. That is stronger and is already wired into the
column-graph chain, so the six-walk module was removed. Git history
keeps it.

Integration note: J.102 independently supplies four-walk extraction and
its global column application. Both walk lengths are retained; the
remaining additive-richness and identity-extension stages are shared.

After merging the independent six-walk lemma, the combined audit checks
7,050 public Gowers theorems in 5,110 modules (5,108 for the facade,
including 4,152 OAI modules), using only the three approved standard
axioms. The source ledger is unchanged at 115 companions and five open
entries, and the selected-port scope check passes. The companion count
does not establish fidelity to every printed statement.


### J.5 revisited with the pipeline's actual losses (2026-10-09, order-of-magnitude)

J.5 compared the structure side against `Theorem162At 3` assuming
Milićević's quasi-polynomial bound. The corpus pipeline instead loses
polynomially, through these parameters:
- Column core density `κ = 2⁻¹⁸⁸²(α⁴)¹¹⁶⁴` (Corollary 7.6 at energy
  `α⁴`).
- Column spectrum cap `d ≈ 16κ⁻² ≈ 2³⁷⁶⁸α⁻⁹³¹²`.
- Witness density `13^{-d}`. This is the dominant loss, `exp(−poly(1/α))`.

If the remaining steps (graph extraction, bilinear organization,
shifted agreement) stay of the same type, the deep structure holds with
some `Bnd(c) ≤ A·c^{-p}`, where `A = 2^{O(10⁴)}` and `p = O(10⁵)`. The
structure side evaluates it at `c = θ/(2m)`, with `m` polynomial of
degree about `10⁸` in `1/(γθ)` (J.4). So the piece count is
`exp(Bnd) = exp(poly(1/(γθ)))`, of degree about `10¹³`.
`Theorem162At 3` allows counts `exp(Θ(r log r))`, with
`r ≥ (2/(θγ))^{2⁵¹²}`. That is degree `2⁵¹²`, and `r ≥ 2^{2⁵¹²}` absorbs
any constant `A ≤ 2^{2⁵⁰⁰}`. Width exponents `1/poly(n·Bnd)` sit far
above the allowed `exp(−Θ(r log r))`.

So, as far as counts and exponents go, a polynomial-bound deep structure
fits the dimension-three budget with enormous room. This is an
order-of-magnitude comparison, not a formal inequality. It also assumes
that the remaining Milićević steps lose no more than polynomially in
their inputs. *Correction (J.5b below):* the formal connection does not go
through Part J, whose `PolyBoundedControl` belongs to the cubic-stackable
route. It goes from the variety chain's decomposition to
`Section16BudgetedPieceAt 3`. That link is blocked by an unbounded constant
that this order-of-magnitude count does not see.
*Second correction (J.5c below):* the assumption that the remaining steps
lose only polynomially fails for the model-elimination stage. Its
guaranteed agreement density is triple-exponentially small.

### J.5b The variety route's last link needs explicit partition constants (2026-10-09)

**Which theorem is missing.** The variety chain ends at
`exists_ceiling_free_variety_relation_decomposition`, whose pieces are
`MultiplyLinearWith` with the graph bound and exponent of
`Proofs16VarietyCeilingFreeDecomposition`. Nothing consumes it yet. Its
target is `Section16BudgetedPieceAt 3`, which
`theorem_16_2_of_budgeted_piece` turns into `Theorem162At 3`. That is the
same glue `theorem_16_2_at_two` uses. For each `(γ, θ)` it asks for a
mass `η` and a parameter `1 ≤ s ≤ η·s(θ,γ,3)`, with pieces
`MultiplyLinear γ s`. Part J and its `PolyBoundedControl` are not on this
path. They serve the cubic-stackable route, whose
`cubicBaseExponent q σ = 2⁻²⁷σ³/q⁴` is explicit.

**What blocks it.** The chain's exponents carry six constants. All of
them come from bare `∃ K p` statements, which originate in
`OAI.Erdos3.simultaneous_monomial_recurrence` (via
`exists_uniform_modular_monomial_recurrence k` and
`exists_simultaneous_multilinear_partition_bound k`). There are two
sources:
- *The bilinear variety partition* (`k = 2`, monomial degrees 1–2). This is
  `MultilinearDiameterPartition`, instantiated only in
  `Proofs16OscillationPartitionInst`. It supplies the variety constants
  `Cv, pv` (slice provider) and `Cs, ps` (spectrum restriction). For
  example, the deep cover exponent is
  `1/(1024·p²·(4C+18)·(milicevicBound D c + 2)^17)`.
- *The polynomial lift to dimension three* (`k = 3`, degrees 1–3). This
  runs through `exists_all_scale_polynomial_multilinear_cover 2`, the
  polynomial Lemmas 16.6/16.9 and
  `exists_simultaneous_commonDiff_partition_bound 2`, which calls
  `exists_simultaneous_multilinear_partition_bound 3`. It supplies the
  decomposition's `C, p`.

`MultiplyLinear γ s` needs the width exponent `E ≥ c(s⁻¹ρ,γ,3)^s`, that is
`s·2^{2^{11}}·log(s/(γρ)) ≥ log(1/E)`. Here `log(1/E) ≥ log(4C+18)`. So `s`
must grow with `log C`. Since `C` is an arbitrary witness with no upper
bound, `s ≤ η·s(θ,γ,3)` cannot be derived at `γ = θ = 1`, where the
right-hand side is the fixed number `η(1,1)·2^{2^{512}}`. The budget's
size does not matter: any opaque constant in the exponent blocks the
comparison. This holds for every bound function. It is independent of `D`,
of `Proofs16DeepBoundDomination`, and of whether deep structure is proved.

Dimension two avoids it. Its cubic route (`Proofs16DimensionTwo`) uses only
explicit partitions, and its family count `section16BaseFamilyBound` is
polynomial. So the exponential-in-count width of the explicit Lemma 16.1
is affordable there.

**Ways out, in order of cost.**
1. *Explicit simultaneous recurrences in degrees ≤ 3*: explicit `K, p` for
   `simultaneous_monomial_recurrence j`, `j ≤ 2`. Candidates are Lau's
   fully explicit bound (arXiv:2407.01611; see J.3) or an explicit
   re-proof of the OAI theorem. Every exponent in the chain stays
   unchanged, and both sources are cleared at once. This is the only
   option that clears the lift.
2. *Gowers's own Lemma 16.1, for the bilinear source only*:
   `lemma_16_1_holds` is proved with explicit constants. Its width
   exponent `K^(−2^(k+1)·q)` is exponential in the number `q` of forms.
   For the variety partition, `q` is the rank `R`, polynomial in `Bnd`, and
   `exp(−O(R))` fits the budget by the J.5-revisited count. For the lift it
   does not. There `q ≈ r·Q` counts slice graphs, `Q ≈ exp(Bnd)`, and a
   width `exp(−exp(poly))` is far below the allowed `exp(−Θ(r log r))`.
   This is the same reason Part J needs `PolyBoundedControl` (J.3). Using
   Lemma 16.1 on the bilinear side would also mean restating
   `section16FreimanVarietyExponent` and the exponents above it, which are
   written for the shape `p(q+1)^8`.
3. *Bypass the Freiman-variety cover*: show that variety pieces form a
   `CubicStackableClass` and use Part J. This needs polynomial counts,
   which variety pieces do not have (`exp(Bnd)`), unless J.3's explicit
   recurrence is proved first. That brings back option 1.

So option 1 in degree 3 is the real requirement. The counts `exp(Bnd)`
force a width exponent polynomial in the number of forms, and only an
explicit Schmidt-type recurrence gives that.

**Option 1 is cheaper than it looked.** The upstream constants are not
opaque, only packaged. `weylBudget_polynomial_bound` takes
`A = (weylBudgetPolynomial j).eval 1` and `d = natDegree + 1` of an explicit
`Polynomial ℕ`. Every later constant is a closed formula:
- `A·3^d` (`polynomial_weyl_inverse_power_bound`);
- `schmidtRecurrenceBase C e` and `schmidtRecurrenceExponent e = 15(e+1)+23`;
- the corpus's `1 + Σ` uniformization;
- the `max`/product recursion of
  `exists_simultaneous_multiaffine_partition_bound`.

Each `∃` step's proof is generic in its hypothesis. So the constants can be
named by restating the steps with fixed witnesses; nothing is re-proved.

`Proofs05ExplicitSchmidtRecurrence` does this up to the partition theorem:
- `schmidtWeylA/D/C` and `polynomial_weyl_inverse_power_interval_explicit`;
- `schmidtMonomialK/P` and `simultaneous_modular_monomial_recurrence_explicit`;
- `uniformSchmidtK/P` and `uniform_modular_monomial_recurrence_explicit`;
- `multiaffinePartitionK/P` and
  `simultaneous_multilinear_partition_bound_explicit k`.

It imports the OAI port, so it is checked on the full-verification host.
Two steps remain:
1. *Thread the named constants up both chains.* Restate
   `Proofs16OscillationPartitionInst` as
   `MultilinearDiameterPartition (multiaffinePartitionK 2 4)
   (multiaffinePartitionP 2 4)`. Restate
   `exists_simultaneous_commonDiff_partition_bound 2` and the polynomial
   Lemma 16.6/16.9 wrappers similarly.
2. *Bound the numbers.* For example, `degree(weylBudgetPolynomial j)`
   satisfies `deg_{j+1} = 4 + 6·deg_j`, so `deg = 1, 10, 64` for
   `j = 0, 1, 2`. Then check `s ≤ η·s(θ,γ,3)` with these bounds. Given
   the `2^{2^{512}}` room, crude bounds such as `A_j ≤ 2^{2^{20}}` should
   suffice.

The same session added `Proofs16DeepBoundDomination` (checked locally) and
`Proofs16DeepBoundSlices` (host). They show that any bound function is
dominated by `milicevicBound D` at a fixed density, and they give the
padded slice-class cover from `MilicevicDeepEventuallyPrime Bnd` with `D`
chosen per `(γ, θ)`.

**Progress on the last link (2026-10-09, night).**
1. *Constants threaded.* Every `∃`-constant layer of the variety route now
   has a fixed-constant form: a predicate `…At C p` and a theorem
   `…At_of`, with the old `exists_…` kept as an unchanged wrapper. This
   covers 25 layers in 23 modules: B1–B8 on the variety side, L0–L9 on the
   lift side, and T1–T7 at the top. `Proofs16ExplicitVarietyDecomposition`
   chains them into `ceilingFreeVarietyRelationDecompositionAt_explicit`,
   at
   - `explicitLiftK = ⌈multiaffinePartitionK 3 8⌉`,
     `explicitLiftP = 3·multiaffinePartitionP 3 8`;
   - `explicitVarietyK = ⌈multiaffinePartitionK 2 4⌉`,
     `explicitVarietyP = multiaffinePartitionP 2 4`.

   *Verification.* All OAI enters through `Proofs05SchmidtRecurrence`.
   The refactor was compiled against a stub of that module, with its one
   OAI-backed proof replaced by `sorry`: 143 modules, no errors. The
   assembly was compiled against a second stub of the explicit module. The
   full check, including the OAI-backed steps, belongs to the
   full-verification host.
2. *Absorption* (checked locally). `Proofs16MonomialControlAbsorption`
   and `Proofs16VarietyControlAbsorption` show the following. Controls of
   the variety shape are `MultiplyLinear γ s` with `s = 18r/γ + 64 + L`,
   for any `L` above `log W⁻¹` and `log(81·7⁴Q² + 27)`.
3. *Budget* (checked locally). `Proofs16VarietyPieceBudget` gives
   `s ≤ η·s(θ,γ,3)` whenever `L ≤ x^(64·2^256)`, `x = 2/(θγ)`. Here `η` is
   the variety piece mass.
4. *Counts* (checked locally). `Proofs16VarietyCountBounds` gives:
   - the family size is at most `x^(2^24)`, via piece mass
     `≥ (θγ/2)^14424120`;
   - a count `⌈fam·e^mb⌉ + 1` costs `log(fam+3) + mb`;
   - `milicevicBound D c ≤ (4/c)^D`.

**The link is closed (2026-10-09).** In `Proofs16VarietyTheoremThree`:

```
theorem_16_2_at_three_of_deep {D} (hD : D ≤ 2^64)
    (hM : MilicevicDeepVarietyStructure D) : Theorem162At 3
corollary_16_11_at_three_of_deep … : Corollary1611At 3
```

So in dimension three, Theorem 16.2 and Corollary 16.11 reduce, through
the variety route, to Milićević's deep structure theorem alone, for any
exponent `D ≤ 2^64`. The steps, in order:
1. *Shape* (`Proofs16VarietyShapeMatch`). The ceiling-free controls
   equal the absorbed shape, via `section16_variety_line_factor_power`.
2. *Absorption.* `Proofs16VarietyBudgetedPiece`'s
   `variety_three_multiplyLinear` makes every relation piece at the named
   constants `MultiplyLinear γ s`, with `s = 18r/γ + 64 + L`.
3. *Loss* (`section16VarietyThreeLoss_le`). `L ≤ 112·Λ` by
   `variety_loss_le`, where `Λ = 7 + 8·2^1700 + (F₁+3+m₁) + (F₂+6+m₂) + Lg`.
   Every summand is at most `X = x^(2·2^256)` by the scale bounds
   (`Proofs16VarietyScaleBounds`, `Proofs16VarietyCountBounds`), and
   `D ≤ 2^64` keeps `m₂ ≤ x^(2^158·D)` below `X`. So
   `112Λ ≤ x^(64·2^256)`.
4. *Budget* (`variety_piece_budget`). `s ≤ η·s(θ,γ,3)`, where `η` is the
   variety piece mass. Then `section16_budgeted_piece_three_of_deep…`
   and `theorem_16_2_of_budgeted_piece` finish.
5. *Constants* (`Proofs16ExplicitConstantBounds`, `Proofs05WeylConstantBounds`,
   and the host part of `Proofs16VarietyTheoremThree`). The four named
   constants are at most `2^1700`.

*Verification status (full check, 2026-10-09).* All of these modules,
including the unfolding of the actual port's recurrence definitions in
`Proofs16VarietyTheoremThree`, now compile against the real selected
sources. No scratch stubs enter this verification. The merged audit
checks 7,867 public Gowers theorems in 5,286 modules using only
`propext`, `Classical.choice`, and `Quot.sound`; see J.126. The deep
structure hypothesis remains unproved.

*What is still open* for 16.2 and 16.11 in dimension three is only
`MilicevicDeepVarietyStructure D` for some `D ≤ 2^64`, which is the
peer's lane.

**Caveat: the `D`-form is not what the pipeline delivers (2026-10-09).**
By the J.5-revisited estimate, the corpus pipeline proves the deep
structure with a polynomial bound `Bnd(c) ≤ A·c^(-p)`. That is the form
`MilicevicDeepEventuallyPrime Bnd`, with piece data and agreement at
scale `exp(-Bnd(c))`. No fixed `D` has `(1/c)^p ≤ (2 + 2·log c⁻¹)^D` as
`c → 0`, so the pipeline cannot supply `MilicevicDeepVarietyStructure D`.

The domination trick of `Proofs16DeepBoundDomination` does not repair
this. The chain uses one `D` at two densities: `c₁` for the variety
pieces at `(γ, θ/4)`, and `c₂ ≪ c₁` for the spectrum pieces. A `D` large
enough at `c₂` overshoots at `c₁` by a factor `log base(c₂)/log base(c₁)`.
This factor grows like `log log x`, so `log mb` exceeds any budget
`K·log x` once `θγ` is small enough.

The fix is to state the chain for a bound function, `D ↦ Bnd`. Every
`D`-dependence of the chain goes through `milicevicBound D c`: 26
modules, 129 occurrences, 17 uses of `two_le_milicevic_base`. That
includes `section16VarietyExtractionCount`,
`section16PolynomialJointVarietyExponent` and
`IsVarietyPiece`/`section16VarietyPieceClass`.

The plan:
- define `…B Bnd` versions;
- make the `D`-versions the instances `Bnd := milicevicBound D`, which
  keeps every current statement definitionally;
- replace `two_le_milicevic_base` by a hypothesis `0 ≤ Bnd c`.

The budget side is already written for this. `section16VarietyThreeLoss_le_of_bounds`
uses `D` only through the two Milićević values. A polynomial `Bnd` gives
`log Q ≈ Bnd(c) = poly(x)`, far inside `x^(2·2^256)`.

**Resolved without the full `Bnd` refactor (2026-10-09).** Only two
densities matter, so two Milićević indices suffice, chosen per density:
`D` for the family at `c₁` and `D₂` for the spectrum at `c₂`. Each
`Dᵢ` is the least index with `Bnd(cᵢ) ≤ milicevicBound Dᵢ cᵢ`, so it
overshoots by at most one base factor:
`milicevicBound Dᵢ cᵢ ≤ (4/cᵢ)·max(Bnd(cᵢ), 1)`
(`exists_milicevicBound_between`).

The modules:
- `Proofs16VarietyTwoScale`: the controls with the two indices.
  `section16PolynomialVarietyThreeExponent2`, with the old exponent as
  its instance `D₂ = D`.
- `Proofs16VarietyBudgetedPiece`: the budget with two indices.
- `Proofs16VarietyLocalPieces`: the relation pieces from the two local
  covers (`VarietyClassCoverAt`) instead of `MilicevicDeepVarietyStructure`.
- `Proofs16DeepBoundSlices`: `variety_structure_class_cover_of_eventually_at`
  gives the cover at any dominating index.
- `Proofs16VarietyEventualThree`: assembles them.

Result (`Proofs16VarietyTheoremThree`):

```
theorem_16_2_at_three_of_eventually {Bnd} {K} (hK : K ≤ 2^64)
    (hBnd : ∀ c ∈ (0,1], Bnd c ≤ (4/c)^K)
    (hM : MilicevicDeepEventuallyPrime Bnd) : Theorem162At 3
```

and the 16.11 corollary. So the dimension-three statements now follow
from the deep structure in exactly the form the pipeline is expected to
prove, at any polynomial degree `K ≤ 2^64`.

Lean traps met here:
- `norm_num`, `ring_nf` and `nlinarith` expand `(c·x)^n` once `n` folds
  to a literal (`2^(2^8)` folds; `2^510` does not). `Nat.pow` then panics,
  even from an unrelated hypothesis in scope, so clear it or keep
  exponents as variables.
- `rfl` checks against `t^14424120` overflow recursion; rewrite forward
  instead.
- `linarith` treats `4·(M·r)·log X` and `18·(M·r)·log X` as unrelated
  atoms.

**Full dependency verification (2026-10-09).** The incoming fixed-constant
chain, `ceilingFreeVarietyRelationDecompositionAt_explicit`, and the new
count bounds now compile against the actual selected OAI dependency
closure. The full merged audit checks 7,669 public Gowers theorems in
5,244 modules and rejects all axioms except `propext`, `Classical.choice`,
and `Quot.sound`; no stub or `sorry` is used in this verified closure.
This supersedes the limited stub-based verification described above.
The subsequent incoming `Proofs05WeylConstantBounds` also passes the full
audit: in degrees one to three, the coefficient sums of the Weyl budget
polynomials are below `2^192` and their degrees are below `256`. These
are numerical inputs to the remaining recurrence-constant comparison.
The later `Proofs16VarietyShapeMatch` also passes the full audit, proving
exact identities for the width exponent and graph count in the absorbed
variety shape. This discharges the shape-matching step above.
The subsequently merged `Proofs16VarietyLossBound` also passes a full
real-dependency audit. Its `variety_loss_le` proves positivity of the
width coefficient and bounds both required logarithmic losses by
`112*Lambda`, provided `Lambda >= 7` and each specified factor is bounded
by `exp Lambda`. This reduces the remaining numerical comparison to
those explicit factor bounds. The full numerical absorption and the deep
structural input remain undischarged, so this does not yet supply
`Theorem162At 3`.

Until the remaining bound comparison is proved,
`MilicevicDeepVarietyStructure D` (or its eventual, any-bound form) yields
the decomposition with these named constants, but not `Theorem162At 3`.

### J.5c The zero-core chain loses triple-exponentially (2026-10-09, kernel-checked)

**Handoff summary.**
1. *Defect.* The J.108–J.110 model packing and elimination guarantees a
   density of at most `exp(-2^(13^d)/2)` and a radius of at most
   `2^(-13^d)`, with `d = poly(1/alpha)`. So no chain built on the
   zero core (J.110–J.140, `global_single_coherent_progression`) can meet
   the polynomial contract of `theorem_16_2_at_three_of_eventually`.
   This is kernel-checked in `Proofs16ZeroCoreGrowth`,
   `Proofs16CoherentAnchorGrowth` and `Proofs16SingleProgressionGrowth`.
2. *ℤ/N simplification.* A bounded image already forces vanishing:
   `freiman_small_image_zero` gives zero on `B(T;ρ/K)` with no new
   frequencies.
3. *Replacement engine, formalized.* `abstract_bsg_core`
   (`Proofs16AbstractBSGCore`) is Milićević's Theorem 4.1 for single
   elements (`ℓ = 1`), with polynomial constants.
   - **Hypotheses.** A finite abelian group without 2-torsion; quadruple
     families `Q i` with symmetries (S1)–(S3) and weak transitivity;
     doubling `K`; `c|X|^3` good pairs of pairs.
   - **Conclusion.** A dense `B′` whose elements each lie in
     `θ|X|²` additive `Q 16`-quadruples.
   - **Use for column maps (instantiated, kernel-checked).**
     `column_bsg_core` (`Proofs16ColumnZeroLadder`) takes exact zero
     relations: `Q (n+1)` says the alternating sum
     `L a₁ − L a₂ − L a₃ + L a₄` vanishes on the four-column domain at
     radius `ρ_n`. Here `ρ_{n+1} = refinementKernelRadius (4D) (2D) ρ₀ ρ_n`.
     - Weak transitivity holds with a *single* bridge: add the two
       relations, then remove the bridge's frequencies. So `c′` is free,
       and the only modulus condition is
       `refinementKernelCap (4D) (2D) ρ₀ ρ₁₄ < N`.
     - The remaining input is `c|X|³` level-1 zero quadruples, which is
       J.98-type data.
     - The output is a dense `B′` whose elements each lie in `θ|X|²`
       additive quadruples, all zero relations at level 16.
     - **From the original data (kernel-checked).** `global_column_bsg`
       (`Proofs16GlobalColumnBSG`) starts from a dense
       `E`-bihomomorphism, with `N ≥ globalColumnBSGModulusBound α`. It
       takes J.98's column system and exact identities: J.98 supplies
       `γN³` of them with `γ = globalColumnQuadrupleDensity α`, and
       `exact_quadruples_le_diffGoodCount` turns them into level-1 zero
       quadruples. With doubling `K = 2/α` (from `|X| ≥ αN/2`) it
       returns a dense `B′` of columns, each in `θ|X|²` additive
       level-16 zero relations.
       - No model packing or elimination is used.
       - `γ` is `exp(-poly(1/α))` (witness density `13^(-d)`), and every
         BSG loss is polynomial in `γ` and `α`. The radii are
         `ρ_16 ≈ ρ₁^((6d)^16)`, still `exp(-poly)`.
       - This is the first stage of a replacement for J.108–J.110 that
         stays in the `exp(-poly)` regime. It does not yet give "all
         quadruples respected".
       - **With the J.142 bridging (kernel-checked).**
         `global_column_word_system` (`Proofs16GlobalColumnWords`)
         instantiates `abstract_bsg_word_system` with this ladder.
         Doubling over all of `ℤ/N` uses `K = 1`, and weak transitivity
         at threshold `c′N` follows from `c′|X|`. The result: for a
         dense bihomomorphism and every `k`, there are dense
         `B′ ⊆ B ⊆ X` with threshold richness. Every anchor list of
         length at most `k + 1` in `B′` has
         `δ_k(γ) N^(3j+2)` compatible word representations, all exact
         level-16 zero relations of the column maps. Still to come:
         Proposition 6.1 analogues, Step 3 (robust Bogolyubov–Ruzsa)
         and Steps 4–6.
4. *Not done.* Robust Bogolyubov–Ruzsa (Step 3) and the remaining
   structure assembly. The original-data prime-cyclic almost-all image
   stage needed from Proposition 6.1 is proved in J.145. The bridging statement is done: J.142 for the abstract
   engine, and `global_column_word_system` for the original data. The
   details follow below.
5. *Proposed lanes (2026-10-09).*
   - The peer, owner of J.142, continues with the Proposition 6.1
     analogue for the exact ladder and with Step 3.
   - This session takes Step 4 in `ℤ/N`. With bounded images on a
     progression-indexed system, `freiman_small_image_zero` gives the
     Bohr-respected (zero) relation directly, with no random characters.
   - Also this session: the quantitative audit of each new global stage
     against `theorem_16_2_at_three_of_eventually`.
   - Either side may claim a lane differently by recording it here.
   - *Step 5 claimed by this session (2026-10-09).* This is Milićević
     §9, Proposition 9.3: the domains `B_x` become `B(Θ₁(x), …, Θ_r(x); ρ)`
     with Freiman-linear `Θ_i`. Inputs, by their place in the corpus:
     - Theorem 2.12 (= [49] Theorem 27, Bohr sums contain span Bohr sets):
       `bohr_sum_contains_span_intersection_quarter`
       (`Proofs16SpectrumPairSumset`), polynomial.
     - Lemma 9.1 (gluing compatible maps): `compatible_bohr_sum_quadruple`
       (J.112).
     - Theorem 2.26 (approximate homomorphisms are Freiman homomorphisms on
       large progressions): the polynomial ℤ/N substitute is Corollary 7.6
       plus Lemma 7.8, as in J.6.
     - Still to build: Lemma 9.2 (eight maps from one 11-parameter identity
       family) and the independence-counting iteration of Proposition 9.3
       (Claim 9.4, sets `I_{x,y}` of size at most `s₀ = (d + log 1/ρ)^O(1)`).
     - *Progress.* Lemma 9.2's double Cauchy–Schwarz step is done:
       `respected_quadruples_of_separated` (`Proofs16SeparatedRespect`).
       Suppose a family `Q` of `c|G|²|Ω|` triples `(x, a, ω)` has
       `f(x+a) − g(x)` depending only on `(a, ω)`. Then `f` respects at
       least `c⁴|G|⁴` additive quadruples
       `f(x+a) − f(x′+a) = f(x+b) − f(x′+b)`, which is Corollary 7.6's
       input.
       `freiman_of_separated` (`Proofs16SeparatedFreiman`) finishes the
       Theorem 2.26 step polynomially: such an `f` is a Freiman
       8-homomorphism on a set of size `2^(-1882)·c^4656·N`.
       `phiAdditiveCount_ge_of_respected` is the `N`-to-one transfer to
       `phiAdditiveCount`.
       `shift_agreement` (`Proofs16ShiftAgreement`) is the pairing step
       `φ₂ = ψ₁ + u`. If `S` separates `f` and `g`, and `ψ` respects
       additive quadruples on `B` and equals `f` there, then `g = ψ + u`
       on the largest fiber, of size at least `|S′|/|G|`. In `ℤ/N` this
       replaces Milićević's rank-and-kernel argument.
     - *Assembling Lemma 9.2 for one pair (next).* Two gaps remain
       between these pieces.
       1. **Popular values.** Restrict to the triples whose value
          `z = x + a` is popular (`z ∈ Z`), and apply Corollary 7.6 with
          `B₀ = Z` instead of `univ`. This needs a variant of
          `respected_quadruples_of_separated` that keeps all four sums
          `x+a, x′+a, x+b, x′+b` in the value set. They do lie there,
          since every pair it counts comes from two triples of the family.
       2. **Domain of `ψ`.** `shift_agreement` needs `x` and `x + a` in the
          set where `ψ` is a homomorphism. Corollary 7.6 gives `ψ = f`
          only on a dense set of *values*. So first extend `ψ` to a Bohr
          set with Lemma 7.8 (`Proofs07BohrHom`), the analogue of
          Milićević's coset progression `C₁`, and then require `x` in it.

       Each restriction keeps a polynomial fraction of the triples,
       because popular values carry `(c/2)N|Ω|` triples each.
       Gap 1 is closed. `respected_quadruples_of_separated_in` keeps all
       four sums in the value set `V = {x + a}`.
       `freiman_on_values_of_separated` applies Corollary 7.6 with
       `B₀ = V`, giving `B ⊆ V` with `|B| ≥ 2^(-1882)·c^4656·|V|` on which
       `f` is a Freiman 8-homomorphism.
       Gap 2 is closed without extending `ψ` outside `A`.
       `shared_linear_part` takes `f` locally affine on `A` with linear
       part `ψ` on `K` (Lemma 7.8's `IsBHomomorphism`), and a family
       separating `f` and `g`. It gives `g x − g x′ = ψ(x − x′)` whenever
       `x + a, x′ + a ∈ A` and `x − x′ ∈ K`. So `g` shares the linear
       part `ψ`, which is Milićević's `φ₂ = ψ₁ + u`.
       **Lemma 9.2 for one pair is assembled:** `milicevic_lemma_9_2_pair`
       (`Proofs16Lemma92Pair`). Start from `cN²|Ω|` triples separating
       `f` and `g`. The result is a set `B` of values, of density
       `2^(-1882)·c^4656` in `V`, on which `f` is a Freiman
       8-homomorphism. Its linear part `ψ` is a Freiman 2-homomorphism
       on a Bohr set of spectrum `≤ 16α′^(−2)` and radius `α′/(32π)`,
       with `α′ = |B|/N`, and `g` shares `ψ` on every fiber. Every bound
       is polynomial in `c`. The eight-map version applies this pair by
       pair, restricting the family to popular values each time.
     - *Plan for Proposition 9.3 (printed pp. 65–68).*
       - **Iteration state.** Freiman homomorphisms `θ₁, …, θ_m` and, for
         each pair `x, y`, a `{-1,0,1}`-independent index set `I_{x,y}`
         with `{θ_i(x−y)} ⊆ ⟨Γ_x ∪ Γ_y⟩_R`. Independence caps
         `|I_{x,y}| ≤ s₀ = (d + log 1/ρ)^O(1)`, since `2^s ≤ (2sR+1)^{2d}`.
         The counting lemma is now `independent_card_le`
         (`Proofs16IndependenceCount`): `s` elements of
         `spanBall Γ R` with distinct `{0,1}`-subset sums satisfy
         `2^s ≤ (2sR+1)^|Γ|`.
       - **Claim 9.4.** Suppose the containment
         `B(θ_i(a) : i ∈ I; η) ⊆ (B_{x+a} ∩ B_x) + (B_{y+a} ∩ B_y)` fails for
         `ε|C|³` triples.
         1. Theorem 2.12 (`bohr_sum_contains_span_intersection_quarter`)
            puts the failing frequency into the span.
         2. One linear combination per element, chosen with success
            probability `(2R+1)^(−4d)`, is exactly
            `exists_good_selection` (`Proofs16SelectionAveraging`, four
            fixed points per requirement, `K = (2R+1)^d`).
         3. Lemma 9.2 (`milicevic_lemma_9_2_pair`, applied pairwise) gives a new
            Freiman `θ`, independent of the current indices on many
            pairs.

         Claim 9.5 is the same for 12-tuples.
         Step 2 is done: `claim_9_4_selection`
         (`Proofs16ClaimNineFourSelection`) chooses `ψ : Fin 4 → G → G`
         with `ψ i z ∈ spanBall (Γ z) R` that realize a prescribed
         decomposition at `(x + a, x, y + a, y)` for a
         `(2R+1)^(−4d)` fraction of the triples. The four independent
         maps make the fixed points distinct.
         `exists_good_selection_indexed` counts over an index family.
         Step 3 is done: `claim_9_4_core` (`Proofs16ClaimNineFourCore`).
         From `εN³` prescribed decompositions `ξ₀ − ξ₁ = ξ₂ − ξ₃` it gets
         the selected maps, an event set `E` of size
         `ε(2R+1)^(−4d)N³`, and Lemma 9.2 for `(ψ₀, ψ₁)` with `ω = y`.
         The result is a Freiman 2-homomorphism `θ` on a Bohr set with
         `ψ₁ x − ψ₁ x′ = θ(x − x′)` on the event fibers. The escaping
         frequency is `ψ₀(x+a) − ψ₁(x) = ξ₀ − ξ₁` on `E`.
         Step 1 is done: `escape_frequency`
         (`Proofs16ClaimNineFourEscape`). Suppose some `d` with
         `|θ_i·d| ≤ ηN` and `sη ≤ 1/4` is not in `B(K;ρ) + B(L;σ)`. Then a
         frequency of `⟨K⟩ ∩ ⟨L⟩` escapes the `{-1,0,1}`-span of the
         `θ_i`, by the corpus's quarter-radius Theorem 27. With
         `K = Γ_{x+a} ∪ Γ_x` and `L = Γ_{y+a} ∪ Γ_y`, it splits as
         `ξ₀ − ξ₁ = ξ₂ − ξ₃`. Still to do: the per-triple splitting into
         span balls, θ's values growing the index sets, and the
         iteration.
         The splitting toolkit is done (`Proofs16SpanBallSplit`).
         `mem_spanBall_iff` describes `spanBall Γ R` by plain coefficient
         functions `n : G → ℤ`.
         `boundedFrequencySpan_subset_spanBall` converts Theorem 27's
         centered bounded span over `K` into `spanBall K R`, via
         `valMinAbs`. `spanBall_union_split` splits
         `spanBall (Γ₁ ∪ Γ₂) R ⊆ spanBall Γ₁ R + spanBall Γ₂ R`. So an
         escaping `ξ ∈ ⟨K⟩ ∩ ⟨L⟩` with `K = Γ_{x+a} ∪ Γ_x` and
         `L = Γ_{y+a} ∪ Γ_y` gives `ξ = ξ₀ + ξ₁′ = ξ₂ + ξ₃′`, each piece in
         its own span ball. Negating the second and fourth pieces
         (`neg_mem_spanBall`) and raising both radii to a common `R`
         (`spanBall_mono`) gives `escape_split`, which is exactly
         `claim_9_4_core`'s per-triple decomposition `ξ₀ − ξ₁ = ξ₂ − ξ₃`.
         **Claim 9.4 is assembled:** `claim_9_4` (`Proofs16ClaimNineFour`).
         Take `εN³` prescribed decompositions whose frequency `ξ₀ − ξ₁`
         avoids a forbidden set `S(x, a)`; in the iteration, `S(x, a)` is
         the `{-1,0,1}`-span of the current `θ_i(a)`, `i ∈ I_{x+a,x}`. The
         result is a map `Θ`, a set `B` on which `Θ` is a Freiman
         8-homomorphism, and `claimNineFourDensity ε R d · N²` pairs
         `(x, a)` with `a ∈ B`, `Θ(a) ∈ ⟨Γ_{x+a} ∪ Γ_x⟩_{2R}` and
         `Θ(a) ∉ S(x, a)`. The density is `κ(c/2)²` with `c = (ε/K⁴)²`,
         `K = (2R+1)^d` and `κ = 2^(−1882)((c/2)^4)^1164`, so it is
         polynomial in `ε` and `(2R+1)^(−d)`. The route differs from
         Milićević's in two places.
         1. *A common value, not a linear part minus a constant.* On the
            selected triples, `ψ₀(x+a) − ψ₁(x) = ψ₂(y+a) − ψ₃(y)` depends
            only on `(x, a)` and only on `(a, y)`. For fixed `a`, the
            edges of value `v` lie in the rectangle
            `f⁻¹(v) × h⁻¹(v)`, and these rectangles are disjoint. So
            `exists_dense_value_class` finds a value class with
            `|S|² ≤ |S_v|·((|X|+|Y|)/2)²`, and `exists_common_value`
            (`Proofs16CommonValue`) sums this by Cauchy–Schwarz into
            `Θ : A → V`. No connected components are needed.
         2. *Freiman-ness of `Θ` from the same Lemma 9.2.*
            `Θ(a) = ψ₀(x+a) − ψ₁(x)` reads as a separated family for
            `(f, g) = (Θ, ψ₀)` in the variables `(x+a, −x)`:
            `Θ((x+a) + (−x)) − ψ₀(x+a) = −ψ₁(x)`. So
            `freiman_common_value` (`Proofs16CommonValueFreiman`)
            restricts to popular `a` and applies `milicevic_lemma_9_2_pair`
            unchanged. The value set of that family is exactly the set of
            `a`'s, so `Θ` is Freiman on a dense set of differences, with
            no offset `u` to carry.

         The iteration invariant is also in place
         (`Proofs16SubsetSumIndependence`). `SubsetSumInjective V`
         (distinct `{0,1}`-subset sums) is `{-1,0,1}`-independence.
         `subsetSumInjective_insert` shows that adjoining `w ∉ ⟨V⟩_1` keeps
         it, which is what `Θ(a) ∉ S(x, a)` supplies.
         `card_le_of_subsetSumInjective` is the cap
         `2^|V| ≤ (2|V|R+1)^|Γ|` for `V ⊆ ⟨Γ⟩_R`.
         **The iteration terminates (kernel-checked):**
         `milicevic_prop_9_3_iteration` (`Proofs16PropNineThreeIteration`).
         - *State* (`PropNineThreeInvariant`). Maps `θ_i`, `i < m`, are
           Freiman 8-homomorphisms on domains `D_i`. For each pair
           `(x, a)` there is an index set `I_{x,a} ⊆ [m]` with `a ∈ D_i`,
           `θ_i(a) ∈ ⟨Γ_{x+a} ∪ Γ_x⟩_{2R}`, `i ↦ θ_i(a)` injective, and
           `{-1,0,1}`-independent values.
         - *Uniform radius.* `R = propNineThreeRadius (2d) M ρ`, with
           `2 ≤ ρM`. `escape_frequency_uniform` uses the rank-capped
           quarter-radius Theorem 27
           (`bohr_sum_contains_rank_cap_span_quarter`) in place of the
           set-dependent one, so one `R` serves every triple and no
           modulus condition appears.
         - *One round* (`milicevic_prop_9_3_round`). From `εN³` bad
           triples (`propNineThreeBad`: (24) fails at some `d`), escape,
           then `escape_split`, then `claim_9_4` with forbidden set
           `⟨θ_i(a) : i ∈ I_{x,a}⟩_1`. That set lies inside the bounded
           span over `I_{x,a} ∪ I_{y,a}`, by
           `spanBall_subset_boundedFrequencySpan`. The new `θ_m = Θ` is
           appended on `claimNineFourDensity ε R d · N²` pairs.
         - *Termination.* `propNineThree_index_card_le` caps every
           `|I_{x,a}| ≤ s₀` for any `s₀` with
           `2^s ≤ (4sR+1)^{2d} ⇒ s ≤ s₀`. `exists_good_of_potential` then
           reaches a state with fewer than `εN³` bad triples and
           `⌈δN²⌉·m ≤ N²s₀`, so `m ≤ s₀/δ`. The hypothesis
           `2s₀η ≤ 1/4` is the triangle-inequality condition of the
           escape step.

         **Claim 9.5 (kernel-checked):** `claim_9_5`
         (`Proofs16ClaimNineFive`).
         - *Coordinates.* A 12-tuple `(x[4], y[4], a[4])` with
           `a₀ + a₁ = a₂ + a₃` is stored as `u : Fin 11 → ZMod N`, with
           `a₃ = u₈ + u₉ − u₁₀` (`twelveX`, `twelveY`, `twelveA`).
           `twelveRest j` keeps the nine coordinates other than `x_j` and
           one `a`-coordinate. `twelve_agree_off` shows they determine the
           tuple off `x_j` (the index tables are checked by `decide`).
         - *Input.* Frequencies `ξ_{j,k}` in the span balls at the 16 points
           `x_j + a_j, x_j, y_j + a_j, y_j`, with
           `∑_j(ξ_{j,0} − ξ_{j,1}) = ∑_j(ξ_{j,2} − ξ_{j,3})`, and *some*
           `ξ_{j,0} − ξ_{j,1}` outside `S(x_j, a_j)`. This is what the
           escape gives: a sum of forbidden elements is excluded only if
           some summand escapes.
         - *Proof.*
           1. Select 16 maps (`exists_good_selection_indexed_le`, the
              `n`-point selection lemma), at a loss `K^(−16)`.
           2. Pigeonhole an escaping coordinate `j` on a quarter of the
              tuples.
           3. `F_j(x_j, a_j) = ∑_k G_k − ∑_{k≠j} F_k` is determined by
              `(a_j, twelveRest j u)`, so `exists_common_value_det` gives
              `Θ(a_j)`. Only one common value is needed, not one per
              coordinate as in Milićević's application of Lemma 9.2 to all
              16 maps.
           4. Each pair `(x_j, a_j)` carries at most `N⁹` tuples. Then
              `freiman_common_value` applies.
         - *Sharp counting.* `exists_common_value_sharp`
           (`Proofs16CommonValueSharp`) replaces the AM–GM factor
           `((|X|+|Y|)/2)²` by `|X|·|Y|`, through
           `∑_v √x_v √y_v ≤ √(∑x_v)√(∑y_v)`. With `|X| = N` and `|Y| = N⁹`,
           the AM–GM form would lose a power of `N`.
         - *Output.* The same shape as `claim_9_4`, with
           `claimNineFiveDensity ε R d = κ(c/2)²` and
           `c = (ε/(4K¹⁶))²`, again polynomial.

         **The full iteration terminates (kernel-checked):**
         `milicevic_prop_9_3_iteration` (`Proofs16PropNineThreeTwelve`),
         with both claims.
         - *Shared update.* `propNineThree_append`
           (`Proofs16PropNineThreeIteration`) appends any Freiman `Θ` whose
           values on the pairs of `P` lie in the span balls and escape the
           current `{-1,0,1}`-spans. Both rounds use it. The rank cap of
           the escape is now any `r ≥ 2d`, with one radius
           `R = propNineThreeRadius r M ρ`.
         - *Bad 12-tuples* (`propNineThreeBad12`). Some `d` is small
           against all current `θ_i(a_j)` but
           `d ∉ B(K_u; ρ) + B(L_u; ρ)`, where `K_u = ⋃_j(Γ_{x_j+a_j} ∪ Γ_{x_j})`
           (`twelveK`). Since `B(K_u; ρ) ⊆ ∑_j(B_{x_j+a_j} ∩ B_{x_j})`, a
           good 12-tuple satisfies Milićević's (26), so the stopping
           condition here is stronger than the paper's.
         - *Claim 9.5 round* (`milicevic_prop_9_3_round_twelve`).
           1. Theorem 27 at rank `8d ≤ r`.
           2. Cut `ξ` into sixteen pieces (`spanBall_biUnion_split` with
              `spanBall_union_split`).
           3. Some coordinate escapes, because the four forbidden spans add
              into the radius-4 span of all current values
              (`add_mem_spanBall_of_subset`, `sum_mem_spanBall_of_subset`),
              and the escape excludes that span. The escape's
              triangle-inequality condition is `32s₀η ≤ 1/4`.
         - *Termination.* With
           `δ = min(claimNineFourDensity, claimNineFiveDensity)`, the
           result is a state with fewer than `εN³` bad triples and fewer
           than `εN¹¹` bad 12-tuples, and `⌈δN²⌉·m ≤ N²s₀`.

         **Final selection, plan and first pieces.** The plan uses the
         corpus's column vocabulary: `L x y = φ_x(y)`, spectra `T`,
         `columnDifferenceMap L (x+a, x) = φ_{x+a} − φ_x`,
         `ColumnPairCompatible` (the quadruple `(x+a, x, y+a, y)` is
         Bohr-respected), and `ColumnTupleRespected` (an 8-tuple of
         columns is respected).
         - *F1, Lemma 9.1 per good pair (done).* `gluedPairMap`
           (`Proofs16GluedPairMaps`) is `bohrSumExtension` of the two
           column differences. `gluedPairMap_spec` makes it
           Freiman-linear on the quarter sum, normalized, and equal to
           each difference on its quarter Bohr set.
           `columnDifferenceMap_freimanOn` derives the hypothesis from
           per-column Freiman-linearity.
         - *F2, the deterministic heart (done).*
           `glued_quadruple_respected`. Suppose four compatible pairs
           `(P_j, Q_j)` have both 8-tuples respected, and `d = u + u'`
           with `u, u'` in the two tuple Bohr sets at quarter radius,
           which is our stronger form of (26). Then
           `ψ₀(d) + ψ₁(d) = ψ₂(d) + ψ₃(d)`, because each glued value
           splits as `ψ_j(u + u') = Δ_{P_j}(u) + Δ_{Q_j}(u')` and both
           8-tuples cancel. The statement is generic in the 8-tuples;
           the `a`-structure enters only when they are read off a 12-tuple.
         - *F3, choosing the pairs (done).* `exists_pair_choice_few_bad`
           (`Proofs16FinalPairChoice`) is the peer's
           `exists_independent_choice_few_bad_queries`
           (`Proofs16IndependentChoiceSelection`), read through
           `twelveOf q c`, the 12-tuple of a quadruple and its chosen
           pairs. `twelveOf` is injective on additive quadruples
           (`twelveOf_injective`). So for *any* set `Bad` of 12-tuples, some
           choice has at most `|Bad|/D` failing distinct-index queries.
           - Inputs: indices `I = A′` (the `a`'s); choice sets
             `F_a = {good pairs for a}`; queries `Q` = distinct additive
             quadruples `a[4]`; bad sets `B_q` = choice 4-tuples whose
             12-tuple is in `propNineThreeBad12` or whose x- or y-side
             8-tuple is not respected.
           - The bound: `∑_q |B_q| ≤ |Bad12| + 2N⁴·|unrespected 8-tuples|`,
             and `D = min ∏_j |F_{a_j}| ≥ (γN²)⁴`. So at most
             `(ε + 2ε′)N³/γ⁴` quadruples fail.
           - Repeated-index quadruples (at most `6N²`) are counted
             separately, as in J.147.
         - *F4, linear domains (done).* `exists_index_window`
           (`Proofs16FinalWindow`). Index sets `S_a ⊆ [m]` with
           `|S_a| ≤ k ≤ m` have a common `J ⊆ [m]` of size `k` containing
           `S_a` for at least `|A|/C(m, k)` of the `a`'s. The proof
           pigeonholes a `k`-superset of each `S_a`, which gives the same
           loss as Milićević's random `J`. Then
           `U_a = B(θ_i(a) : i ∈ J; η)` is linear in `a`, and it lies inside
           the domain built from `S_a` (`bohr_anti`), so every containment
           survives. Take `k = 2s₀`.
         - *F5, relating back (done).* `gluedPairMap_relate`: if the chosen
           pair `p` for `a` is compatible with `(z + a, z)`, the glued map
           equals `φ_{z+a} − φ_z` on the common quarter-radius Bohr set.
           This is the exact form of
           `|Z(φ_a − φ_{z+a} + φ_z)| ≥ (ρ/4)^{4d}|G₂|`; the Bohr lower bound
           gives the size.

         **Assembly design (and a trap avoided).**
         - *Order.*
           1. Run the iteration to a state with fewer than `εN³` bad
              triples and fewer than `εN¹¹` bad 12-tuples.
           2. Call a pair `(x, y)` good for `a` when
              `(x+a, x, y+a, y)` is compatible and the triple is not bad.
              Let `A′ = {a : |G_a| ≥ N²/2}`. By Markov,
              `|A′| ≥ (1 − 2(ε + ε₁))N`, where `ε₁N³` bounds the
              incompatible quadruples of the input.
           3. Choose the pairs by F3 with
              `Bad = Bad12 ∪ {12-tuples with an unrespected 8-tuple}`.
              Then `|Bad| ≤ (ε + 2ε₂)N¹¹`, where `ε₂N⁷` bounds the
              unrespected 8-tuples, and `D = (N²/2)⁴`. So at most
              `16(ε + 2ε₂)N³` distinct quadruples in `A′` fail. Every
              other quadruple is respected by the glued maps on
              `⋂_j U_{a_j}`, by F2.
           4. Choose `J` *for quadruples*, not for single `a`'s: apply
              `exists_index_window` to the respected quadruples `q`, with
              `S_q = ⋃_j (I_{x_{a_j},a_j} ∪ I_{y_{a_j},a_j})`, `|S_q| ≤ 8s₀`.
              The output set is `X = {a ∈ A′ : S_a ⊆ J}`. It contains all
              four entries of at least `C(m, 8s₀)^(−1)·#respected`
              quadruples, which also bounds `|X|` from below.
         - *The trap.* Choosing `J` to maximize `|X|` first, and only then
           counting respected quadruples inside `X`, is circular. The
           failure bound would need `ε ≪ C(m, k)^(−4)`, but `m ≤ s₀/δ(ε)`
           grows as `ε` shrinks. Choosing `J` for quadruples is why
           Milićević takes `|J| = 8s₀`. With it, `ε, ε₁, ε₂` only need to
           be small absolute constants.
         - *Counting quadruples in `A′`.* No energy bound is needed. Since
           `A′` has density `1 − O(ε + ε₁)`, at least
           `|A′|³ − |ℤ/N ∖ A′|·N²` triples `(a₀, a₁, a₂)` in `A′` have
           `a₀ + a₁ − a₂ ∈ A′`. Repeated-index quadruples number at most
           `6N²` (`repeated_additive_quadruples_card_le`).
         - *Identification.* `twelveK Γ u` is `columnTupleFrequencies T v`
           for the x-side 8-tuple `v` of `u`. So "not bad" is exactly F2's
           split hypothesis `hd` at radius `r/4`: run the iteration at
           `ρ = r/4`.
         - *Tools (done, `Proofs16FinalAssemblyTools`).*
           - `columnTupleFrequencies_twelveXSide` / `…YSide`: the
             identification above.
           - `exists_quadruple_window`: the window chosen for quadruples,
             `|J| = 4k`.
           - `dense_additive_quadruples_ge`: at least
             `|A|³ − (N − |A|)N²` additive quadruples in `A`
             (`additiveQuadruplesIn`).
           - `markov_large_fibers`: at least `(1 − 2η)N` values of `a`
             have `|G_a| ≥ M/2`.
         - *Deterministic links (done, `Proofs16PropNineThreeGlue`).*
           - `good_pair_domain` (Lemma A): a good pair's glued map is
             Freiman-linear on a domain containing
             `B(θ_i(a) : i ∈ J; η)` for every `J ⊇ I_{x,a} ∪ I_{y,a}`.
           - `twelve_good_respected` (Lemma B): a quadruple whose 12-tuple
             is not bad, has both 8-tuples respected, and has compatible
             chosen pairs, is respected by the glued maps (`chosenGlued`)
             on `⋂_j B(θ_i(q_j) : i ∈ J; η)`.

         **Proposition 9.3 is kernel-checked:** `milicevic_prop_9_3`
         (`Proofs16PropNineThree`). It depends only on `propext`,
         `Classical.choice` and `Quot.sound`.
         - *Input.*
           - Column maps `L x`, Freiman-linear on `B(T x; r)` with
             `L x 0 = 0`, `|T x| ≤ d`, `0 < r < 4`.
           - At most `ε₁N³` incompatible quadruples
             (`incompatibleTriples (colComp T L r)`).
           - At most `ε₂N¹¹` 12-tuples with an unrespected x- or y-side
             8-tuple.
           - The iteration parameters: a rank cap `rk ≥ 8d`; `M` with
             `2 ≤ (r/4)M`; `s₀`; `η` with `32s₀η ≤ 1/4`; `ε > 0`; and
             `5ε₁ + ε ≤ 1/2`.
         - *Output.*
           - `θ_i` Freiman 8-homomorphisms on `D_i` for `i < m`, and a
             window `J` with `|J| = 8s₀`.
           - A set `X` and chosen pairs `c(a)`. Every index `a` uses lies
             in `J`, below `m`, and has `a ∈ D_i`.
           - `ψ_a = chosenGlued T L r c a` is normalized and Freiman-linear
             on `U_a = B(θ_i(a) : i ∈ J; η)`.
           - Relating back: `x_a` is compatible with at least `N/2`
             columns `z`, and `ψ_a = φ_{z+a} − φ_z` on the common quarter
             Bohr set.
           - `C(m + 8s₀, 8s₀) · #{respected additive quadruples in X} ≥
             ((1 − 2η′)³ − 2η′ − 16(ε + 2ε₂))N³ − 6N²`, with
             `η′ = 5ε₁ + ε`.
           - `⌈δN²⌉·m ≤ N²s₀`.
         - *Audit.*
           - The count bound is positive for small `ε, ε₁, ε₂`, so `X` is
             not empty.
           - Indices `i ≥ m` in `J` carry `θ_i = 0` from the iteration's
             initial state, so they add no constraint.
           - **Open point, domain coherence.** For `i ∈ J ∖ S_a` with
             `i < m`, nothing ensures `a ∈ D_i`. So `θ_i` need not be
             Freiman on a set containing `X`. Respected quadruples are
             unaffected, since extra frequencies only shrink `U_a`. But
             Prop 10.1 needs the `Θ_i` Freiman on one domain `C ⊇ X`.
             Milićević's coset-progression domains raise the same
             intersection question, and the printed proof does not
             address it.
           - Candidate repairs:
             (i) choose `J` among quadruples whose entries lie in
             `⋂_{i∈J} D_i`, which needs a density argument for
             intersections of the `D_i`;
             (ii) replace each `θ_i` by its Lemma 7.8 linear extension on
             a Bohr set (`freiman_common_value` already yields one), and
             intersect Bohr sets, which have polynomial-density
             intersections.
           - Option (ii) looks natural: the linear parts are Freiman
             2-homomorphisms on `B(spec; ρ′)`, and an intersection of
             `8s₀` such Bohr sets has density `≥ ∏ρ′^{|spec|}`.
           - Recorded under "Further questions (Step 5)" below until settled.
         - *Regime check against the contract.* `DeepStructureAt Bnd`
           bounds ranks (`|Γ|, |Ψ|, r`) by `Bnd(c)`, and radius and
           agreement density from below by `exp(−Bnd(c))`, with
           `Bnd ≤ (4/c)^K`. So polynomial ranks and `exp(−poly)` densities
           are what is required. Proposition 9.3's output fits:
           - rank `|J| = 8s₀ = poly(d, log 1/r)`;
           - radius `η ≈ 1/s₀`;
           - `log(1/density) ≈ 8s₀·log m`, with `m ≤ s₀/δ` and
             `log(1/δ) = O(d log R)`, also polynomial.

           An explicit-exponent audit is still to be written.

         **Further questions (Step 5).**
         1. *Domain coherence.* The final structure needs frequency maps
            Freiman-linear on one centered Bohr set
            (`IsFreimanLinearOn (bohr Ψ ρ) (L i)` in
            `MilicevicDeepVarietyStructure`). The current `θ_i` are Freiman
            8-homomorphisms on uncentered dense sets `D_i`, and `a ∈ D_i`
            is known only for `i ∈ S_a`.
            - *Partial repair.* Following the paper's `θ = φ^lin − u`:
              `shift_agreement` gives `ψ₁ = Ψ + u` on a dense fiber, and
              Lemma 7.8 gives `Ψ`'s linear part `λ` on a centered Bohr set
              `K`. Then `Θ(a) = λ(a) − u` wherever `x, x + a` lie in `Ψ`'s
              affine domain and `a ∈ K`. So the new frequency map can be
              taken affine on a centered Bohr set.
            - *What this does not settle.* It still does not put `a ∈ K_i`
              for `i ∈ J ∖ S_a`.
            - *A dead end.* Localizing every round to `⋂_{i≤m} K_i` would
              multiply the rank by `m`. Since `m = exp(poly)`, the density
              would become doubly exponential.
            - *The paper.* Milićević's statement intersects the coset
              progressions of the `J` maps, but the printed proof does not
              show that `X` meets the intersection with many quadruples.
              Possibly every `C_i` contains the small `C₀` in which the
              `a`'s live. That would need the Theorem 2.26 progressions to
              contain `C₀`, which is not stated.
            - *The ε-proportionality principle (2026-10-10).* Every
              candidate repair has failed in the same way.
              - The candidates: per-round localization; a pigeonholed
                common index set `S*`; a common translate `s + ⋂K_i` with
                local quadruple counting; recentring through the affine
                linear parts `L_i = λ_i + u_i` on `⋂K_i`.
              - Each pays a factor built from the iteration's output: the
                round count `m`, or the ranks of the `K_i`, which are
                `polylog(1/δ)` with `log(1/δ) ≥ 9316·log(1/ε)`. The
                failing-quadruple bound `O(ε)N³` must then beat that
                factor. So `log(1/ε)` must exceed a power `> 1` of
                `log(1/ε)`, which is circular.
              - Milićević's window is the one step that escapes: it loses
                the same factor `C(m, 8s₀)⁻¹` on good and failing
                quadruples alike.
              - So a repair of coherence must likewise be *proportional*.
                It must select domains by an operation that scales good
                and failing configurations equally, or produce domains
                (such as a fixed `C₀ ⊆ C_i`) whose size does not depend on
                the iteration.
              - With affine `L_i = λ_i + u_i` on centred `K_i`, everything
                reduces to one question: can the `a`'s be confined in
                advance to a centred set contained in every `K_i`?
              - *Quantified obstruction.*
                - Localizing to a common Bohr-type piece costs at least
                  `exp(−C·rank(⋂_{i∈J} K_i)) ≥ exp(−C′·s₀·(log 1/δ)⁴)`,
                  with `log(1/δ) = O(d log R) + 9316·log(1/ε)`.
                - The failure count `O(ε)N³` must beat it. So
                  `log(1/ε) ≳ s₀·(log 1/δ)⁴ ≥ s₀·(9316·log 1/ε)⁴`, which
                  is impossible.
                - Extending each `θ_i` from its dense `B_i` to the whole
                  `C₀` is also impossible in general. A Freiman map on a
                  dense set extends only to the thickening `B_i + K_i`.
                  The same holds for maps on low-rank Bohr sets: they are
                  linear forms in the GAP coordinates, not global
                  multiplications `x ↦ t·x`.
              - *Status against the paper.* The overview (p. 12) states
                Step 5's output as `Θ₁, …, Θ_r` Freiman-linear on the whole
                index progression `C`, with the index set becoming a dense
                `X ⊆ C`. Proposition 9.3 states `Θ_i` on a coset
                progression `C′` with `X ⊆ C′`. But the printed proof
                produces each `θ_i` on its own Theorem 2.26 progression
                `C_i`, and never shows that `X` meets `⋂_{i∈J} C_i` in a
                set carrying many respected quadruples. By the bound above,
                this cannot follow from any localization whose cost depends
                on the iteration. **This appears to be a gap in the printed
                proof of Proposition 9.3**, not only in our formalization.
                Resolving it needs a new idea, or a different Step 5.
              - *Where the gap comes from (2026-10-10).* In the vector-space
                predecessor (`F_p^n`), the `θ_i` are linear maps on
                subspaces of bounded codimension. A linear map on a
                subspace always extends to all of `F_p^n`, so coherence is
                free there: every `θ_i` is defined everywhere and `X` lies
                in every domain. The general-group version replaces
                subspaces by coset progressions or Bohr sets, and this
                extension step fails.
              - *Checked in ℤ/N.*
                - Take a Freiman-linear map on a sub-Bohr set
                  `K = C₀(ν) ∩ B(Γ′)` of a proper progression `C₀`. It need
                  not extend to `C₀` even when `C₀` has rank 1. `K`'s index
                  set in `ℤ` is a Bohr set of `ℤ`, roughly a proper rank-2
                  progression `{m₁q + m₂r′}`. A Freiman-linear map there is
                  `m₁v₁ + m₂v₂`, which need not be a function of `n`
                  linearly.
                - The lattice route fails too. The relevant sublattice
                  `{n : ⟨n, w_γ⟩ ≡ 0}` has index a power of `N`, so the
                  "invertible index" extension is unavailable. Quantitative
                  lattice regularization (Milićević §2.6, Lemma 2.32 and
                  Theorem 2.33) could at best control *small* relations; it
                  does not make the extension exist.
              - *What a repair must supply.* Either:
                (a) new frequency maps that are born Freiman on one fixed
                    centred set `C₀ ⊇` all `a`'s. Claims 9.4/9.5 only define
                    them on the escaping `a`'s plus Bohr thickenings; or
                (b) a Step 6 (Proposition 10.1) that works with per-column
                    index sets `S_a ⊆ J`, with `θ_i` Freiman only on its own
                    `D_i ∋ a` for `i ∈ S_a`, rather than with one uniform
                    Freiman `Θ` on `C`.

                Both remain research questions. The F_p^n argument does not
                transfer verbatim to general abelian groups at this step.
              - *How [49] gets coherence (Discrete Analysis 2024:20, p. 31,
                after Corollary 20).* It uses Hosseini–Lovett averaging.
                1. Only `ℓ₀ = log^O(1)` of the `m` maps cover each `U_y`.
                2. Average over `ℓ₀`-subsets to pin the patterns
                   `I_{y+z} = J₁`, `I_z = J₂`, `I_{y+w} = J₃`,
                   `I_{w} = J₄`, then *fix* `z, w`.
                3. For the varying `y`, every `J₁`-map is defined at
                   `y + z`, because its index was used there. So
                   `Y² ⊆ ⋂_{J₁}(C_i − z) ∩ ⋂_{J₃}(C_i − w)`.
                4. Proposition 18 then finds one proper coset progression in
                   that intersection that meets `Y²` densely.

                This works there because the target is a dense set with a
                *pointwise* property. Pinning loses a proportional factor,
                and no failure count has to be beaten.
              - *The analogue for Proposition 9.3: fix the final pair.*
                - Choose one pair `(x*, y*)` for *all* `a`, rather than
                  `(x_a, y_a)` per `a`. Then `S_a = I_{x*,a} ∪ I_{y*,a}`, so
                  pinning `S_a = J*` gives coherence exactly as in [49].
                - The containment (24) for the triples `(x*, y*, a)` costs
                  only an average over `(x*, y*)`, which is proportional.
                - The x-side 8-tuples become original quadruples
                  `(x* + a_j)_j`, also proportional.
                - The obstruction is (26). It is now needed on *diagonal*
                  12-tuples (`x_j = x*`, `y_j = y*`). There are `N⁵` of
                  these against `N¹¹` general ones, and the iteration
                  controls only the general ones.
                - A diagonal Claim 9.5 loses the two-sided separation that
                  makes the new map Freiman. With a shared `x`, the value
                  `F_j(x, a_j)` is determined only together with `x`, through
                  the other coordinates `F_k(x, a_k)`.
                - Grouping coordinates restores separation only for sums
                  such as `ψ₀ + ψ₃(· + a₁ − a₂)`. The iteration's
                  pair-level escape needs a single coordinate.
                - Open sub-questions: a diagonal Claim 9.5 with a
                  grouped-coordinate invariant, or a derivation of diagonal
                  (26) from (24) using Lemma 2.40-type genericity of the
                  frequencies.
         2. *Explicit exponents (done, `Proofs16PropNineThreeBudget`).*
            With `L = d·log(2R+1)` and `ℓ = log(1/ε)`:
            - `log(1/claimNineFourDensity) ≤ 6540·log 2 + 37264·L + 9316·ℓ`;
            - `log(1/claimNineFiveDensity) ≤ 25172·log 2 + 149056·L + 9316·ℓ`;
            - the window loss satisfies `C(m + k, k) ≤ (m + k)^k`.

            So `log(1/final density) = O(s₀·log(s₀/δ))`, which is
            polynomial in `d`, `log R` and `log(1/ε)`. Here
            `R = propNineThreeRadius` is `(r/4)^(−O(d))`. This confirms the
            regime check.
         3. **The rank obstruction, and why Theorem 2.26 is needed here
            (2026-10-10).** Domain coherence hides a rank problem.
            - *The obstruction.* In Claims 9.4/9.5 the Freiman step runs at
              density `κ = 2^(−1882)((c/2)^4)^1164·…` with
              `c = (ε/K⁴)²` and `K = (2R+1)^d`, so `κ = exp(−poly(d))`. The
              polynomial substitute for Theorem 2.26 (Corollary 7.6 +
              Lemma 7.8, as in `milicevic_lemma_9_2_pair`) puts the linear
              part on a Bohr set of rank `16κ^(−2) = exp(poly(d))`. But the
              deep contract needs the frequency maps Freiman-linear on
              `bohr Ψ ρ` with `|Ψ| ≤ Bnd(c) ≤ (4/c)^K`. So any structured
              domain built from the substitute violates the contract.
            - *What suffices.* Sanders-strength Theorem 2.26 gives rank
              `(log 1/κ)^O(1) = poly(d)`, which fits. So at this step the
              Milićević route cannot use the polynomial substitute.
            - *Available input.* `lib/openai-math` already supplies the
              Sanders-type estimate in `ℤ/N`:
              `OAI.Erdos3.CyclicCrootSisask.exists_quartic_bogolyubov`
              (`Estimates/LocalizedSiftingAlmostPeriods`). For `A` of
              density `e^(−p)` it gives a rank-regular Bohr set in
              `2A − 2A` with rank `≤ 1 + C(p+1)⁴` and radius
              `≥ exp(−C(p+1))`. The `…_progression` variant gives a proper
              centred GAP of the same rank with volume
              `exp(−C(p+1)⁸)N`. The corpus already uses these: Theorem 7.1
              in `Proofs07FreimanClosure`, via `exists_dense_cyclic_model`
              and `exists_bounded_affine_box_of_cyclic_model`, and the
              peer's `Proofs16RobustDifferenceBohr`.
            - *Plan, "Theorem 2.26 at Sanders strength" in `ℤ/N`.*
              1. Start from an approximate homomorphism: many respected
                 quadruples, i.e. the graph has energy `≥ c|A|³`.
              2. The graph BSG, which is polynomial (Proposition 7.3 /
                 `abstract_bsg_core`), gives a graph piece of doubling
                 `poly(1/c)`.
              3. A dense cyclic model of order 8 follows from
                 `exists_dense_cyclic_model`.
              4. The Bogolyubov affine box in the model comes from
                 `exists_bounded_affine_box_of_cyclic_model`, with rank
                 `polylog(1/c)`.
              5. Pull back: the graph meets a low-rank affine box. On it
                 the graph is the graph of a Freiman-affine function,
                 because a graph piece projects injectively.

              This replaces Lemma 7.8 wherever a structured domain must
              have low rank, and is the next large task on this route.
            - *Done (2026-10-10): the low-rank half needs no graph model.*
              - `sanders_linear_part` (`Proofs16SandersLinearPart`) is
                Lemma 7.8 at Sanders strength.
              - A Freiman 8-homomorphism `f` on `A` of density `e^(−p)`
                extends to `ψ` on `2A − 2A` by
                `ψ(a₁+a₂−a₃−a₄) = f a₁ + f a₂ − f a₃ − f a₄`
                (`quadSumExt`).
              - `ψ` is well defined for a Freiman 4-homomorphism, and is
                Freiman-linear on `2A − 2A` for a Freiman 8-homomorphism.
              - `f a − f a′ = ψ(a − a′)` holds for *all* `a, a′ ∈ A`.
              - `exists_quartic_bogolyubov` puts a Bohr set of rank
                `≤ 1 + C(p+1)⁴` inside `2A − 2A`.
                `bohr_subset_oai_carrier` converts its chord radius `ρ` to
                the corpus's phase radius `ρ/(2π)`.
              - `freiman_common_value_sanders`
                (`Proofs16CommonValueSanders`) attaches this to the new map
                of Claim 9.4. `Θ`'s linear part lives on a Bohr set of rank
                `1 + C(log(1/δ) + 1)⁴`, polylogarithmic in the density `δ`
                of its value set, which satisfies `|B| ≥ δN`.
              - *Bohr thickenings (done).* `freiman_bohr_thickening`
                (`Proofs16FreimanThickening`). Suppose
                `bohr Γ ρ ⊆ 2A − 2A`. Then a Freiman 8-homomorphism `f`
                on `A` extends, by `f̂(b + k) = ψ(k) + f(b)`, to a map that
                is Freiman-linear on `A + B(Γ; ρ/4)`. So each `θ_i`
                is Freiman on a structured, Bohr-thickened domain.
              - Domain coherence (item 1) remains open: it is not known
                whether `X` can be placed in all `J` thickenings at once.
                Localizing every round would make the rank or density
                doubly exponential. Theorem 2.26's progressions are
                arbitrary coset progressions, so the printed argument has
                the same gap.
         Quantitatively, `s₀ = O(d log(dR))`, and
         `δ` is polynomial in `ε` and `(2R+1)^(−d)`. With
         `R = (ρ^(−1))^O(d)`, this makes `m ≤ s₀/δ = exp(O(d² log 1/ρ))`
         rounds: exp-poly in `d` and `log 1/ρ`, as in the paper.
       - **Termination.** Each round raises some `|I_{x,y}|` on a dense set
         of pairs, and the size is capped at `s₀`. So the iteration stops
         after polynomially many rounds.
       - **Final selection.** Choose one good pair `(x_a, y_a)` per `a`,
         by averaging. Glue by Lemma 9.1 (`compatible_bohr_sum_quadruple`,
         J.112). A random index set `J` of size `8s₀` makes `U_a` linear
         in `a`, at loss `C(m, 8s₀)^(−1)`, again by averaging.
   - *Step 4 done (kernel-checked).* `signed_sum_zero_of_small_image`
     (`Proofs16StepFourPrime`): a signed sum `∑ s_j·f_j` of normalized
     Freiman-linear maps with at most `K < N` values on `B(⋃ T_j; ρ)`
     vanishes on `B(⋃ T_j; ρ/K)`. This holds for every such tuple, with no
     added frequencies, random characters or `ε` loss.
     `IsFreimanLinearOn.const_mul` and `IsFreimanLinearOn.finset_sum`
     are the closure lemmas.
   - *Audit of the BSG route (kernel-checked).*
     `globalColumnQuadrupleDensity_ge` (`Proofs16ColumnBSGGrowth`):
     `γ ≥ 2^(-30121)·(α/2)^74500 / 13^(4d)`. So
     `log(1/γ) ≤ 4d·log 13 + O(log(1/α))`, polynomial in `1/α`, since
     `d ≤ 16/β² + 1`. Every BSG loss downstream is polynomial in `γ`
     and `α`. Compare the triple-exponential guarantee of the
     model-elimination core.
     The radii stay in the same regime. `zeroLadderRadius_ge` gives
     `ρ_n ≥ u^((16D+1)^n)` for `u = min(1/2, ρ₀/5, ρ₁)`, from
     `refinementKernelRadius_ge`:
     `refinementKernelRadius d e ρ r ≥ (ρ/2)(ρ/5)^d (r/2)^(d+e)`. So
     `log(1/ρ₁₆) ≤ (16D+1)^16 · log(1/u)`, a fixed power of `D`.

J.5 revisited assumed that the remaining pipeline steps "lose no more
than polynomially". The model-elimination stage built since (J.109–J.111)
does not. `Proofs16ZeroCoreGrowth` bounds the density that
`global_column_shifted_agreement` guarantees, from the definitions alone.
Write `d = columnSpectrumCap (columnEightDensity alpha)`, about
`2^13080·alpha^(-9312)` (J.5 revisited dropped the `alpha/2` halving).

1. **The word density is exponentially small.** Every density in the
   anchor/walk/word chain is at most the witness density
   `columnWitnessDensity ≤ 13^(-d)` (`globalColumnWordDensity_le_witness`,
   `columnWitnessDensity_le`).
2. **That density becomes a rank.** `globalColumnModelRank = ⌈4d/δ⌉`
   divides by the word density `δ`, so the rank is at least `13^d`
   (`thirteen_pow_le_globalColumnModelRank`). The guaranteed rank bound
   for the final column spectra, `g + d`, is therefore already
   exponential in `1/alpha`, beyond every polynomial `Bnd`.
3. **The rank becomes an exponent.** The test density is
   `1/(4·⌈2/r⌉^(g+d)) ≤ 2^(-g)` (`modelTestDensity_le_inv_two_pow`; every
   cell count is at least two because `r ≤ 1/(4π)`).
4. **The test density becomes a round count.** Elimination runs
   `⌈log(M+1)/β⌉ ≥ 2^g/2` rounds, and each costs a factor `β/10 ≤ e^(-1)`.
   So the zero-core density is at most `exp(-2^g/2)`
   (`globalColumnZeroDensity_le`).

Hence `globalColumnAgreementDensity alpha ≤ exp(-2^(13^d)/2)`
(`globalColumnAgreementDensity_le_triple_exp`): triple-exponentially small
in a polynomial of `1/alpha`. In particular, for `alpha ≤ 1/2` and every
`K ≤ 2^64`,

```
globalColumnAgreementDensity alpha < exp(-(4/alpha)^K)
```

(`globalColumnAgreementDensity_lt_polynomial_contract`). The right side is
the agreement that `DeepStructureAt Bnd` requires at density `alpha` when
`Bnd alpha ≤ (4/alpha)^K`, the hypothesis of
`theorem_16_2_at_three_of_eventually`.

**What this does and does not show.**
- These are upper bounds on the *guaranteed* density, not on the actual
  agreement set. The shortfall is not a matter of constants: the
  structure side needs `log(1/density)` polynomial in `1/alpha`, and here
  it is at least `2^(13^d)`.
- The same rank also enters the zero-core radius:
  `globalColumnZeroRadius ≤ (ρ/2)/(⌈4/ρ⌉^g·…)`, which is doubly
  exponentially small. The contract's `exp(-Bnd c) ≤ ρ` therefore fails
  too (kernel-checked in `Proofs16CoherentAnchorGrowth`). Both zero-core
  radii are at most `2^(-g)` (`globalColumnZeroRadius_le_inv_two_pow`,
  `globalEvenColumnZeroRadius_le_inv_two_pow`). So any `B` with `exp(-B)`
  at most the radius of `global_column_shifted_agreement` or of
  `global_coherent_column_anchors` has `B ≥ 13^d/2`
  (`globalColumnZeroRadius_bound_ge`, `globalCoherentAnchorRadius_bound_ge`).
  `global_column_difference_extensions` (J.112) works at exactly this
  rank and radius. The even-length variant
  (`Proofs16GlobalEvenZeroCoreParameters`) has the same shape: rank
  `⌈2k·d/δ⌉` and per-round factor `β/(5k)`.
- **The current mainline inherits it (kernel-checked).**
  `global_coherent_column_anchors` (J.129) starts from the even core at
  length four. `Proofs16CoherentAnchorGrowth` proves that
  `globalEvenColumnZeroDensity alpha k` (every `k ≥ 1`),
  `globalCoherentAnchorDensity` and `globalCoherentAnchorTolerance` are at
  most `exp(-2^(13^d)/2)`, and that `globalCoherentAnchorRank ≥ 13^d`.
  `globalCoherentAnchorDensity_lt_polynomial_contract` is the
  contract comparison for the anchor density. J.129 itself notes that no
  polynomial bound on these composite parameters is asserted. These
  results show that none is available.
  `global_single_coherent_progression`, which the later global modules
  (`GlobalCoherentBridge`, `…WordSystem`, `…RichSystem`, `…RobustSystem`,
  `…Graph`) import, is stated entirely in these parameters:
  - `z = globalEvenColumnZeroDensity alpha 4`, together with `z^8/4`,
    `globalPopularAnchorTolerance = z^16/20` and the anchor density;
  - the even rank and the even radius.

  `global_single_progression_parameters_le` (`Proofs16SingleProgressionGrowth`)
  bundles their bounds: each density is at most `exp(-2^(13^d)/2)`, the
  rank is at least `13^d`, and the radius forces `B ≥ 13^d/2`.
  The shared steps are generic in `Proofs16ZeroCoreGrowth`:
  - `thirteen_pow_le_rank_ceil` covers any rank `⌈m·d/δ_k⌉` with `m ≥ 1`;
  - `elimination_density_le` covers any per-round divisor `m ≥ 1`;
  - `lt_polynomial_contract_of_le_triple_exp` does the final comparison.
- Later stages that start from this agreement set can only lose more,
  so the present chain cannot supply the polynomial contract however the
  bilinear organization is finished. Nor can it supply Milićević's
  quasi-polynomial form.
- It does not show that no route can. The two blow-ups come from two
  design choices, and each repair alone removes exactly one exponential
  (triple to double):
  - **Rank.** The common spectrum `⌈4d/δ⌉` charges `4d` frequencies to
    each of up to `1/δ` packed models (J.108). A rank `poly(1/alpha)`
    needs `δ ≥ poly(alpha)`, or models that share frequencies. Then
    `β = exp(-poly)`, but `t = log M/β = exp(poly)` rounds still cost
    `exp(-exp(poly))`.
  - **Elimination.** Each round keeps `β/10` of the columns and kills
    only a `β` fraction of the models, so the total cost
    `(β/10)^(log M/β)` is exponential in `1/β`. The requirement is a
    total cost `β^O(log M)`, i.e. each round must kill a *constant*
    fraction of the active models at column cost `β^O(1)`.
    - Killing `β^O(1)` per *model* is not enough, since there are
      `M = ⌈1/δ⌉ = exp(poly)` models.
    - Nor is "β polynomial in `1/alpha`" available: `β` is a Bohr-set
      density, exponentially small in the rank.
    - Counting tests relative to the common Bohr set `B(Γ;·)` would
      remove `g` from `β` but leave `d`. It fixes the rank's
      contribution, not the `1/β` round count.
- With both repaired (rank `poly`, total cost `β^O(log M)`), the stage
  would lose `exp(-poly(1/alpha))`. That is the polynomial-`Bnd` regime
  J.5 revisited assumed. No such elimination scheme is proposed here.

**Leads for the redesign** (heuristic, not proved)
- *E = {0} is not the expensive part in Milićević's proof.* J.2 records
  that his Freiman bihomomorphism on a bilinear Bohr variety, the form
  `DeepStructureAt` asks for, is an intermediate object of his §§5–11,
  with quasi-polynomial bounds. Only his final step extends it to the
  `E`-bihomomorphism (`SetRankLE E r`) of Theorem 1.4. J.2 also shows that
  the consumers cannot use the `E`-form directly (the readout (R) is not
  elementary). So the contract's `{0}` is right, and the cost of reaching
  it here comes from this pipeline's route, not from the target.
- *Constrain rather than delete: Milićević's own mechanism.* His
  Proposition 8.1 (arXiv:2601.01682, printed pp. 61–62) reaches the zero
  relation without touching the index set.
  - **Hypothesis.** Freiman-linear maps `φ_x : B_x → H` are indexed by a
    proper coset progression `C`, with Bohr sets of codimension `≤ d` and
    radius `ρ`. Every alternating `2k`-sum takes **at most `K` values** on
    the intersection of its domains.
  - **Construction.** Draw `m = O(log(kK/(εc)))` random characters
    `χ_i` of `H` and set `U_x = {y ∈ B_x : χ_i(φ_x(y)) ∈ (-1/20k, 1/20k) ∀ i}`.
  - **Why it works.** A nonzero value `h` attained on `∩ U_{x_i}` must
    have every `χ_i(h)` small, which has probability at most `2^(-m)`.
    So all but an `ε` fraction of the chosen tuples vanish identically
    on `∩ U_{x_i}`.
  - **Cost.** `U_x` contains a Bohr set of codimension
    `(2d·log(kK/(εc)))^O(1)` and radius `(2kd·log(1/ε))^(-O(1))` (his
    Lemma 2.37). `C` is unchanged ("C is not modified by this choice").
    His Step 6 (§10, abstract Balog–Szemerédi–Gowers) then passes from
    `1-ε` of the tuples to all of them.
  - **Comparison.** Here the cost of `K` nonzero values is
    `O(log K)` extra frequencies. The present pipeline pays a column
    factor `(β/10)` per test and `log M/β` tests.
  - **Precondition.** The *bounded image* is decisive. A nonzero
    Freiman-linear model has a large image, and constraining
    `χ_i(f(y))` to be small leaves `f(y)` in a Bohr set of `H`, which
    still contains nonzero elements unless `m ≈ log N`. So Proposition 8.1
    does not apply to J.109's models directly. Milićević gets the bounded
    image beforehand: `#Im ≤ K` for the alternating sums (his Steps 1–3,
    §§5–7: a variant of rank-`O(1)` respectedness, abstract BSG and robust
    Bogolyubov–Ruzsa onto `C`).

  So the most direct redesign is to aim the J.108 stage at bounded-image
  alternating sums rather than at a packing of linear models. Then a
  Proposition 8.1 analogue can kill the nonzero values at polylog
  codimension cost.

  *Formalized core (2026-10-09).* `Proofs16CharacterRefinement` proves the
  deterministic selection behind Proposition 8.1 by averaging over all
  `N^m` character tuples, with no probability.
  - `exists_character_refinement`: suppose each signed sum
    `∑ j, s j * f q j y` (signs `±1`) takes at most `K` values on
    `⋂ j, B q j`. Then some `χ : Fin m → ZMod N` makes it vanish on the
    refinements `characterRefinement χ n (B q j) (f q j)` for all but
    `K·|Q|/2^m` of the indices `q`. The index set is not shrunk.
  - `nonseparating_tuples_card_le` and `not_separates_signed_sum` are the
    two ingredients.

  Still open: the Bohr-set containment of the refined domains and the
  bounded-image input. The containment is Milićević's Proposition 2.37
  ("Bohr–Bohr sets are Bohr", printed p. 31).
  - **Statement.** For a Freiman-linear `ψ : B(Γ;ρ) → T^d`, the set
    `{x ∈ B : ‖ψ(x)‖ ≤ ε}` contains a Bohr set of codimension
    `d + (2r·log(1/(ερ)))^O(1)` and radius `ε·(2r·log(1/(ερ)))^(-O(1))`,
    where `r = |Γ|`.
  - **Proof.** A proper coset progression `C ⊆ B` (his Prop. 2.35); a
    homomorphism approximating `ψ` on a sub-progression (Lemma 2.22); a
    Bohr set inside that sub-progression (Prop. 2.13); then add the
    approximating characters as frequencies.
  - **What the corpus has, for ℤ/N.**
    - A proper progression inside a Bohr set:
      `exists_proper_progression_in_bohr`, through the OAI port.
    - Coordinate affinity of Freiman-linear maps on it:
      `freiman_linear_gap_affine`.
    - Simultaneous Dirichlet: `simultaneous_small_multiplier`.
  - **What is missing.** The reverse inclusion, a Bohr set inside a proper
    progression (Prop. 2.13). In ℤ/N a Freiman-linear map on a rank-`r`
    Bohr set is `∑ nᵢ(y)·bᵢ` in progression coordinates. So the refined
    set is a *generalized* Bohr set, and recovering an ordinary Bohr set
    inside it is a geometry-of-numbers step. It is the next formalization
    target if this redesign is pursued.
  - **Starting point.** The OAI port's
    `OAI/Combinatorics/Progressions/Fourier/QuarticBohrProgression.lean`
    proves only the forward inclusion
    (`bohrCyclicProgression_carrier_subset`). But it builds that
    progression from successive minima (`minkowskiSecondConstant`), the
    lattice machinery the reverse inclusion would reuse.

  **Correction (same day): in ℤ/N neither step is needed.** For `N`
  prime, `freiman_small_image_zero` (`Proofs16PrimeSmallRange`, J.97)
  already turns a bounded image into exact vanishing, with no new
  frequencies: a normalized Freiman-linear map on `B(T;ρ)` with at most
  `K < N` values is zero on `B(T;ρ/K)`.
  - An alternating sum `∑ ±φ_{x_i}` is Freiman-linear on the common domain
    `⋂ B(T_{x_i};ρ) = B(⋃ T_{x_i};ρ)`. So a bound `K` on its image gives
    the zero relation at radius `ρ/K`, which costs `log K` in
    `log(1/radius)` and nothing in codimension.
  - Milićević needs random characters and Proposition 2.37 only because
    a general finite abelian group has small subgroups. A prime cyclic
    group has none.
  - So `Proofs16CharacterRefinement` is not needed for ℤ/N. It stays as
    a group-agnostic formalization of Proposition 8.1's core. The
    Bohr-inside-progression step above is *not* a prerequisite here.

  The redesign question therefore reduces to two inputs:
  1. bounded-image (`log K` polynomial) alternating sums for many
     additive quadruples; the exact identities of J.98 are a special
     case;
  2. the pass from many quadruples to all of them on a dense index set.

  For (2) Milićević uses the abstract Balog–Szemerédi–Gowers theorem
  (his Theorem 4.1, Steps 2 and 6). J.108–J.110 use model packing and
  elimination instead, which is where the triple exponential enters. A
  polynomial-loss abstract BSG for "respected" quadruple families is the
  natural replacement to formalize next.

  **The abstract BSG, and what the corpus already has for it.**
  Milićević's Theorem 4.1 (printed p. 47) has the following shape.
  - **Hypotheses.** Take `X` with `|X−X| ≤ K|X|` and `A ⊆ X`, and
    quadruple families `Q_1, …, Q_36` in `A` with:
    - *largeness:* `|Q_1| ≥ c|X|^3`;
    - *symmetry:* closure under `(a₃,a₄,a₁,a₂)`, `(a₂,a₁,a₄,a₃)` and
      `(a₁,a₃,a₂,a₄)`;
    - *weak transitivity:* if `(a₁,a₂,b,b′) ∈ Q_i` and
      `(b,b′,a₃,a₄) ∈ Q_j` for at least `c′|X|` pairs, then
      `(a₁,a₂,a₃,a₄) ∈ Q_{i+j}`.
  - **Conclusion.** A subset `A′` of size `(c/2K)^O(1)|X|` in which every
    `ℓ`-tuple has `(c/2K)^O(1)|X|^(3ℓ−1)` bridging representations through
    `Q_36`, for `ℓ ≤ k`. All losses are polynomial.
  - **Application.** Proposition 6.1 takes `Q_i` to be the quadruples
    whose alternating sum has image at most `K^i` on the common domain.
    Each transitivity step multiplies the image bound and intersects the
    domains.
  - **Corpus.** The robust-connectivity input (his Lemma 4.2, many short
    paths between any two vertices of a dense set) exists here as
    `exists_dense_four_walk_set` (J.102), with polynomial bounds.
  - **Plan.** Prove Theorem 4.1 for ℤ/N from J.102. Apply it with `Q_i` =
    "alternating sum has at most `K^i` values on the radius-`ρ/2^i`
    common domain". Then `freiman_small_image_zero` turns the conclusion
    into exact zero relations at radius `ρ/K^O(1)`. The losses stay
    `exp(-poly)` provided `K` and the spectrum rank are polynomial.
    This would replace J.108–J.110.
  - **Progress (2026-10-09).**
    - `Proofs16WeakTransitivityLadder` proves the engine of Claims 4.3
      and 4.4 for any relation family `R i` on a finite vertex set `S`.
      Suppose `R` is weakly transitive against `R 1` with constant `c`:
      `c·|S|` common `z` with `R i x z ∧ R 1 z y` give `R (i+1) x y`.
      Then at least `η·|S|^m` chains of `m` intermediate `R 1`-steps, with
      `2^m·c ≤ η`, give `R (m+1) x y` (`rel_of_chainCount`). The proof
      averages over the last vertex, losing a factor `2` per step.
    - `Proofs16FourWalkLadder` combines it with J.102 into Claim 4.3,
      four-walk form (`rel_four_on_four_walk_set`). If `R 1` is
      symmetric with ordered-edge density `δ` and `c ≤ δ^5/2^17`, a set of
      `3δn/8` vertices has `R 4 u v` for all its pairs.
      `chainCount_three_eq` identifies the chain count with
      `graphFourWalks`.
    - `Proofs16AbstractBSGDifferences` does the difference-graph step
      in any abelian group.
      - `exists_popular_differences`: suppose the good pairs of pairs
        `(x+d,x),(y+d,y)` number at least `c|X|^3` in total and
        `|X−X| ≤ K|X|`. Then at least `(c/2)|X|` differences each carry
        `(c/2K)|X|^2` of them.
      - `difference_ladder_rel_four`: fix such a `d`. Assume `Q 1` has
        symmetry (S1), and `Q` is weakly transitive against `Q 1` with
        `0 < c′ ≤ δ^5/2^17`. Then a set of `3δ|X|/8` vertices `u` has
        `Q 4 (u+d) u (v+d) v` for all its pairs. That is Claim 4.3, via
        the subtype graph on `X` and `rel_four_on_four_walk_set`.
    - `Proofs16AbstractBSGUnion` builds the union graph, assuming no
      2-torsion.
      - `exists_antipodal_free_subset` picks representatives `D′` with
        `|D| ≤ 2|D′| + 1`.
      - `diffUnion D′ T` is the union graph, symmetric and inside
        `A × A`.
      - `diffUnion_same_difference` is property (20): two pairs with the
        same difference are `Q 4`-related, using (S2) for swapped pairs.
      - `diffUnion_card_ge`: the graph has at least `∑_{d∈D′} |T d|`
        edges.
    - `Proofs16AbstractBSGClaim44` proves Claim 4.4 in four-walk form
      (`claim_4_4`).
      - **Hypotheses.** A graph `P ⊆ A × A` has property (20) for `Q 4`,
        and `Q` has symmetry (S3) and weak transitivity. Any two
        vertices of `B` are joined by `η|X|^3` four-walks.
      - **Conclusion.** For `B₁, B₂ ⊆ B` of densities `ε₁, ε₂` and
        `|X−X| ≤ K|X|`, at least `(κ/2)|X|^3` additive quadruples of
        `B₁² × B₂²` lie in `Q 16`, where `κ = (ε₁ε₂η)²/K⁴` and
        `16c′ ≤ κ`.
      - **Proof.** Walk count (`walkTuples_card`); fiber Cauchy–Schwarz
        over difference sequences (`collisions_ge`); collision geometry,
        where equal differences force a common shift `e`; each
        quadruple's fiber injects into its `shiftRel`-chains; averaging;
        then the ladder at levels `4i`.
    - `Proofs16AbstractBSGPruning` proves the pruning step
      (`rich_pruning`). Take `θ < κ/2` with `κ = (ε²η)²/K⁴`. Then fewer
      than `ε|X|` elements of `B` lie in fewer than `θ|X|²` additive
      `Q 16`-quadruples (`richCount`). Otherwise Claim 4.4 on those
      poor elements gives more quadruples than they carry.
    - `Proofs16AbstractBSGCore` assembles all of this into
      `abstract_bsg_core`, stated for a finite abelian group without
      2-torsion.
      - **Hypotheses.** Symmetries (S1) for `Q 1`, (S2) for `Q 4`, (S3)
        for all levels; weak transitivity with constant `c′`; doubling
        `|X−X| ≤ K|X|`; `c|X|^3` good pairs of pairs; and `c|X| ≥ 4`.
      - **Conclusion.** Sets `B′ ⊆ B ⊆ A` with `|B′| ≥ ε|X|`, in which
        every element lies in at least `θ|X|²` additive
        `Q 16`-quadruples with the rest in `B`.
      - **Constants.** `δ = c/2K`, `δ₂ = 3cδ/64`, `η = δ₂⁵/2^14`,
        `ε = 3δ₂/16`, `κ = (ε²η)²/K⁴` (`absBsgDelta`, …,
        `absBsgKappa`), with `θ < κ/2`. All are polynomial in `c/K`.
      - `exists_dense_rich_walk_set` and `walkSet_card_eq_fourWalks`
        connect J.102's four-walk set on the subtype of `X` to
        `walkSet`.
    - Still needed for Theorem 4.1: the bridging statement
      (`|Z_ℓ(a)| ≥ (c/2K)^O(1)|X|^(3ℓ−1)`).
    - **Correction to the plan above (same day).** Theorem 4.1 does not
      conclude that *all* additive quadruples of `A′` are respected. It
      gives many bridging representations for every tuple of `A′`.
      - Proposition 6.1 turns that into image bounds for all but an `ε`
        fraction of the 16-tuples.
      - "All" is reached only after robust Bogolyubov–Ruzsa onto a
        progression (Step 3) and Steps 4–6, where Step 6 is a second
        abstract BSG.
      - So replacing J.108–J.110 needs that chain, not Theorem 4.1 plus
        `freiman_small_image_zero` alone. The layers above formalize the
        engine those steps share.
- *Small additive rank.* Otherwise, a model family spanned by `R` basic
  maps might be eliminated with one test per generator, at column cost
  `β^O(R)`. That is `exp(-poly)` when `R` and the spectrum rank are
  polynomial.

None of these is established. They are recorded as the most direct leads.

This is the audit the J.5 revisited estimate called for. It does not
change any proved statement; it shows that the order-of-magnitude
`Bnd(c) ≤ A·c^(-p)` there is not what the current parameters deliver.

### J.103. Exact additive richness from matched four-walks

**Verified 2026-10-09.** Seven modules carry J.102's walk counts through
the endpoint identity and counting arguments. The conclusion is uniform
additive richness in every pair of subsets of one dense column set.

`Proofs16FourStepIdentity` first proves the crossing symmetry for plain
column-pair identities. `ColumnPairIdentity.four_step_shrink` then
composes four identities through three intermediate pairs. The endpoint
defect vanishes on the union of all ten column Bohr domains by
telescoping. Its own domain uses only the four endpoint spectra;
`freiman_zero_remove_frequencies` removes the six intermediate spectra
in one step. For rank `d`, initial radius `rho`, and identity radius
`0 < r <= rho`, the cost is

```
N > refinementKernelCap (4*d) (6*d) rho r,
rnew = refinementKernelRadius (4*d) (6*d) rho r.
```

`Proofs16FourWalkDifferences` records the four consecutive differences
of a walk. Equality of these sequences is equivalent to translation of
all corresponding vertices. In particular, a start and a difference
sequence determine the complete walk. `Proofs16MatchedFourWalkIdentity`
uses edge coherence, crossing, and the four-step composition to prove
that matched walks give an endpoint pair relation at `rnew`. Repeated
vertices cause no problem for this algebraic argument.

`Proofs16FourWalkCollisionCount` counts the walks from `U` to `V` and
applies the existing weighted Cauchy--Schwarz theorem to their difference
sequences. There are `N^4` possible sequences. If the walk family has
size at least `mu*N^5`, it has at least `mu^2*N^6` ordered matching pairs.
`Proofs16FourWalkProjection` projects these pairs to their endpoint
quadruples. The endpoints and the first walk's internal triple determine
the second walk, so each fibre has size at most `N^3`. Consequently,
there are at least `mu^2*N^3` distinct endpoint quadruples.

`Proofs16WalkAdditiveRichness` defines `mixedExactColumnQuadruples U V`:
these are exact additive quadruples `q` with `q0,q2` in `U` and `q1,q3`
in `V`. If `|U| >= beta1*N`, `|V| >= beta2*N`, and every endpoint pair
has at least `eta*N^3` four-walks, it proves

```
# mixedExactColumnQuadruples(U,V,rnew)
  >= (beta1*beta2*eta)^2 * N^3.
```

The radius and modulus costs do not depend on `beta1` or `beta2`.

`Proofs16GlobalColumnRichness` assembles this directly from the original
dense bihomomorphism. Put

```
d = columnSpectrumCap (columnEightDensity alpha)
rho = globalColumnIdentityRadius alpha
r = columnIdentityRadius d rho 1
delta = globalColumnQuadrupleDensity alpha / 4
eta = globalColumnWalkDensity alpha = delta^5 / 16384
Nrich = max(globalColumnGraphModulusBound alpha,
            refinementKernelCap (4*d) (6*d) rho r + 1).
```

For prime `N >= Nrich`, `global_column_additive_richness` constructs
`X,T,L,W,B`, retaining the original witness system, column rank,
normalization, and Freiman linearity. It proves `B subset X`,
`|B| >= 3*delta*N/8`, positive `eta` and `rnew`, and the displayed mixed
quadruple bound for every `U,V subset B` and every nonnegative pair of
lower density bounds. No graph, walk, or relation hypotheses remain in
this global theorem.

**Limits and next step.** This is hereditary abundance of exact additive
quadruples, not exactness of every additive quadruple on `B`. The next
selection step must retain vertices participating in many exact
quadruples, then build the compatible representations needed for the
structured family. Bilinear organization, shifted agreement, and the
final numerical structure budget remain open. The numbered companion
count does not change.

**Verification.** The global construction checks 213 modules. All 14 new
named theorems pass individual axiom checks using only `propext`,
`Classical.choice`, and `Quot.sound`. No additional upstream modules or
Apache provenance changes were needed.

After merging the retirement of the redundant six-walk module, the
combined audit checks 7,058 public Gowers theorems in 5,116 modules
(5,114 for the facade, including 4,152 OAI modules). Only the three
approved standard axioms occur. The source ledger remains identical
at 115 companions and five open entries; selected-port scope passes.
Companion counts do not certify fidelity to every printed statement.

### J.104. Dense popular columns and exact triple representations

**Verified 2026-10-09.** Four modules select a dense core of columns with
many representations, while preserving the ambient hereditary richness
needed to connect those representations in later steps.

`Proofs16ColumnAnchorCounts` defines `exactColumnAnchor B T L r a` as
the exact quadruples in `B` whose first coordinate is `a`. It proves
monotonicity under restriction of the vertex set, identifies the mixed
quadruples for `(C,C)` with all exact quadruples in `C`, and bounds their
count by the sum of ambient anchor degrees over `C`.

The density-form richness statement also gives the denominator-free
inequality

```
eta^2 * |C|^4 <= N * #exactColumnQuadruples(C)
```

for every `C subset B`, by applying it at the actual density `|C|/N`.

`Proofs16PopularColumnAnchors.popular_column_anchors_dense` assumes
`|B| >= b*N`, with `b,eta > 0`, and sets

```
lambda = eta^2*b^3/16,
P = {a in B : #exactColumnAnchor(B,a) >= lambda*N^2}.
```

It proves `|P| >= b*N/2`. Indeed, if the discarded set `C` had size at
least `b*N/2`, its anchor upper bound and the hereditary lower bound
would give `eta^2*|C|^3 <= lambda*N^3`, contradicting the choice of
`lambda`. This uses the actual discarded-set cardinality and gives a
cubic dependence on `b`; bounding its cardinality merely by `N` would
give the weaker quartic threshold considered previously.

`Proofs16ColumnTripleRepresentations` reindexes anchor quadruples as
triples. A triple `(x,y,z)` corresponds to the quadruple `(a,y,x,z)`,
so its exactness gives

```
a = x-y+z,
L(a)(t) = L(x)(t)-L(y)(t)+L(z)(t)
```

on the intersection of the four relevant column Bohr sets. All four
indices lie in `B`. The reindexing is a bijection, so the triple count
is exactly the anchor degree; the same `lambda*N^2` lower bound holds.

`Proofs16GlobalColumnAnchors.global_popular_column_representations`
assembles this from the original dense bihomomorphism, at the unchanged
threshold `globalColumnRichnessModulusBound alpha`. Its parameters are

```
b = globalColumnVertexDensity alpha
  = 3*(globalColumnQuadrupleDensity alpha/4)/8,
eta = globalColumnWalkDensity alpha,
lambda = globalColumnAnchorDensity alpha = eta^2*b^3/16.
```

The theorem constructs `X,T,L,W,B,P`, with `P subset B subset X`,
`|B| >= b*N`, `|P| >= b*N/2`, and at least `lambda*N^2` exact triples
for every `a in P`. It retains the original witness system, column rank,
local Freiman linearity, normalization, positive radius and density
parameters, and the full mixed-quadruple richness statement for subsets
of `B`. No new radius loss or modulus threshold occurs in this selection.

**Remaining work.** The triple representations form the base case for
compatible representations of several columns. They have not yet been
glued recursively, and their abundance does not imply that every
additive quadruple on `P` has the exact identity. Bilinear organization,
shifted agreement, and the final numerical structure budget remain open.

**Verification.** The global construction checks 217 modules. All ten
new named theorems pass individual axiom checks using only `propext`,
`Classical.choice`, and `Quot.sound`. No additional upstream modules or
Apache provenance changes were needed.

The combined audit checks 7,084 public Gowers theorems in 5,120 modules
(5,118 for the facade, including 4,152 OAI modules), with the same three
approved axioms. The source ledger is identical at 115 companions and
five open entries, and the selected-port scope check passes. These
counts do not certify fidelity to every printed statement.

### J.105. Joining two popular column representations

**Verified 2026-10-09.** Six modules give compatible six-entry
representations for every pair of columns in the dense core from J.104.

`Proofs16PopularEndpointFibres` proves a generic averaging lemma: a
family of mass at least `mu*M*K`, with `M` possible endpoints and every
endpoint fibre of size at most `K`, has at least `mu*M/2` endpoints
whose fibres have size at least `mu*K/2`. A positive popular fibre
belongs to the image of the family.

`Proofs16TripleEndpointFibres` obtains the sharp elementary cap `N`
for both endpoint fibres of a fixed-column triple family. Once either
endpoint and the middle coordinate are fixed, the equation `a=x-y+z`
determines the other endpoint. Thus a triple family of size at least
`lambda*N^2` has at least `lambda*N/2` popular first endpoints and the
same number of popular last endpoints, each with at least `lambda*N/2`
representations. Both popular endpoint sets lie in `B`.

`Proofs16FibreGluingCount` counts the choices from two specified fibres
above each connecting quadruple. The total is exactly the sum of the
products of the two fibre cardinalities; uniform lower bounds therefore
multiply without a further selection loss.

`Proofs16ColumnPairSplice` uses the following orientation. Let a triple
`y` represent `a`, and a triple `z` represent `b`. For an exact quadruple
`q`, require `y3=q2` and `z1=q1`. Its identity `q0+q1=q2+q3` says that
replacing `(y3,z1)` by `(q0,q3)` translates both coordinates by the same
amount. The output is

```
s = (y1,y2,q0,q3,z2,z3).
```

It satisfies `a-b = s0-s1+s2-s3+s4-s5`. The two old middle entries are
recoverable as `a-s0+s1` and `b+s4-s5`. The output and the two anchors
therefore recover both original triples and `q`, proving injectivity of
the gluing map.

`columnPairRepresentations` records the two recovered triple identities
and the connecting exact quadruple. Its specification includes all six
output vertices lying in `B` and the corresponding alternating map
identity on the Bohr domains of the anchors, the six output vertices,
and the two recovered middle entries. Those intermediate domain
conditions are retained explicitly; they have not been discarded here.

`Proofs16ColumnPairGluing.column_pair_representations_count` takes
popular last endpoints for `a` and popular first endpoints for `b`.
Hereditary richness supplies at least `eta^2*lambda^4*N^3/16` connecting
quadruples, and each has at least `(lambda*N/2)^2` choices of triples.
Injectivity then proves

```
# columnPairRepresentations(B,T,L,r,a,b)
  >= eta^2*lambda^6*N^5/64.
```

`Proofs16GlobalColumnPairRepresentations` assembles this for every
`a,b` in the same dense core `P`, directly from the original dense
bihomomorphism. It defines

```
globalColumnPairDensity alpha
  = (globalColumnWalkDensity alpha)^2
    * (globalColumnAnchorDensity alpha)^6 / 64
```

and proves its positivity along with the uniform pair-representation
count. Original witnesses, column rank, normalization, local linearity,
single-column triples, and the full ambient hereditary richness remain
in the conclusion. The size threshold and radius are unchanged.

**Remaining work.** This is the two-column case of compatible tuple
representations. The arbitrary-length induction, its density recurrence,
and the subsequent bilinear organization and shifted agreement are still
open. No final Gowers numerical bound is claimed from this step alone.

**Verification.** The focused global construction checks 223 modules.
All 13 new named theorems pass individual axiom checks with only
`propext`, `Classical.choice`, and `Quot.sound`. No additional upstream
modules or Apache provenance changes were needed.

The combined audit checks 7,104 public Gowers theorems in 5,126 modules
(5,124 for the facade, including 4,152 OAI modules), with the same three
approved axioms. The source ledger is identical at 115 companions and
five open entries, and the selected-port scope check passes. These
counts do not certify fidelity to every printed statement.

### J.106. Compatible representations of arbitrary anchor lists

**Verified 2026-10-09.** The two-column construction now extends to every
nonempty finite list of anchors. Seven modules formalize the word type,
injective splice, recursive compatibility predicate, counting induction,
closed density formula, and construction from the original bihomomorphism.

`ColumnWord N k` is a recursively nested word of `k` triples, with exactly
`3*k` entries and `N^(3*k)` possibilities. `columnWordEval f` evaluates the
alternating sum of the entries after applying `f`: a triple contributes
`f x-f y+f z`, followed by subtraction of the remaining word's value.
`columnAnchorEval f` is the corresponding alternating sum of an anchor
list. Repeated anchors and repeated word entries are allowed.

`Proofs16ColumnWords.columnWord_first_fibre_card_le` proves that a
fixed-value family of words with `k+1` triples has first-endpoint fibres
of size at most `N^(3*k+1)`. Fixing the first entry and all entries except
the middle entry of the first triple determines that middle entry.
Projection onto the last entry of the first triple and the remaining
`k` triples is therefore injective on the fibre. Averaging then gives
at least `delta*N/2` popular first endpoints, each with at least
`delta*N^(3*k+1)/2` representations, whenever the full family has at least
`delta*N^(3*k+2)` words.

`Proofs16ColumnWordSplice` prepends a triple representing `a` to a
nonempty word representing `b`. If the exact connecting quadruple is
`q`, the old triple's last entry is `q2` and the old word's first entry
is `q1`. Replace them by `q0` and `q3`. The resulting word represents
`a-b`. The output and the two represented values recover both replaced
entries: the old triple's last entry is `a-y1+y2`; the old word's first
entry is `b+z2-z3+value(tail)`. This gives a left inverse and proves
injectivity of the splice at every length.

`columnWordRepresentations B T L r as` records the recovered triple,
recovered shorter word, and exact connecting quadruple recursively.
`columnWordRepresentations_spec` proves that every output entry lies in
`B`, that its value is `columnAnchorEval id as`, and that its map value
is `columnAnchorEval (fun x => L x y) as` on the recursively specified
`columnWordDomain`. That domain explicitly retains all recovered
intermediate column conditions. The map identity is not yet asserted
on only the anchor and output Bohr domains.

`column_word_representations_step` keeps the two input densities separate.
For a triple family of density `lambda` and a shorter word family of
density `delta`, the two popular endpoint sets have densities at least
`lambda/2` and `delta/2`. Hereditary richness supplies at least
`eta^2*lambda^2*delta^2*N^3/16` connecting quadruples. Multiplying by the
two fibre bounds and using splice injectivity gives

```
# representations(a :: b :: as)
  >= (eta^2*lambda^3*delta^3/64) * N^(3*as.length+5).
```

There is no need to replace the input densities by their minimum. The
verified uniform density for `k+1` triples is therefore the recurrence

```
delta_0 = lambda,
delta_(k+1) = eta^2*lambda^3*delta_k^3/64.
```

`column_word_representations_count` proves this bound for every nonempty
list in a core whose anchors have at least `lambda*N^2` triple
representations. `columnWordDensity_formula` and
`columnWordDensity_loss_exponent` give the explicit solution

```
delta_k = (eta^2*lambda^3/64)^((3^k-1)/2) * lambda^(3^k).
```

The exponents here are natural numbers; `(3^k-1)/2` is exactly the
geometric sum `sum_{i<k} 3^i`. Positivity is proved for every `k` when
`lambda` and `eta` are positive.

`global_column_word_representations` constructs the same dense core
`P` directly from the original dense bihomomorphism and proves all
these counts with `lambda = globalColumnAnchorDensity alpha` and
`eta = globalColumnWalkDensity alpha`. The original column witnesses,
rank bounds, normalization, local linearity, triple counts, and full
ambient hereditary richness remain in its conclusion. No additional
modulus threshold or radius loss is introduced for these representation
counts.

**Remaining work.** The arbitrary-length counting induction is complete.
The recursively retained intermediate domains still need to be removed
with an explicit frequency/radius budget before using an identity on
only the output and anchor domains. Subsequent bilinear organization,
shifted agreement, and the final Gowers numerical structure budget
remain open. The explicit density formula is an intermediate estimate,
not a proof of the remaining numbered structure statements.

**Verification.** The global construction checks 226 modules, and the
closed-form module checks 225. All 14 new named theorems pass individual
axiom checks using only `propext`, `Classical.choice`, and `Quot.sound`.
No additional upstream modules or Apache provenance changes were needed.

The combined audit checks 7,139 public Gowers theorems in 5,133 modules
(5,131 for the facade, including 4,152 OAI modules), with the same three
approved axioms. The source ledger is identical at 115 companions and
five open entries, and the selected-port scope check passes. These
counts do not certify fidelity to every printed statement.

### J.107. Removing all intermediate domains from word identities

**Verified 2026-10-09.** Five modules turn J.106's recursive local map
identities into identities on only the anchor and output Bohr domains,
with explicit parameters for every fixed word length.

`Proofs16ColumnWordDomains` flattens a word into `columnWordEntries`
and proves that its length is `3*k` for a word of `k` triples. Its
alternating list evaluation is exactly `columnWordEval`. The same
module defines `columnWordAux`: at each splice it records only the old
triple's last entry and the old word's first entry, followed by the
auxiliary entries of the recovered shorter word. A representation of
`a :: as` therefore has exactly `2*as.length` auxiliary entries. This is
smaller than counting every vertex of every recursive triple and
connecting quadruple separately.

All auxiliary entries of a valid representation lie in `B`.
`columnWordDomain_of_entries_aux` proves that the anchor, output, and
auxiliary constraints imply the full recursive `columnWordDomain`.
The proof observes that the connecting quadruple's other two entries
are output entries, while its two old entries are precisely the two
new auxiliary entries. No further intermediate constraints are needed.

`Proofs16ColumnListSpectrum` forms the union of the column spectra for
a finite list. If every spectrum has cardinality at most `d`, the union
has cardinality at most `length*d`. Membership in its Bohr set is
exactly membership in every listed column's Bohr set. Alternating list
evaluations preserve Freiman linearity and normalization. In particular,
the difference between the anchor map sum and output map sum is
Freiman-linear on the union of the anchor and output spectra.

`column_word_identity_remove_aux` applies the prime-target
frequency-removal theorem to this difference. Write `k = as.length`,
so the represented anchor list has `k+1` terms. The two rank bounds are

```
D = 4*(k+1)*d,    E = 2*k*d.
```

The first counts the anchors and the `3*(k+1)` output entries. The
second counts the auxiliary entries. Given `0 < r <= rho`, set

```
K = ceil(4/rho)^D * ceil(1/r)^(D+E),
s = (rho/2)/K.
```

If the prime modulus satisfies `N > K`, the output map sum equals the
anchor map sum whenever the argument belongs to the Bohr sets of the
anchors and output entries at radius `s`. No auxiliary spectrum appears
in this conclusion. The proof first obtains zero on the intersection
with the auxiliary constraints at radius `r`, then uses
`freiman_zero_remove_frequencies` once. The counts of representations
are unaffected.

`ColumnWordIdentity` packages exactly this conclusion, without recovered
intermediate domain assumptions. The auxiliary rank bound is `2*k*d`,
rather than the preliminary `8*(k+1)*d` estimate from counting every
recursive domain column.

`Proofs16ColumnWordIdentityParameters` specializes these parameters to
J.106's global construction. It defines

```
globalColumnWordIdentityRadius alpha k
  = refinementKernelRadius (4*(k+1)*d) (2*k*d) rho r,
globalColumnWordIdentityModulusBound alpha k
  = max(globalColumnRichnessModulusBound alpha,
        refinementKernelCap (4*(k+1)*d) (2*k*d) rho r + 1),
```

where `d = columnSpectrumCap (columnEightDensity alpha)`,
`rho = globalColumnIdentityRadius alpha`, and
`r = globalColumnRichnessRadius alpha`. Positivity of the new radius and
the required comparison `r <= rho` are proved.

`global_column_word_identities` constructs the dense core directly from
the original dense bihomomorphism under this explicit modulus bound.
It retains the witness system, spectrum rank, normalization, local
linearity, core density, all triple and arbitrary-length representation
counts, and full hereditary richness. Every represented word whose
anchor list has `k+1` terms satisfies `ColumnWordIdentity` at the radius
above. This finishes removal of the intermediate domains for any fixed
length, with the stated length-dependent size and radius costs.

**Remaining work.** The core does not yet satisfy all additive map
identities, and no global bilinear organization or shifted agreement is
claimed. These structural steps and the final numerical structure budget
remain open. The earlier radius `r` is not claimed sufficient after
removing auxiliary conditions; the new radius and threshold are part of
the theorem.

**Verification.** The global construction checks 231 modules. All 17 new
named theorems pass individual axiom checks using only `propext`,
`Classical.choice`, and `Quot.sound`. The combined audit checks 7,173
public Gowers theorems in 5,138 modules (5,136 for the facade, including
4,152 OAI modules). The source ledger is identical at 115 companions and
five open entries, and the selected-port scope check passes. These
counts do not certify fidelity to every printed statement. No upstream
modules or Apache provenance changed.

### J.108. Bounded local models on a common Bohr domain

**Verified 2026-10-09.** Seven modules use J.107's word identities to
construct a bounded family of normalized Freiman-linear models in every
fixed alternating-value fibre of the dense core.

`dense_family_packing` is a finite packing lemma. Suppose the families
`F i` lie in a common finite universe of size at most `M`, each has
size at least `delta*M`, and `delta,M > 0`. A subfamily of maximum
cardinality among the pairwise disjoint subfamilies has an index set
`J` with `|J|*delta <= 1`. Every original family intersects a selected
family: otherwise it could be added to the packing. The proof counts
the disjoint union directly. It requires no probability estimate or
rounding loss.

`columnWordValueFibre_card_le` proves that words of `k+1` triples with
one fixed alternating value occupy at most `N^(3*k+2)` possibilities.
Forget the first entry. The remaining two entries of the first triple
and the tail determine that entry from the prescribed value, so this
projection is injective. Thus the representation density in J.106 is a
density within a single value fibre, with no extra factor of `N` lost
when packing families.

`ColumnListIdentity` compares the alternating map sums of two finite
anchor lists on their own Bohr domains. A `ColumnWordIdentity` gives
such a comparison with the flattened word. If two anchor families
share a represented word, their map sums therefore agree after adding
that word's domain constraints. `columnListIdentity_trans_shrink`
removes the shared word spectra in one application of
`freiman_zero_remove_frequencies`. For two anchor lists of `k+1` terms,
the endpoint and auxiliary rank bounds are respectively

```
D = 2*(k+1)*d,    E = 3*(k+1)*d.
```

The comparison holds at `refinementKernelRadius D E rho r` when
`N > refinementKernelCap D E rho r`, with no shared-word spectrum
remaining in the conclusion.

`column_model_packing` combines these facts. Families of density
`delta` in one fixed-value fibre yield at most `1/delta` representative
anchor lists, and each original anchor list has a local map identity
with one representative. In particular, a nonempty fibre always has a
selected model; empty fibres are allowed and require no model.

`Proofs16FixedColumnWordFamilies` supplies a common finite word type
for the application. A `ColumnAnchorTuple N k` is a first anchor and a
`Fin k` tuple of remaining anchors. Its associated list has length
`k+1`. A length equivalence transports the list's representation family
into `ColumnWord N (k+1)`. The equivalence preserves cardinalities,
entries, alternating values, and all proved map identities. This makes
the packing argument apply to actual representation families without
adding a new representation hypothesis.

`columnModelSpectrum` is the union of the selected models' anchor
spectra. If each anchor list has length at most `m`, it has rank at most
`|J|*m*d`. All selected alternating map sums are normalized and
Freiman-linear on this common Bohr domain at the original linearity
radius. Membership in the common Bohr set supplies every selected
model's own column constraints.

`global_column_models` applies the construction directly to the
original dense bihomomorphism. It keeps the original witnesses, local
linearity and rank bounds, normalization, dense core, and fixed-length
representation counts. For every value `c`, it constructs a set `J` of
anchor tuples in the `c` fibre and a common spectrum `Gamma` with

```
|J|*delta <= 1,
|Gamma| <= |J|*(k+1)*d,
|Gamma|*delta <= (k+1)*d,
```

where `delta = globalColumnWordDensity alpha k`. Each tuple in the
fibre agrees with a selected normalized Freiman-linear model on the
intersection of its own column domains and the common Bohr domain.
The identity comparing the two anchor lists is retained as well.

The new radius and modulus bound are explicit:

```
s = refinementKernelRadius (2*(k+1)*d) (3*(k+1)*d)
      (globalColumnIdentityRadius alpha)
      (globalColumnWordIdentityRadius alpha k),
N0 = max(globalColumnWordIdentityModulusBound alpha k,
         corresponding refinementKernelCap + 1).
```

Both the dense core and these parameters are uniform in `c`. Setting
`c = 0` gives a bounded family of local models for additive anchor
relations.

**Remaining work.** The selected models need not be zero. A further
core-refinement argument must eliminate nonzero additive models before
claiming all additive map identities on the core. Bilinear organization,
shifted agreement, and the final numerical budget are still open.
Neither the packing bound nor a common domain alone proves these steps.

**Verification.** The focused global construction checks 238 modules.
All 15 new named theorems pass individual axiom checks using only
`propext`, `Classical.choice`, and `Quot.sound`. No upstream modules or
Apache provenance changed. The incoming named recurrence constants and
arbitrary-bound slice interfaces are included in the combined audit
recorded below; their deep structure inputs remain hypotheses.

The merged combined audit checks 7,223 public Gowers theorems in 5,148
modules (5,146 for the facade, including 4,152 OAI modules), with the
same three approved axioms. The source ledger remains identical at 115
companions and five open entries, and the selected-port scope check
passes. These counts do not certify fidelity to every printed statement.

### J.109. Quantitative elimination of active additive models

**Verified 2026-10-09.** Eight modules prove a refinement argument for
local model families. The evaluation tests include the individual column
Bohr conditions, so no evaluation outside a column's domain is used.

`freiman_nonzero_card_half` starts with a normalized Freiman-linear map
`f` on `B(T;r)` and a point `z` in `B(T;r/2)` with `f(z) != 0`. For each
`x` in the half-radius domain, at least one of `f(x)` and `f(x+z)` is
nonzero. Both points belong to the full domain. Covering the half-domain
by the nonzero set and one translate of it proves

```
|B(T;r/2)| <= 2 * |{y in B(T;r) : f(y) != 0}|.
```

Now let `Gamma` have rank at most `g`, an extra spectrum `U` have rank
at most `d`, and `f` be normalized and Freiman-linear on `B(Gamma;rho)`.
Suppose `0 < r <= rho`, the prime modulus exceeds
`refinementKernelCap g d rho (r/2)`, and `f` is nonzero somewhere on
`B(Gamma; refinementKernelRadius g d rho (r/2))`. The contrapositive of
frequency removal gives a nonzero point even on
`B(Gamma union U;r/2)`. The translation bound and the Bohr lower bound
then give, with `Q = ceil(1/(r/2))`,

```
N <= 2*Q^(g+d) * |{y in B(Gamma union U;r) : f(y) != 0}|.
```

`localSeparatingTests` records pairs `(y,gamma)` with `y` in the
specified domain and `N < 5*centeredAbs(gamma*f(y))`. For prime `N >= 7`,
at least half of the characters separate each nonzero value. Thus the
number of separating tests in the constrained domain is at least
`beta*N^2`, where

```
beta = modelTestDensity g d r = 1/(4*Q^(g+d)).
```

Both `0 < beta` and `beta <= 1/4` are proved. The estimate is uniform in
the extra spectrum `U` and hence applies to every individual column
spectrum of rank at most `d`.

`dual_test_selection` double-counts pairs of columns and models against
tests. If each column-model pair has at least a `beta` fraction of valid
detecting tests, some test simultaneously retains at least `beta` of
the columns and detects at least `beta` of the models. The proof averages
the product of the two counts, then bounds each count by the full size
of its respective set. `exists_model_test` applies this with
`U = T x`; its chosen evaluation belongs to the common domain and to
every retained column's domain.

`exists_model_test_cell` partitions those retained columns by the ten
Dirichlet cells of `gamma*L x y`. It keeps at least `beta/10` of the
original columns. Four values from one cell cannot have an alternating
sum separated by `gamma`: pair the first two and last two entries and
use the two strict cell-difference bounds. Therefore no detected model
can equal a four-term map value from the retained core.

`ColumnQuadModelAlternatives` records the invariant for iteration. Every
additive quadruple either has zero map defect at a target radius `s`,
or agrees with one of the active models at the testing radius `r`.
These two radii are kept distinct. The refinement step retains at least
`beta/10` of the column mass and at most `1-beta` of the active model
count, and preserves this invariant. A detected model is excluded by
evaluating the asserted model relation at the selected valid test.

`column_model_elimination_iterate` proves that after `t` rounds the core
has at least `(beta/10)^t*|A|` columns and at most `(1-beta)^t*|I|` active
models remain. An empty active set requires no further refinement.
`modelEliminationRounds_kills` proves that

```
t = ceil(log(|I|+1)/beta)
```

makes the survivor bound strictly smaller than one, using
`1-beta <= exp(-beta)`. The count is an integer, so all active models are
gone. `column_model_elimination_zero_core` produces a nonempty subcore
of the stated density on which every additive quadruple has zero map
defect on its target common and individual Bohr domains.

**Remaining work.** The elimination theorem takes the model alternatives
and nonvanishing of the active models as explicit inputs. The global
construction from J.108 still needs to be instantiated at four anchors,
with active models separated from those already zero on the smaller
common domain. Its modulus threshold and retained density must then be
made uniform in the original density. Subsequent bilinear organization,
shifted agreement, and the printed numerical budget remain open. The
logarithmic dependence on the number of models does not by itself bound
the dependence on `beta`, whose exponent includes the common rank.

**Verification.** The focused elimination theorem checks 55 modules.
All 16 new named theorems pass individual axiom checks using only
`propext`, `Classical.choice`, and `Quot.sound`. No additional upstream
modules or Apache provenance changes were needed.

The combined audit checks 7,253 public Gowers theorems in 5,156 modules
(5,154 for the facade, including 4,152 OAI modules), with the same three
approved axioms. The source ledger is identical at 115 companions and
five open entries, and the selected-port scope check passes. These
counts do not certify fidelity to every printed statement.


### J.110. Global zero-relation core and a column-domain bihomomorphism

The model-elimination inputs in J.109 are now discharged from the original
bihomomorphism. The four-anchor model construction in J.108 is instantiated
at alternating value zero. Write

```
d = columnSpectrumCap (columnEightDensity alpha)
delta = globalColumnWordDensity alpha 3
g = ceil(4*d/delta)
M = ceil(1/delta)
rho = globalColumnIdentityRadius alpha
r = globalColumnModelRadius alpha 3
u = refinementKernelRadius g d rho (r/2)
s = min r u
beta = modelTestDensity g d r
t = ceil(log(M+1)/beta)
c = (beta/10)^t * globalColumnVertexDensity alpha / 2
```

`columnQuadAnchor` encodes an additive quadruple as the list
`[q 0,q 1,q 2,q 3]`. Its alternating map value is exactly
`columnQuadValue L q y`. `column_models_initialize` keeps only those models
which are nonzero somewhere on `bohr Gamma u`. Every discarded model is
zero there, and hence gives a zero relation at radius `s`. Every active
model still supplies the comparison at testing radius `r` required for
elimination. This uses both parts of `s = min r u`.

`modelEliminationRounds_mono` and `column_model_cover_zero_core` replace
the actual active model count by the uniform cap `M`. The power comparison
has the correct direction because `0 < beta/10 <= 1`.
`global_zero_column_core` constructs a nonempty core of at least `c*N`
columns, a common spectrum of rank at most `g`, and zero alternating map
values for every additive quadruple on the common and individual radius-`s`
Bohr neighborhoods. The modulus threshold is the maximum of the previous
four-anchor threshold, `refinementKernelCap g d rho (r/2)+1`, and `7`.
All parameters depend only on `alpha`; positivity of the final radius and
core density is proved.

`zero_columns_bihomomorphism` enlarges each column spectrum from `T x` to
`Gamma union T x`. Horizontal Freiman identities follow by reordering
`[a,b,c,d]` to `[a,c,b,d]` in the alternating relation. Vertical identities
follow from the original column linearity and `s <= rho`.
`global_column_core_bihomomorphism` applies this to the constructed core,
with each enlarged spectrum having rank at most `g+d`.
`columnBohrDomain_card` expresses the full domain cardinality as the sum
of its column cardinalities. Applying the Bohr lower bound column by
column gives the additional global guarantee

```
c*N^2 <= ceil(1/s)^(g+d) * |columnBohrDomain P (Gamma union T) s|.
```

Thus the constructed two-dimensional domain has a positive density
bound depending only on `alpha`, as well as a dense set of columns.

The global statements from coherent pairs onward now retain the original
witness lower bound

```
columnWitnessDensity (columnEightDensity alpha) * N^4 <= |W x|
```

for every original column `x` in `X`. This bound was already proved at
the global relation stage but had been dropped by subsequent interfaces.
Carrying it through is necessary for a later quantitative agreement
argument with the original map. The original witness system remains on
the original spectra at radius `1/(4*pi)`; this does not assert that its
witness sums lie in the smaller final domain.

**Remaining work.** A column-domain bihomomorphism is now constructed.
Bilinear organization of its varying spectra, quantitative shifted
agreement with the original map, and the final numerical budget remain
open. In particular, the witness count alone does not prove agreement
on the smaller final domain. The common rank enters the exponent defining
`beta`; no polynomial dependence on `1/alpha` or fit to the printed
Gowers bound is asserted. The five numbered open statements and prior
source-fidelity caveats remain unchanged.


**Verification.** The strengthened witness chain and its pair-representation
consumer pass a 255-module focused build. The final dense-domain construction
passes a 253-module build. All 16 new named theorems pass individual axiom
checks. The combined audit checks 7,282 public Gowers theorems in 5,162
modules (5,160 for the facade, including 4,152 OAI modules), using only
`propext`, `Classical.choice`, and `Quot.sound`. The numbered ledger is
identical at 115 companions and five open entries; the selected-port scope
check passes. There are no new upstream ports or provenance changes.


### J.111. Quantitative shifted agreement on the smaller column domain

The agreement obligation left in J.110 is now proved for the constructed
column domains. The original map is recovered after a common vertical
shift and addition of its values on the selected source row. No separate
witness-selection or agreement hypothesis remains in the global theorem.

**Witness comparison.** `witness_agreement_slice` groups four-coordinate
witnesses by their last three coordinates and the Dirichlet-cell signature
of the first coordinate against the final spectrum `S`. With `Q` cells
per frequency there are `N^3 * Q^|S|` labels. A largest label class projects
injectively to a source slice `D`, giving

```
|W| <= N^3 * Q^|S| * |D|.
```

For `a,b` in that slice, cell closeness and `1 <= s*Q` imply
`a-b in bohr S s`. If the original witness sums lie in `bohr T rho`,
the final difference domain lies in it as well, and `L` is normalized
Freiman-linear there, then

```
L(a-b) = f(a)-f(b).
```

Indeed, the two represented sums differ by `a-b`; apply Freiman linearity
to the first sum plus zero and the second sum plus this difference. The
three frozen source values cancel. `witness_agreement_slice_density`
converts witness density `w`, spectral rank at most `R`, and the above
count into `|D| >= (w/Q^R)*N`.

The global chain now preserves linearity at the original radius
`1/(4*pi)`, in addition to the smaller-radius identities. The original
property was already available in `global_many_exact_column_quadruples`
but had been dropped in `global_dense_column_relations`. It is retained
through every subsequent global stage. This is necessary because the
witness sums themselves need not lie in the final smaller domain.

**A single shift.** `exists_common_slice_shift` starts with at least
`delta*N` columns, each with a source slice of at least `lambda*N` points.
There are at least `delta*lambda^2*N^3` ordered pairs in these slices.
Averaging their second coordinates yields one common centre `t` and at
least `delta*lambda^2*N^2` pairs `(x,a)` with both `a,t in D x`.
Translate each such pair to `(x,a-t)`, preserving cardinality.

Restrict the column set to those with `(x,t) in A` and define

```
Phi(x,y) = L(x,y) + phi(x,t).
```

`column_bihomomorphism_add_row` proves that `Phi` is still a Freiman
bihomomorphism: the horizontal offset identity is the original map's
identity along row `t`, and the vertical offsets cancel.
`column_slices_shifted_agreement` then proves actual membership and values
on the translated agreement set:

```
(x,y+t) in A,    Phi(x,y) = phi(x,y+t).
```

The generic theorem keeps the agreement radius and the bihomomorphism
radius separate.

**Global parameters.** Let `s`, `c`, `g`, and `d` be the zero-core
parameters in J.110, and set

```
w = columnWitnessDensity (columnEightDensity alpha)
Q = ceil(2/s)
R = g+d
lambda = w/Q^R
agreementDensity = c*lambda^2.
```

Positivity of both new density parameters is proved.
`global_column_shifted_agreement` starts from the original dense
bihomomorphism and the same modulus threshold as J.110. It constructs a
column set `V`, spectra of rank at most `R`, a common shift `t`, and an
agreement set of cardinality at least `agreementDensity*N^2` inside the
column domain at radius `s/2`. The adjusted map `Phi` is a Freiman
bihomomorphism on the full radius-`s` column domain. This half-radius
margin is explicit and does not require asserting that the original
witness sums lie there.

**Remaining work.** The frequency sets still vary arbitrarily with the
column. Organizing them into the bilinear Bohr geometry required by the
variety theorem, while retaining quantitative agreement, remains open.
The final numerical budget also remains open. The new result does not
prove `MilicevicDeepVarietyStructure` or close any of the five remaining
numbered statements. The density loss here uses one frequency cell per
column; summing pair counts across all cells could improve this local
loss, but that refinement is not asserted as proved.


**Verification.** The original-radius interface update passes a focused
256-module build including the pair-representation consumer. The global
agreement theorem passes a 257-module build, and all eight new named
theorems pass individual axiom checks. The full audit checks 7,291 public
Gowers theorems in 5,166 modules (5,164 for the facade, including 4,152 OAI
modules), using only `propext`, `Classical.choice`, and `Quot.sound`.
The numbered ledger is unchanged at 115 companions and five open entries;
the selected-port scope check passes. No upstream code or licensing
changes were needed.


### J.112. Compatible map extension on bounded-span intersection domains

The next domain-organization step requires more than geometric containment:
values must extend to the enlarged domains. The local construction below is
motivated by the gluing argument in [Milićević, Lemma 9.1 and Proposition
9.3](https://arxiv.org/pdf/2601.01682). Our formal statement uses quarter
neighborhoods and proves the additive-quadruple formulation of Freiman
linearity directly. It is not a claim to have formalized Proposition 9.3.

**Local gluing.** Suppose normalized maps `f` and `g` are Freiman-linear
on `bohr T r` and `bohr U r`, and agree on their intersection.
`compatible_bohr_sum_quadruple` proves that the represented values
`f(a)+g(b)` respect every additive quadruple whose `a` coordinates lie
in `bohr T (r/4)` and whose `b` coordinates lie in `bohr U (r/4)`.
The four-term difference in the first domain equals the reversed
four-term difference in the second. Both lie in the full domains by
`bohr_four_term_mem`; compatibility and `freiman_bohr_four_term` give the
value identity. In particular, two representations of the same point
have the same value.

`bohrSumExtension T U f g r` chooses a quarter-radius representation when
one exists. Its value is independent of that choice. It is normalized
and Freiman-linear on `bohrQuarterSum T U r`, the entire sum of the two
quarter neighborhoods. It equals each original map on that map's quarter
neighborhood. Values outside the sum are defined as zero, with no
linearity assertion there.

**Explicit enlarged Bohr domain.** For ranks at most `d` and `0 < r < 4`,
set

```
M = ceil(8/r)
R = polynomialSpectrumCutoff d (r/8) (bohrSumRankThreshold d d M M)
K = boundedFrequencySpan T R intersect boundedFrequencySpan U R.
```

`bohrExtensionSpectrum_subset_sum` applies the existing uniform Bohr-sum
containment theorem at radius `r/4` to prove

```
bohr K (1/(4*pi)) subset bohrQuarterSum T U r.
```

Thus `bohrSumExtension_freiman_span` gives an actual Freiman-linear map
on this Bohr set. `bohrExtensionSpectrum_card_le` supplies the spectral
cap `(2*R+1)^d`. These bounds depend on the radius and rank, with no
modulus-size hypothesis beyond primality for the containment theorem.

**Column differences.** For a pair `p`, define its spectrum as
`T(p.1) union T(p.2)` and its map as `L(p.1,y)-L(p.2,y)`.
`columnDifferenceMap_freiman` derives local linearity from the vertical
identity of a column-domain bihomomorphism. If two pairs have the same
index difference, `columnDifferenceMap_compatible` uses the horizontal
identity to show agreement on their common domain.
`column_differences_span_extension` therefore extends the two difference
maps simultaneously, with spectral rank bounded by

```
(2*bohrExtensionCutoff (2*d) r+1)^(2*d).
```

`global_column_difference_extensions` applies this to the actual global
zero core, directly from the original dense bihomomorphism and the same
modulus threshold. It retains core density, original witness counts,
normalization, and the column-domain bihomomorphism. Every two pairs in
the core with equal index difference have the stated extension. This is
a family of pairwise extensions; compatibility among all choices of
extensions on their enlarged domains is not asserted.

**Remaining structural work.** The intersection spectra still depend on
the two representing pairs. They have not been replaced by values of a
single bounded list of Freiman frequency maps indexed by the difference.
The source's Proposition 9.3 performs this selection and also controls
higher arrangements. Its hypotheses include a structured index domain
and control of higher additive tuples; our current dense four-quadruple
core does not automatically supply those hypotheses. A subsequent
construction must provide the requisite parameter geometry and retain
map-value agreement. Bilinear-variety structure, the final numerical
budget, and the five numbered open statements remain unproved.

**Incoming budget lemma.** This checkpoint also merges
`Proofs16MonomialControlAbsorption` from `origin/main`. It rewrites the
source width control as a real power and proves that monomial count and
width controls imply `MultiplyLinear`, assuming explicit exponent and
logarithmic coefficient bounds. Those numerical conditions remain to be
discharged in the final variety route; the lemma does not prove the deep
structure input.


**Verification.** The local gluing closure checks 139 modules, the span
extension 140, the column-difference application 145, and the global
application 277. All 12 new named extension theorems and the five incoming
monomial-control theorems pass individual axiom checks. The combined
audit checks 7,320 public Gowers theorems in 5,172 modules (5,170 for the
facade, including 4,152 OAI modules), with only `propext`,
`Classical.choice`, and `Quot.sound`. The numbered ledger remains identical
at 115 companions and five open entries, and selected-port scope passes.
No upstream ports or Apache provenance changes were needed.


## J.113. Zero column relations of every bounded even length

The arbitrary-word model construction now feeds an elimination theorem
for every fixed even length, rather than only quadruples. This supplies
the higher identities identified as missing in J.112. It does not supply
the structured index domain required by the source's Proposition 9.3.

**Arity-dependent elimination.** Fix `k > 0`. If all entries of an
alternating list of length `2*k` occupy one of `Q` Dirichlet cells, then

```
centeredAbs (gamma * columnAnchorEval f as) * Q <= k*N.
```

Pair consecutive entries, use cell closeness for each difference, and
apply the centered-distance triangle inequality. With `Q = 5*k`, this
precludes the separation condition `N < 5*centeredAbs(...)`. Thus the
same evaluation test used for quadruples removes every detected model
on a cell retaining at least `beta/(5*k)` of the columns. The common
Bohr testing point and all individual column domains are retained.

`even_model_elimination_iterate` and `even_model_elimination_zero_core`
carry this loss through the logarithmic elimination rounds.
`even_models_initialize` converts the full model cover of
`columnAnchorFibre A (2*k-1) 0` into alternatives: inactive models already
vanish on the kernel neighborhood, and active models keep their original
testing-radius comparisons. `even_model_cover_zero_core` gives a
nonempty core retaining

```
(beta/(5*k))^(modelEliminationRounds beta M) * A.card
```

when the full model count is at most `M`. At `k=2` the cell count is the
previous ten-cell bound. The earlier quadruple interfaces remain valid.

**Global parameters.** Define

```
d     = columnSpectrumCap (columnEightDensity alpha)
delta = globalColumnWordDensity alpha (2*k-1)
g     = ceil((2*k)*d/delta)
M     = ceil(1/delta)
rho   = globalColumnIdentityRadius alpha
r     = globalColumnModelRadius alpha (2*k-1)
s     = min r (refinementKernelRadius g d rho (r/2))
beta  = modelTestDensity g d r
c     = (beta/(5*k))^(modelEliminationRounds beta M)
          * globalColumnVertexDensity alpha/2.
```

The exported names are `globalEvenColumnModelRank`,
`globalEvenColumnModelCount`, `globalEvenColumnZeroRadius`, and
`globalEvenColumnZeroDensity`. The modulus threshold is the maximum of
the global model threshold at `2*k-1`, the new kernel cap plus one, and
seven. The radius is positive and at most `rho`; the density is positive
for positive `k` and `0 < alpha <= 1`.

`global_even_zero_column_core` starts with the original dense
bihomomorphism, the density assumptions, primality, and that explicit
modulus threshold. It produces `X,T,L,W,P,Gamma`, retaining the original
witness system, full-radius column linearity, witness counts, small-radius
linearity, normalization, and original column ranks. The core `P` is a
nonempty subset of `X`, has size at least `c*N`, and `Gamma.card <= g`.
For every `m <= k`, every length-`2*m` list from `P` whose alternating
index sum is zero has zero alternating map value on the intersection
of the common and individual Bohr domains at radius `s`.

**All shorter even relations on one core.** `columnPairPadding` prepends
pairs of the same anchor. Its length grows by two per pair, its
alternating value is unchanged, and all its entries satisfy any
predicate satisfied by the anchor and the original list. For a nonempty
shorter list, use its own first entry as the repeated anchor. Hence
`even_zero_relations_mono` needs no extra frequency or Bohr-domain
assumption. The empty-list case is immediate. In particular, choosing
`k=8` in the global theorem supplies the 4-, 8-, and 16-term identities
simultaneously. No implication from quadruple identities to higher
identities is assumed.

**Remaining work.** These are identities on a dense set with arbitrary
bounded-rank column spectra. Structured index geometry, coherent
frequency selection, preservation of agreement under that construction,
and the final numerical bounds remain to be proved. The common rank
still depends on `1/delta`; no fit to the printed density budget is
claimed. The five numbered open entries and existing source-fidelity
caveats are unchanged. No new upstream code was ported.

**Incoming numeric controls.** `Proofs16VarietyControlAbsorption`, merged
from `origin/main`, converts variety-shaped width and graph-count bounds
into `MultiplyLinear gamma (18*r/gamma + 64 + L)`. Its hypotheses include
positive width coefficient, the scale and density conditions, and
explicit logarithmic bounds absorbed by `L`. This is a numeric bridge
for the variety route; the required deep structure is still open.


**Verification.** The generic elimination closure passes 255 modules,
and the global theorem with shorter-relation padding passes 259 modules.
All 17 new named theorems and the five incoming variety-control theorems
pass individual axiom checks. The final merged audit checks 7,359 public
Gowers theorems in 5,182 modules (5,180 facade modules, including 4,152
OAI modules), using only `propext`, `Classical.choice`, and `Quot.sound`.
The numbered ledger remains identical at 115 companions and five open
entries. Selected-port scope remains 4,134 upstream modules and 17
compatibility modules, with reciprocal-only modules excluded; Apache
license and provenance files are unchanged.


## J.114. Escaping frequencies, indexed selection, and a sharper loss

The first steps of the frequency-selection argument in Claim 9.4 of
[the general U4 inverse theory](https://arxiv.org/pdf/2601.01682) are now
formalized with explicit finite bounds. The new results concern actual
failed containments and selected frequency values; they do not yet
extract the coherent Freiman frequency maps required by Proposition 9.3.

**From failed containment to a new frequency.** Suppose `T` and `U` have
rank at most `d`, `0 < r < 4`, and the selected set `D` satisfies
`D.card*sigma <= 1/(4*pi)`. If `bohr D sigma` is not contained in the sum
of the quarter-radius Bohr sets for `T` and `U`, then
`bohr_sum_frequency_escape` gives a point `y` in that selected Bohr set
and a frequency `q` in `bohrExtensionSpectrum T U d r` such that

```
N/(4*pi) < centeredAbs(q*y)
q not in boundedFrequencySpan D 1.
```

The point cannot lie in the intersection-spectrum Bohr set, by the
previous containment theorem. A violated frequency condition gives `q`.
The bounded-span phase estimate shows that every frequency in the unit
span of `D` has phase at most `N/(4*pi)` at `y`, proving the exclusion.
No duality or separation assumption is added.

`column_pair_frequency_escape` applies this to the unions of the spectra
of four columns. Splitting each union span gives four values `v_i`, each
in its own column's bounded span at cutoff `R = bohrExtensionCutoff
(2*d) r`, with `v_0-v_1 = v_2-v_3` outside the unit span of `D`. Overlap
between the two frequency sets in a union does not increase the cutoff.

**Indexed averaging.** `exists_good_indexed_selection` counts requirements
by their original indices, even when several indices prescribe identical
values on identical supports. If every allowed-value set has at most `K`
elements and every requirement specifies at most `m` values, one
selection meets at least a `K^(-m)` fraction of the indexed requirements.
This follows by counting all assignments and interchanging two finite
sums. There is no support-image multiplicity loss.

`exists_good_colored_selection` uses the domain `Fin m × X` to select
`m` independent functions. Each requirement prescribes one value per
color. Positions in `X` may repeat: their colors distinguish the specified
assignments. Consequently no distinct-position hypothesis or discarded
diagonal count is needed for this result.

`exists_escaping_frequency_selection` combines those facts. Given an
arbitrary finite indexed family `B` of failed containments, spectra of
rank at most `d`, and the stated selected-set radius bound for each
configuration, it produces four frequency maps `f_i`, all taking values
in the relevant bounded column spans, such that

```
B.card <= (2*R+1)^(4*d) * good.card.
```

Here `good` counts the original configurations for which the selected
frequency differences agree and escape the prescribed unit span. This
is the exact finite averaging loss for this construction; index-additivity
can be imposed by the choice of `B`, but is not needed by the selection
itself. The four maps are not asserted to be Freiman maps.

**Independent-family growth.** A frequency outside the unit bounded span
of a dissociated set can be inserted while preserving dissociation.
`bounded_span_escape_rank_budget` then proves

```
D.card + 1 <= spanGeneratorBound K.card R
```

when both the selected family and the new frequency lie in the bounded
span of `K` at cutoff `R`. `bohr_escape_extends_independent_family` applies
this to the frequency supplied by an actual failed containment. This
provides the pointwise insertion and rank-budget facts for a later global
selection iteration; the global iteration is not yet constructed.

**Quantitative improvement to the existing selection lemma.** For a
single selected function, `exists_good_quad_selection` still requires
consistent prescriptions at repeated indices. It counts the original
quadruples directly with loss `K^4`. Combining it with the existing energy
extraction proves `lemma19_indexed_selection_piece_eight`: if all four
prescribed values belong to the new-value sets and

```
delta*N^3*K^4 <= T.card,
```

there is an order-eight Freiman piece of size at least
`2^(-1882)*delta^1164*N`. The previous all-new-values interface required
`256*delta*N^3*K^4`. Thus, for fixed `delta`, the required configuration
count improves by a factor 256. The two-new-value and mixed selection
interfaces and the downstream `corollary20Kappa` parameter have not yet
been strengthened. No improved final density bound follows here.

**Scope.** Structured index geometry, extraction of coherent new Freiman
frequency maps from the escaping configurations, the higher-arrangement
selection, and preservation of agreement through that organization
remain open. The five numbered open entries and all documented
source-fidelity caveats remain unchanged. No upstream code was ported,
and the Apache license and provenance files are unchanged.


**Verification.** The escaping-frequency selection closure checks 143
modules, the independent-family extension checks 142, and the stronger
Freiman selection checks 53. All ten new named theorems pass individual
axiom checks. The combined audit checks 7,389 public Gowers theorems in
5,187 modules (5,185 facade modules, including 4,152 OAI modules), with
only `propext`, `Classical.choice`, and `Quot.sound`. The numbered ledger
is identical at 115 companions and five open entries. The selected-port
scope check passes with 4,134 upstream and 17 compatibility modules.


## J.115. Freiman extraction retaining mixed frequency configurations

The four frequency maps selected in J.114 can now be made Freiman on
four dense coordinate domains, while an explicitly dense subfamily of
the original escaping configurations remains. This supplies the
coordinate-extraction part of the structural argument; the four maps
have not yet been identified with one common difference-index map.

**Mixed energy.** `keyMatchingCount` counts pairs from two finite families
whose keys, computed by possibly different functions, agree. Its finite
fibre-sum formula and Cauchy--Schwarz inequality give the generic counting
step. For column maps, the mixed key of `(x,y)` is
`(x-y,f(x)-g(y))`. `mixedColumnEnergy A B C D f g h l` counts equal keys
between `A × B` and `C × D`.

Regrouping a self-comparison of the mixed keys of `f,g` gives a comparison
of the ordinary difference keys of `f` on `A × A` and `g` on `B × B`.
Two Cauchy--Schwarz steps therefore prove

```
mixedColumnEnergy A B C D f g h l ^ 4
  <= phiAdditiveCount A f * phiAdditiveCount B g
       * phiAdditiveCount C h * phiAdditiveCount D l.
```

The unrestricted energy of each of the last three maps is at most `N^3`.
Consequently, any family of at least `delta*N^3` mixed additive quadruples
with first coordinate in `A` forces at least `delta^4*N^3` respected
quadruples of `f` on `A`. `mixed_quadruples_freiman_piece` applies the
existing order-eight Corollary 7.6 extractor, giving a subset of `A` of
size at least `2^(-1882)*(delta^4)^1164*N` where `f` is Freiman of order
eight. The other three maps need not agree with `f`.

**Retaining the original configurations.** A Freiman piece in an arbitrary
coordinate projection need not support many original configurations.
Before extraction, retain only first-coordinate fibres containing at
least `delta*N^2/2` configurations. The new generic
`popular_fibre_retained_mass` shows that this discards at most
`delta*N^3/2` configurations. It requires no upper bound on fibre size.
`fibre_filter_mass_lower` then controls the mass retained by every subset
of popular endpoints.

Define the explicit positive retention function

```
H(delta) = delta/2 * (2^(-1882) * ((delta/2)^4)^1164).
```

`mixed_configurations_retain_freiman_piece` yields a coordinate set `E`
and a subfamily `R` of the original family, all of whose first coordinates
lie in `E`, with `FreimanHom 8 E (f 0)` and `R.card >= H(delta)*N^3`.
The proof retains the original configurations by filtering, so any extra
property of those configurations, including escape from a selected
frequency span, is preserved.

**Every coordinate.** The four permutations

```
[0,1,2,3], [1,0,3,2], [2,3,0,1], [3,2,1,0]
```

preserve the equation `x0-x1 = x2-x3` and move the chosen coordinate to
position zero. Reindexing and its inverse preserve cardinality and the
original subfamily relation. `mixed_configurations_retain_coordinate`
therefore gives the same retention bound for any coordinate.

Set `mixedConfigurationDensity delta 0 = delta` and recursively apply
`H` for each additional extraction. An induction over a finite set of
coordinates restricts configurations while retaining all previously
proved Freiman properties. `mixed_configurations_freiman_family` treats
all four coordinates: it returns four sets `E_i` and a subfamily `R`,
with each `f_i` Freiman of order eight on `E_i`, every `q_i` in `E_i`,
and `R.card >= mixedConfigurationDensity delta 4*N^3`.

Each coordinate set also has density at least
`mixedConfigurationDensity delta 4`. Indeed, three coordinates determine
an additive quadruple, so a family whose chosen coordinate lies in `E`
has size at most `E.card*N^2`. Both this exact finite bound and its real
density consequence are proved in `Proofs16MixedCoordinateDensity`.

**Application to failed Bohr containments.** For
`R = bohrExtensionCutoff (2*d) r`, define

```
escapingFreimanDensity delta d r
  = mixedConfigurationDensity (delta/(2*R+1)^(4*d)) 4.
```

`failed_containments_freiman_family` starts from at least `delta*N^3`
additive index quadruples, bounded column spectra, and the actual
selected-frequency containment failures of J.114. It obtains four maps
taking values in their column bounded spans, four dense order-eight
Freiman coordinate domains, and a subfamily of density at least
`escapingFreimanDensity delta d r`. Every retained configuration still
has equal map differences outside its prescribed selected unit span.
The same density lower-bounds all four coordinate domains. Positivity of
the recursive density and of this applied density is proved.

**Remaining structural work.** The four maps live on distinct dense
coordinate sets. A common map indexed by column differences, suitable
Bohr/progression extensions, higher-arrangement selection, and the global
independent-family iteration remain to be constructed. The final
bilinear-variety structure and numerical budget are still open. No
numbered source statement is closed by this checkpoint, and no new
upstream port or license change was needed.


**Verification.** The complete failed-containment Freiman-family closure
checks 251 modules. All 23 new named theorems pass individual axiom
checks. The full audit checks 7,431 public Gowers theorems in 5,196
modules (5,194 facade modules, including 4,152 OAI modules), with only
`propext`, `Classical.choice`, and `Quot.sound`. The numbered ledger is
identical at 115 companions and five open entries; the selected-port
scope check still passes with 4,134 upstream and 17 compatibility modules.

### J.116. One common Freiman map on translated column differences

The four coordinate maps from J.115 now yield a single difference map
on a dense retained family, with an explicit cubic retention bound.
The six new modules are `Proofs16MixedGraphOverlap`,
`Proofs16FreimanTranslateCover`, `Proofs16CommonGraphCover`,
`Proofs16FourfoldGraphMap`, `Proofs16CommonDifferenceRetention`, and
`Proofs16EscapingDifferenceMap`.

**Dense overlap without discarding the configurations.** Suppose `Q`
contains at least `delta*N^3` mixed configurations, with coordinates zero
and one in `A` and `B`. Fixing coordinates two and three leaves a fibre
whose projection to coordinate one has at least `delta*N` elements.
The additive index equation makes this projection injective. Thus there
are `a,c,S`, with `S` contained in `B`, such that `s+a` belongs to `A`
and `f0(s+a)=f1(s)+c` for every `s` in `S`. This overlap is auxiliary:
the subsequent covering still applies to every original configuration.

**A graph cover with reciprocal-density cost.** For a Freiman map `f`
on `A` and a subset `S` of density at least `mu`, the graph sum
`{(x+s,f(x)+f(s)) : x in A, s in S}` has at most `N` elements.
Indeed, its first-coordinate projection is injective by the Freiman
identity. Applying the existing disjoint-family packing theorem yields
anchors `J` in `A` with `J.card*mu <= 1`. Each `x` has witnesses
`j in J`, `u,v in S` satisfying both `x=j+u-v` and
`f(x)=f(j)+f(u)-f(v)`.

Apply this to the shifted overlap in `A` and the original overlap in
`B`. The two anchor sets satisfy `J.card*K.card*delta^2 <= 1`.
Every mixed difference is represented as

```
x-y = (j-k)+(u-v)-(w-z)
f0(x)-f1(y) = (f0(j)-f1(k))+(f1(u)-f1(v))-(f1(w)-f1(z)),
```

with all four representation points in the same set `S`.

**The common map and retained mass.** `fourfoldGraphDomain S` is
`2S-2S`, represented as `(u-v)-(w-z)`. An order-eight Freiman map on `S`
induces a map `theta` on this entire difference set. Its values are
independent of representation, and it preserves additive quadruples.
The proof converts each relation between four represented differences
into an equality of sums of eight original points, counting repetitions.

`mixed_configurations_common_difference_map` chooses one of the at most
`delta^-2` anchor pairs. It returns `S`, `theta`, constants `a,c`, and
`R` contained in the original `Q`, with

```
S.card >= delta*N,
R.card >= delta^3*N^3,
f0(q0)-f1(q1) = c+theta(q0-q1-a)       (q in R).
```

Every argument `q0-q1-a` lies in `fourfoldGraphDomain S`. The theorem
also retains agreement with every four-term representation. No primality
assumption is needed for these covering and retention arguments.

**Application to actual failed containments.** Set
`epsilon = escapingFreimanDensity delta d r` from J.115.
`failed_containments_common_difference_map` produces a set `S` of density
at least `epsilon` and at least `epsilon^3*N^3` original configurations.
On each retained configuration the common value
`c+theta(q0-q1-a)` equals both selected pair differences and remains
outside its prescribed unit span. The four selected maps still take
values in their original column bounded spans; `f1` remains order-eight
Freiman on `S`. Thus the common map is obtained from the actual
containment failures, rather than assumed as an extra structural input.

**Incoming numerical progress and remaining work.** The merge from
`origin/main` also adds `Proofs16VarietyPieceBudget`. Its theorem
`variety_piece_budget` proves that the variety piece parameter fits the
dimension-three budget provided the logarithmic loss `L` is at most
`(2/(theta*gamma))^(64*2^256)`. That hypothesis and the missing variety
structure must still be supplied. Our common difference map lives on
`2S-2S`; the required Bohr/progression localization, retention through
that localization, higher-arrangement selection, and independent-family
iteration remain open. This checkpoint closes no numbered paper entry
and claims no new final bound for the full source theorem. It adds no
upstream port and changes no licensing material.

**Verification.** The new failed-containment common-map closure checks
265 modules. All ten new named theorems and the four incoming budget
theorems pass individual axiom checks. The complete merged audit checks
7,453 public Gowers theorems in 5,203 modules (5,201 facade modules,
including 4,152 OAI modules), using only `propext`, `Classical.choice`,
and `Quot.sound`. The numbered ledger is byte-for-byte unchanged at
115 companions and five open entries. The selected-port scope remains
4,134 upstream and 17 compatibility modules; reciprocal-only modules
remain excluded.

### J.117. Common difference maps on controlled Bohr neighborhoods

The common map from J.116 now has a full Bohr domain, and a quantitatively
dense family of original configurations has its translated differences
in the half-radius neighborhood. The escape from the prescribed unit
span is preserved on every retained configuration.

**Separate the two density costs.** The new
`common_graph_cover_retained_fibre` accepts an already chosen overlap
`S` of density `mu` and an original configuration family of density
`delta`. The graph cover uses at most `mu^-2` anchor pairs, so a single
pair retains at least `mu^2*delta*N^3` configurations. The supplied map
need only agree with every four-term representation on `S`; its larger
domain and Freiman properties are retained by the caller. The earlier
cubic retention theorem is now a consequence with `mu=delta`, avoiding
a duplicate pigeonhole proof.

**Small clusters preserve fourfold values.** If all pairwise differences
in `C` lie in `B(Gamma;rho/4)`, their differences lie in
`B(Gamma;rho/2)`. For a map on `E` that extends to `B(Gamma;rho)`, with
`C` contained in `E`, the normalized extension satisfies

```
psi((u-v)-(w-z)) = (f(u)-f(v))-(f(w)-f(z))
```

for all four points in `C`. The proof uses the order-two Freiman identity
on the full neighborhood, its value at zero, and its agreement on pair
differences. Both neighborhood membership and value agreement are proved
in `Proofs16FourfoldBohrExtension`.

**Uniform parameters.** For an input density `kappa > 0`, define

```
rho(kappa) = commonDifferenceRadius kappa = kappa/(32*pi),
r(kappa)   = commonDifferenceRank kappa = ceil(16*kappa^(-2)),
M(kappa)   = commonDifferenceCells kappa = ceil(8/rho(kappa)),
mu(kappa)  = commonDifferenceClusterDensity kappa
           = kappa/M(kappa)^r(kappa),
beta(kappa) = commonDifferenceBohrDensity kappa
            = mu(kappa)^2*kappa.
```

Positivity of the radius, cell count, cluster density, and final retained
density is proved. The rank ceiling also proves that `mu(kappa)` is a
valid lower bound for the density computed with any spectrum of rank at
most `16*kappa^(-2)`.

`dense_freiman_fourfold_bohr_cluster` starts with an order-eight Freiman
map on a set of density at least `kappa`. The existing dense extension
theorem gives a spectrum of rank at most `16*kappa^(-2)` and radius
`rho(kappa)`. Averaging produces a cluster whose pairwise differences
lie in the quarter-radius Bohr set. The existing Bohr cardinality lower
bound, with `M(kappa)` cells per frequency, gives this cluster ambient
density at least `mu(kappa)`. Its fourfold graph values therefore agree
with a normalized Freiman map on the full Bohr set, and its fourfold
indices lie in the half-radius set.

**Mixed configurations and actual failures.**
`mixed_configurations_common_bohr_map` extracts the dense overlap from
J.116, localizes it to the cluster above, and applies the generalized
retention theorem. From `delta*N^3` configurations it returns a subfamily
of size at least `beta(delta)*N^3`, a spectrum of rank at most
`16*delta^(-2)`, and a normalized order-two Freiman map `psi` on
`B(Gamma;rho(delta))`. There are constants `a,c` such that every retained
configuration satisfies

```
q0-q1-a in B(Gamma;rho(delta)/2),
f0(q0)-f1(q1) = c+psi(q0-q1-a).
```

No primality assumption is needed for this mixed-map localization.
`failed_containments_common_bohr_map` applies it to the coordinate maps
from the actual containment failures of J.115. With
`epsilon = escapingFreimanDensity delta d r`, its retained density is
`beta(epsilon)`. The common value equals both selected pair differences,
stays outside each configuration's selected unit span, and the selected
maps still belong to their original bounded column spans.

**Remaining work.** This closes the common Bohr-map step, not the proper
progression or global iteration steps. A proper progression inside a
Bohr set is already available through `exists_proper_progression_in_bohr`,
but a dense retained family with differences in a suitable translated
progression must still be constructed. Higher arrangements, the global
independent-family iteration, the final bilinear variety structure, and
its remaining quantitative inputs are also still open. No numbered
source entry or final source-theorem bound is claimed by this checkpoint.
No upstream code was ported and no license or provenance file changed.

**Verification.** The new failed-containment Bohr-map application and
previous difference-map application check together in 271 modules. All
eleven new named theorems and the refactored common-difference theorem
pass individual axiom checks. The full audit checks 7,470 public Gowers
theorems in 5,209 modules (5,207 facade modules, including 4,152 OAI
modules), using only `propext`, `Classical.choice`, and `Quot.sound`.
The numbered ledger is byte-for-byte unchanged at 115 companions and
five open entries. The scope check still reports 4,134 upstream and
17 compatibility modules, excluding reciprocal-only dependencies.

### J.118. Common escaping maps on a proper progression

The common Bohr map from J.117 can now be recentered on one proper
centered progression while retaining a quantitatively dense family of
original configurations. The proof averages configurations with their
full multiplicities; projecting to a set of difference values would not
justify the same retained-mass bound.

**Indexed translation averaging.** For any finite index family `Q`, any
map `x` into `ZMod N`, and any test set `P`,

```
sum_t card {q in Q : x(q)-t in P} = Q.card*P.card.
```

`indexed_translate_filter_sum` proves this exact identity over the reals
by interchanging the sums and using the bijection `t -> x(q)-t` for each
fixed configuration. Consequently, if `Q.card >= mass >= 0` and
`P.card >= eta*N`, some translate retains at least `eta*mass` indices.
No injectivity of `x` is assumed.

**Recentering the Freiman values.** Suppose all `x(q)` lie in
`B(Gamma;rho/2)`, the test set also lies in that half-radius neighborhood,
and `psi` is a normalized order-two Freiman map on `B(Gamma;rho)`.
Positive retained mass supplies one retained index `q0`; then
`t=x(q0)-(x(q0)-t)` lies in the full Bohr neighborhood. For each retained
index, all four arguments `x(q),0,t,x(q)-t` lie in the full domain, so
its Freiman identity gives

```
psi(x(q)) = psi(t)+psi(x(q)-t).
```

`bohr_freiman_translate_retention` proves this with the original index
subfamily and its mass bound. No value of `psi` outside its proved
Freiman domain is used in this recentering argument.

**Uniform progression parameters.** Define

```
bohrProgressionDensity(r,rho)
  = exp(-((r+1)*log(1+rho^(-1))+10*(r+1)^2)).
```

For any spectrum of cardinality at most `r` and `rho > 0`,
`exists_uniform_proper_progression_in_bohr` returns a proper centered
progression of rank at most `r+1`, contained in `B(Gamma;rho/4)`, with
cardinality at least `bohrProgressionDensity(r,rho)*N`. This is the
existing proper Bohr progression theorem, combined with its proved
logarithmic width choice and monotonicity in the rank bound. The density
is positive. The progression itself is proper; no properness assertion
is made about a dilation of it.

Combining this progression with indexed translation retention gives
`bohr_freiman_progression_retention`. It preserves the original
normalized map on the full Bohr neighborhood, returns the actual
progression and recentering translation, and retains at least the
progression-density fraction of the configuration mass.

**Common mixed and escaping values.** With the J.117 parameters, set

```
eta(kappa) = commonDifferenceProgressionDensity kappa
           = bohrProgressionDensity(r(kappa),rho(kappa)),
xi(kappa)  = commonDifferenceProgressionRetention kappa
           = eta(kappa)*beta(kappa).
```

Both positivity statements are proved. The theorem
`mixed_configurations_common_progression_map` starts from `delta*N^3`
mixed configurations, the first coordinate's Freiman map and the second
coordinate's order-eight map. It obtains a proper centered progression
`P` with rank at most `r(delta)+1` and size at least `eta(delta)*N`, a
subfamily of at least `xi(delta)*N^3` original configurations, and
constants `a,c` such that every retained configuration satisfies

```
q0-q1-a in P.carrier,
f0(q0)-f1(q1) = c+psi(q0-q1-a).
```

The spectrum bound `16*delta^(-2)`, the full-domain order-two Freiman
property, and normalization at zero are retained. The progression lies
in the quarter-radius neighborhood. This theorem requires no primality
assumption.

`failed_containments_common_progression_map` applies it to actual failed
Bohr containments. For `epsilon = escapingFreimanDensity delta d r`, the
retained mass is at least `xi(epsilon)*N^3`. On every retained
configuration, the common progression value equals both selected pair
differences and remains outside the prescribed selected unit span.
All four maps keep their original bounded column-span membership.

**Remaining structural work.** The difference-map progression
localization is now proved for the four-coordinate configuration case.
Higher arrangements, coherent maps across the needed relation families,
and the global independent-family iteration remain open. The final
bilinear variety structure and remaining quantitative hypotheses have
not been supplied. No numbered catalogue entry is closed here, and no
new final source-theorem bound is claimed. The existing selected port is
sufficient; provenance and licensing material are unchanged.

**Verification.** The escaping-progression application checks 274
modules. All ten new named theorems pass individual axiom checks. The
full audit checks 7,483 public Gowers theorems in 5,215 modules (5,213
facade modules, including 4,152 OAI modules), using only `propext`,
`Classical.choice`, and `Quot.sound`. The numbered ledger is byte-for-byte
unchanged at 115 companions and five open entries. The selected-port
scope remains 4,134 upstream and 17 compatibility modules, excluding
reciprocal-only dependencies.

### J.119. Dense pair escape and the independent-family rank budget

The progression result of J.118 now gives the pair-enlargement ingredient
for the frequency-selection iteration. This follows the role of
[Claim 9.4 in the auxiliary inverse-theorem source](https://arxiv.org/html/2601.01682v1#S9):
one common map supplies a new independent frequency on many column
pairs. The present explicit parameters come from J.115–J.118; no claim
is made that they match that source's quasipolynomial estimates.

**From quadruples to pairs.** If an additive quadruple's first pair and
third coordinate are known, its fourth coordinate is determined. Thus
`additive_quadruples_pair_card_le` proves `Q.card <= E.card*N` whenever
all first pairs lie in `E`. Its real-density consequence turns
`delta*N^3` quadruples into at least `delta*N^2` pairs, including when
coordinates repeat. The new paired projection therefore preserves the
normalized retained density from J.118.

**Keep the translation and constant term.** Define
`translatedFreimanDomain S a = {a+x : x in S}`. Membership is equivalent
to `x-a in S`, and cardinality is unchanged. If `psi` is order-two
Freiman on `S`, then `theta(x)=c+psi(x-a)` is order-two Freiman on this
translated domain. These facts allow the selected map to be used at the
actual column difference, without silently dropping either `a` or `c`.

**Ambient span accounting.** Increasing a generator set preserves its
bounded span at the same cutoff. A difference of elements in the spans
of `K` and `L`, at respective cutoffs `R` and `S`, belongs to the span
of `K union L` at cutoff `R+S`. In particular, the selected column-map
values give cutoff `2*bohrExtensionCutoff (2*d) r` for their difference.
This factor of two is retained explicitly; overlapping generator sets
do not justify claiming the original cutoff for an arbitrary difference.

**A common map escaping on many pairs.**
`failed_containments_dense_pair_escape` takes the actual failure family
and a selected-frequency set `F(p)` for each column pair. The only
connection needed is `F(q0,q1)` contained in the quadruple's selected set
`D(q)`. It returns a proper progression `P`, a translation `a`, one
Freiman map `theta` on `a+P`, and a set `E` of first pairs from the original
family. With `epsilon = escapingFreimanDensity delta d r`,

```
E.card >= commonDifferenceProgressionRetention epsilon*N^2.
```

For every `p in E`, its difference lies in `a+P`, and `theta(p1-p2)`
belongs to the union of its column spans at the doubled cutoff while
lying outside the unit span of `F(p)`. The progression rank and size
bounds from J.118 are preserved.

**Exact growth and a finite budget.** `extendIndependentFamily` inserts
the new value at each chosen index and leaves the other sets unchanged.
Theorems prove that this preserves dissociation and ambient bounded-span
membership, contains every old selected set, and increases each selected
cardinality by exactly one. For `E` contained in an index set `Omega`,

```
sum_Omega card(F') = sum_Omega card(F)+E.card.
```

If each ambient generator set has size at most `k`, the total cardinality
is at most `Omega.card*spanGeneratorBound k R`. Consequently, any
sequence whose successive total increases are at least
`eta*Omega.card` satisfies `n*eta <= spanGeneratorBound k R` after `n`
steps. The proof requires only the invariant at the final state and the
proved increment inequalities for the preceding steps.

**Actual failed-containment increment.**
`failed_pair_containments_increase_rank` specializes the quadruple's
selected set to the union of its two pair selections. Assuming these
pair selections are dissociated and lie in their ambient doubled-cutoff
spans, it produces the common progression map and dense pair set above.
Updating those pairs preserves the invariants and gives the exact total
increment. The resulting total satisfies

```
sum_p card(F'(p))
  <= N^2*spanGeneratorBound (2*d) (2*bohrExtensionCutoff (2*d) r).
```

**Remaining work.** These are an actual improvement step and a proved
bound on sequences of improvements. A complete selection procedure that
records its maps and domains and terminates with few failed containments
has not yet been constructed. The more complicated arrangement
improvement corresponding to Claim 9.5 is also still missing. Global
coherence, the final bilinear variety structure, and its remaining
quantitative inputs stay open. No numbered source entry is closed here.
The existing selected port suffices; no license or provenance changes
were needed.

**Verification.** The actual dense-pair rank-increment closure checks
282 modules. All fourteen new named theorems pass individual axiom
checks. The full audit checks 7,502 public Gowers theorems in 5,222
modules (5,220 facade modules, including 4,152 OAI modules), using only
`propext`, `Classical.choice`, and `Quot.sound`. The numbered ledger is
byte-for-byte unchanged at 115 companions and five open entries. The
selected-port scope remains 4,134 upstream and 17 compatibility modules,
with reciprocal-only dependencies excluded.

### J.120. Complete selection for quadruple pair containments

The actual pair-enlargement step from J.119 now terminates with a finite
list of controlled Freiman maps and few failed quadruple containments.
The result records the maps and their domains throughout the argument;
it does not replace them by arbitrary pointwise frequency sets.

**Fixed iteration parameters.** For fixed column rank `d` and radius
`r`, define

```
R = pairSelectionCutoff d r = 2*bohrExtensionCutoff (2*d) r,
s0 = pairSelectionRank d r = spanGeneratorBound (2*d) R,
sigma = pairSelectionRadius d r = 1/(8*pi*(s0+1)),
eta = pairSelectionGain delta d r
    = commonDifferenceProgressionRetention (escapingFreimanDensity delta d r).
```

The radius is positive, and `eta > 0` when `delta > 0`. Every dissociated
pair selection in its ambient cutoff-`R` span has cardinality at most
`s0`. Therefore the union of the selections from the two pairs of any
quadruple satisfies the radius hypothesis
`selected.card*sigma <= 1/(4*pi)`. This is a uniform hypothesis for every
stage of the iteration, including an empty selection.

**Recorded state and invariant.** `PairFrequencyMap` stores an actual
proper centered progression, its translation, and its map. Its
`Controlled` predicate retains the rank and density bounds from J.118
and the order-two Freiman property on the translated progression.
`PairSelectionState` stores a list of these maps and a selected frequency
set for each column pair. Its validity predicate asserts:

- every listed map is controlled at the fixed extraction density;
- every pair selection is dissociated and lies in its prescribed
  bounded column-union span;
- every selected frequency is the value of a listed map at that pair's
  difference, with the difference in that map's domain;
- the list length times `eta*N^2` is at most the total selected-frequency
  cardinality.

The empty state is valid. The total rank bound gives
`maps.length*eta <= s0` for every valid state.

**A genuine improvement preserves the state.** Define the failure
family by filtering the prescribed additive quadruples for which

```
B(F(q0,q1) union F(q2,q3);sigma)
  is not contained in
bohrQuarterSum (T(q0) union T(q1)) (T(q2) union T(q3)) r.
```

If there are at least `delta*N^3` failures, `PairSelectionState.improve`
applies the actual failure theorem from J.119. It prepends the resulting
controlled map, adds its values on the improved pair set, and proves all
four validity properties again. Old frequency sets are contained in the
new ones. The exact cardinality increment and the improved pair density
supply the required growth inequality for the longer list.

**Termination.** `exists_pair_frequency_selection` proves existence of
a valid state with fewer than `delta*N^3` failures. If none existed,
repeated improvements would give valid states of every finite list
length. Choosing a length greater than `s0/eta` contradicts the rank
budget. The result retains `maps.length*eta <= s0`, and a companion gives
`maps.length <= floor(s0/eta)`. These bounds are independent of the
modulus. This is a classical existence proof, not an executable search
implementation.

**Actual map indices.** For each pair, select one list index for each
frequency using the validity witnesses. Distinct frequencies force
distinct selected indices. `PairSelectionState.pair_indices` and
`index_family` therefore return exact image identities, equal index and
frequency cardinalities, and domain membership for every selected
index.

The exported theorem `pair_frequency_selection` gives a natural number
`m`, maps `g : Fin m -> PairFrequencyMap N`, and pair-specific index sets
`I(p)`, with

```
m*eta <= s0,
I(p).card <= s0,
card {g_i(p1-p2) : i in I(p)} = I(p).card.
```

Every selected value has the required domain membership, the resulting
frequency set is dissociated and contained in its ambient bounded span,
and fewer than `delta*N^3` of the prescribed additive quadruples fail
the containment. All map rank, size, properness, and Freiman assertions
remain available through `Controlled`.

**Remaining work.** This completes the quadruple-containment selection
iteration. It does not provide the higher-arrangement improvement or the
simultaneous selection needed for the corresponding twelve-tuple
containments. The later anchor choices, coherent gluing, and final
bilinear variety structure remain open, as do the remaining numerical
hypotheses. No numbered catalogue entry or final source-theorem bound is
claimed here. No new port or licensing change was necessary.

**Verification.** The complete quadruple-selection closure checks 288
modules. All twelve new named theorems pass individual axiom checks.
The full audit checks 7,526 public Gowers theorems in 5,228 modules
(5,226 facade modules, including 4,152 OAI modules), using only
`propext`, `Classical.choice`, and `Quot.sound`. The numbered ledger is
byte-for-byte unchanged at 115 companions and five open entries. The
selected-port scope remains 4,134 upstream and 17 compatibility modules,
with reciprocal-only dependencies excluded.


### J.121. Higher-arrangement extraction with controlled multiplicity

The first-coordinate extraction for the sixteen-map arrangement is now
proved. The argument first treats a general indexed offset equation and
then specializes it to the eleven free parameters of the larger
arrangement. It retains actual configurations rather than only their
endpoint image.

**Indexed collisions.** Let `Q` be a subset of `I x ZMod N`, let
`a,v : I -> ZMod N`, and suppose every offset fibre `a^{-1}(z)` has
cardinality at most the positive integer `M`. Assume

```
f(x+a(i)) - g(x) = v(i)  for every (i,x) in Q,
card Q >= delta*M*N^2.
```

Cauchy--Schwarz gives `card Q^2 <= card W * card I`, where `W` is the
family of pairs in `Q` with equal parameter `i`. The offset-fibre bound
also gives `card I <= M*N`. Project a collision to

```
(x+a(i), x, y+a(i), y).
```

The projection's multiplicity is at most `M`: its image fixes `x`, `y`,
and `a(i)`, leaving at most `M` choices of `i`. Consequently its image
has at least `delta^2*N^3` distinct mixed quadruples. Their endpoint
and value relations agree with the already proved mixed-quadruple
extraction theorem. This establishes `offset_equation_freiman_piece`
without dropping the multiplicity factor.

**Retaining the original family.** Use popular endpoints `x+a(i)` at
threshold `delta*M*N/2`. At least `delta*M*N^2/2` original configurations
survive this restriction. Applying the collision argument to that family
gives an order-eight Freiman set `E` with

```
card E >= 2^(-1882) * (((delta/2)^2)^4)^1164 * N.
```

Retaining all original configurations whose endpoint belongs to `E`
therefore gives a family `R` with

```
card R >= H(delta)*M*N^2,
H(delta) = delta/2 * (2^(-1882) * (((delta/2)^2)^4)^1164).
```

The formal definition is `offsetFreimanRetention`; it is positive for
positive `delta`. The theorem also records `R subset Q`, the endpoint
membership for every member of `R`, and `E subset` the original endpoint
image. The normalized density loss is independent of `M` and `N`.

**Sixteen endpoints and eleven free parameters.** Write the parameter
as `((a,z),x)` with `z : Fin 9 -> ZMod N`. Set the four shifts to
`a`, `z0`, `z1`, and `a+z0-z1`, so their required additive relation is
identically satisfied. The four left base points are `x,z2,z3,z4` and
the four right base points are `z5,z6,z7,z8`. Each base point and its
shifted copy supply two endpoints. `HigherArrangementEquation` equates
the sum of the four left map differences to the sum of the four right
map differences.

Separating the first base point `x` writes this equation as
`f0(x+a)-f1(x)=v(a,z)`. The offset fibres have exactly `N^9` parameters,
and the full parameter space has exactly `N^11` elements. Thus
`higher_arrangements_retain_first_freiman_piece` takes a family of at
least `delta*N^11` solutions and retains at least `H(delta)*N^11`
original solutions whose first endpoint lies in an order-eight Freiman
set for `f0`, with the explicit size bound above.

**Remaining work.** This extracts only the first coordinate. Transport
to the other fifteen endpoints and successive extraction on the same
retained family remain to be proved. Common pair-map alignment, the
higher-arrangement improvement, simultaneous selection, anchor coherence,
and the final bilinear variety structure are also still open. The
quadruple selection in J.120 does not by itself supply these conclusions.
No numbered catalogue entry or final source-theorem bound is claimed
here. No new upstream port or licensing change was necessary.

**Verification.** The first-coordinate extraction closure checks 227
modules. All twelve new named theorems pass individual axiom checks.
The full audit checks 7,545 public Gowers theorems in 5,234 modules
(5,232 facade modules, including 4,152 OAI modules), using only
`propext`, `Classical.choice`, and `Quot.sound`. The numbered ledger is
byte-for-byte unchanged at 115 companions and five open entries. The
selected-port scope remains 4,134 upstream and 17 compatibility modules,
with reciprocal-only dependencies excluded.


### J.122. Simultaneous Freiman extraction at all sixteen endpoints

The first-coordinate argument from J.121 now applies to every endpoint
and can be iterated on one retained family of higher arrangements. This
completes the dense-set Freiman extraction stage for all sixteen maps.
It does not yet put paired maps on a common progression or align their
difference maps.

**Symmetries with their parameter maps.** `HigherArrangementSymmetry`
records a bijection of the eleven-parameter space, a permutation of the
sixteen endpoints, the identity relating these two maps, and preservation
of the arrangement equation after reindexing the sixteen functions.
Composition reverses the order of the coordinate pullbacks relative to
the parameter maps. Four explicit involutions generate the symmetries
needed here:

- reverse every shifted/unshifted pair, negating all four shifts;
- exchange the first two shifts and the last two shifts simultaneously;
- exchange the first two shifts with the last two shifts;
- exchange all left base points with the corresponding right base points.

The shift relation `a1+a2=a3+a4` is preserved by each construction.
The parameter transformations are proved involutive, and their endpoint
identities are proved at every coordinate. The equation is preserved,
with an overall sign change for pair reversal and side exchange.
`higherArrangementCoordinateSymmetry_zero` proves that the selected
symmetry takes any prescribed endpoint to position zero in the
reindexed arrangement.

**No extra density loss from reindexing.** Apply the first-coordinate
extraction to the bijective image of the original family, and pull the
retained subfamily back through the inverse parameter map. Both finite
families retain their exact cardinalities. Thus
`higher_arrangements_retain_coordinate` provides the same set-size and
configuration-retention bounds as J.121 for any `i : Fin 16`. The result
records containment in the original family and original endpoint image,
not just a family of abstract solutions to the reindexed equation.

**Coordinate fibres.** For any coordinate `i`, a parameter tuple is
determined by its `i`-th endpoint and the ten-coordinate index of its
reparametrization. The remaining base point is recovered by subtraction.
This gives, for an arbitrary family `R` with its `i`-th endpoint in `E`,

```
card R <= card E * N^10.
```

No arrangement-equation hypothesis is needed for this fibre bound.
Consequently `card R >= delta*N^11` implies `card E >= delta*N`.

**One family for all sixteen maps.** Define the explicit density sequence

```
c_0 = delta,
c_(n+1) = H(c_n),
H(t) = t/2 * (2^(-1882) * (((t/2)^2)^4)^1164).
```

`higherArrangementDensity_pos` proves positivity at every finite stage
for positive initial density. Induction on any finite subset of endpoint
positions uses the coordinate extraction to shrink the retained family.
Previously extracted Freiman sets stay valid, since all subsequent
families are subsets of their predecessors. The number of steps is the
cardinality of the selected coordinate set.

The final theorem `higher_arrangements_freiman_family` starts with
`delta*N^11` solutions of `HigherArrangementEquation f` and returns sets
`E_i` and a single family `R subset Q` such that

```
f_i is Freiman of order eight on E_i for every i in Fin 16,
card E_i >= c_16*N for every i,
all sixteen endpoints of every tuple in R lie in their respective E_i,
card R >= c_16*N^11.
```

Each `E_i` also lies in the `i`-th endpoint image of the original family.
Thus the density assertion is about one simultaneous subfamily, with
all sixteen restrictions in force.

**Remaining work.** These are Freiman sets, not yet the common coset
progressions in the full higher-arrangement structure theorem. Pair-map
alignment, actual higher-arrangement frequency escape and enlargement,
simultaneous selection, anchor coherence, and the final bilinear variety
structure remain open. In particular, a sum of escaping frequencies
must retain the multiplicities of repeated generators. The quadruple
containment theorem alone does not establish the higher containments.
No numbered catalogue entry or final source-theorem bound is claimed
here. No new upstream port or licensing change was necessary.

**Verification.** The all-coordinate extraction closure checks 233
modules. All fifteen new named theorems pass individual axiom checks.
After merging the incoming explicit variety-decomposition chain, the
full audit checks 7,669 public Gowers theorems in 5,244 modules
(5,242 facade modules, including 4,152 OAI modules), using only
`propext`, `Classical.choice`, and `Quot.sound`. The incoming assembly
and count bounds compile with their actual dependencies. The numbered
ledger remains byte-for-byte unchanged at 115 companions and five open
entries. The selected-port scope remains 4,134 upstream and 17
compatibility modules, with reciprocal-only dependencies excluded.


### J.123. Eight progression maps on one higher-arrangement family

The sixteen-coordinate Freiman extraction from J.122 now feeds a
simultaneous representation of all eight pair differences by maps on
translated proper progressions. Every restriction preserves a quantified
portion of the original eleven-parameter family. The resulting eight
maps also satisfy the original arrangement equation on that family.

**Cover retention for indexed configurations.**
`indexed_common_graph_cover_retained_fibre` extends the earlier
quadruple-specific cover argument to any finite indexed family `Q`,
with endpoint maps `x,y`. Suppose a translated overlap of the two graphs
has density at least `mu`, and suppose `Q` has mass at least `mass > 0`.
The Freiman graph-cover argument supplies anchor sets `J,K` with
`card J * card K * mu^2 <= 1`. Assign each original configuration an
anchor pair and retain a large fibre of that assignment. At least
`mu^2*mass` original configurations survive. Their paired differences
all have one translated fourfold graph representation. In particular,
repeated endpoint pairs in `Q` are counted with their original index
multiplicity throughout this argument.

**A dense overlap from an offset equation.** For the indexed equation

```
f(x+a(i)) - g(x) = v(i),
card Q >= delta*M*N^2,
card {i : a(i)=z} <= M,
```

J.121 supplies at least `delta^2*N^3` mixed collision quadruples. The
existing graph-overlap theorem therefore gives a set `S subset B` with
`card S >= delta^2*N` on which a translate of `f` agrees with `g` up to
a constant. The original family `Q` remains available. This is proved
as `offset_equation_dense_overlap`, including both endpoint-domain
hypotheses.

**A common difference map and its proper progression.** Write

```
kappa = delta^2,
mu(kappa) = commonDifferenceClusterDensity kappa,
eta(kappa) = commonDifferenceProgressionDensity kappa.
```

Assume `f` is Freiman of order two on its endpoint set and `g` is
Freiman of order eight on its endpoint set. Localize the dense overlap
to a Bohr cluster and apply the indexed cover retention there. This
retains at least `mu(kappa)^2*delta*M*N^2` configurations whose offsets
are represented by one translated normalized Freiman map on a full Bohr
neighborhood. The offsets lie in its half-radius part, so the earlier
indexed progression localization applies.

`offset_equation_common_progression_map` consequently returns a proper
centered progression `P`, a translation `b`, an additive constant `c`,
and a normalized map `psi`, with

```
rank P <= commonDifferenceRank (delta^2) + 1,
card P >= eta(delta^2)*N,
f(x+a(i))-g(x) = c+psi(a(i)-b)
```

on a retained original family of size at least `G(delta)*M*N^2`, where

```
G(delta) = eta(delta^2)*mu(delta^2)^2*delta
         = offsetDifferenceProgressionRetention delta.
```

`G(delta)` is positive when `delta` is positive and is independent of
`M,N`. The packaged theorem `offset_equation_pair_frequency_map` returns
an actual `PairFrequencyMap` controlled at `delta^2`; its map is
`theta(t)=c+psi(t-b)` on the translated progression. The translation and
additive constant are both retained. Properness is asserted for `P`,
without an unproved properness claim for its dilates.

**All eight pairs.** Specialize to the higher-arrangement parameters
with `M=N^9`. The first pair's offset is the first shift, and its residual
is already provided by the arrangement equation. Even-coordinate
symmetries then move any of the eight pairs into this position while
preserving the order of its two endpoints and the exact cardinality of
the configuration family.

The definitions `higherArrangementPairLeft`, `higherArrangementPairRight`,
and `higherArrangementPairDifference` record this indexing. Additional
lemmas prove that the first four shifts are additive and that the right
four shifts equal the corresponding left shifts.

For iteration, define

```
b_0 = epsilon,
b_(n+1) = G(b_n).
```

`higher_arrangements_retain_pair_maps` treats any finite subset of pair
positions. Every stage only restricts the previously retained family,
so earlier map identities and domain memberships remain valid. A map
selected at stage `n` is controlled at `b_n^2`; this stage is recorded
explicitly instead of assuming an unproved monotonicity of the control
functions. After eight stages, every selected map has such a control
with `n < 8`, and at least `b_8*N^11` original configurations remain.

**Combined theorem.** `higher_arrangements_common_pair_family` first
uses all sixteen coordinate extractions, with
`epsilon = higherArrangementDensity delta 16`, and then performs all
eight pair alignments. It returns the sixteen Freiman sets, the eight
controlled progression maps, and one subfamily `R subset Q` of size at
least `higherArrangementPairDensity epsilon 8 * N^11`. Each coordinate
set retains its density bound `epsilon*N`; every tuple in `R` has all
sixteen endpoints in these sets and all eight shifts in their respective
map domains. Each map value equals the original endpoint-map difference.
The theorem also records `HigherArrangementPairMapEquation`: the sum of
the four left map values equals the sum of the four right map values.

**Remaining work.** This is an eight-map difference representation on
one common family. It is not yet the higher-arrangement frequency-escape
or enlargement theorem. Those steps must preserve repeated-generator
multiplicities when passing from a sum of frequencies to an escaping
component. Simultaneous selection, coherent anchor choices, and the
final bilinear variety structure remain open, as do the unresolved
numerical absorption estimates. No numbered catalogue entry or final
source-theorem bound is claimed here. No new upstream port or licensing
change was necessary.

**Verification.** The complete common-pair-family closure checks 305
modules. All seventeen new named theorems pass individual axiom checks.
After integrating the incoming logarithmic-loss bound, the full audit
checks 7,700 public Gowers theorems in 5,254 modules
(5,252 facade modules, including 4,152 OAI modules), using only
`propext`, `Classical.choice`, and `Quot.sound`. The numbered ledger
remains byte-for-byte unchanged at 115 companions and five open entries.
The selected-port scope remains 4,134 upstream and 17 compatibility
modules, with reciprocal-only dependencies excluded.


### J.124 Actual higher-containment escape and independent-family growth

The higher-arrangement step now starts from failed Bohr containments,
rather than assuming escaping frequency maps as input. Twelve original
modules prove twenty-seven named theorems; no upstream port is added.

**Multiplicity in the escape argument.** Put
`R = bohrExtensionCutoff (8*d) r`. A failed containment for the selected
frequency union `D` gives a common frequency in the bounded spans of the
eight left and eight right column spectra. Under
`D.card * 4 * sigma <= 1/(4*pi)`, that frequency is outside the
coefficient-four span of `D`. Decomposing each eight-column union gives
four signed pair differences on each side with equal sums. The cutoff
of each individual column remains `R`. A finite-union sum lemma pays
for repeated generators: four summands in individual unit spans belong
to the coefficient-four span of their union, not necessarily its unit
span. Consequently at least one of the four left components escapes its
own selected unit span.

**Selection from actual failures.** Sixteen independently colored maps
retain at least the fraction `(2*R+1)^(-16*d)` of the original failed
arrangements, including arrangements with repeated endpoints. Applying
J.122 and J.123 to this family produces all eight controlled pair maps
on one retained family, preserving both the frequency equation and the
escaping left sum. Define

```
a = delta / (2*R+1)^(16*d),
b = higherArrangementDensity a 16,
h = higherArrangementPairDensity b 8.
```

Each selected map is controlled at
`(higherArrangementPairDensity b n)^2` for some `n < 8`. Pigeonholing the
four escaping left positions costs a factor of four. The new projection
lemma bounds the number of arrangement parameters over fixed pair
endpoints by `N^9`. Thus `higher_failed_containments_dense_pair_escape`
returns one actual controlled map and a pair set `E` of size at least
`(h/4)*N^2`, on every element of which its value lies outside the old
selected unit span. Its value belongs to the ambient pair span with
cutoff `2*R`; the doubling accommodates overlapping endpoint spectra.

**Rank increment and uniform radius.** For any ambient cutoff
`C >= 2*R`, `higher_failed_pair_containments_increase_rank` adjoins this
map value on `E`, preserves the old selected sets, dissociation, and
ambient membership, and increases the total selected cardinality by
exactly `E.card`. The total stays at most
`N^2 * spanGeneratorBound (2*d) C`. Allowing an arbitrary larger `C`
is necessary for combining this step with the quadruple increment.

Set `s = spanGeneratorBound (2*d) C` and
`sigma = 1/(128*pi*(s+1))`. Every independent selected pair set has at
most `s` frequencies, and the union for a higher arrangement has at
most `8*s`. The positive radius therefore pays the coefficient-four
phase budget uniformly throughout any valid growth process.

**Remaining work.** The simultaneous quadruple/higher selection process
still needs to be constructed using a shared ambient cutoff and radius.
Coherent anchors, gluing, and the resulting deep bilinear variety
structure remain open. The numerical variety route also still needs
its final instantiated bounds. This checkpoint does not discharge a
numbered catalogue entry or assert an improved final source bound.

**Verification.** The full higher-radius closure checks 317 modules.
All twenty-seven new named theorems pass individual axiom checks using
only `propext`, `Classical.choice`, and `Quot.sound`. The numbered ledger
is byte-for-byte unchanged at 115 companions and five open entries.
The port-scope check still reports 4,134 upstream and 17 compatibility
modules, with reciprocal-only dependencies excluded. The initial combined audit checks 7,748 public Gowers theorems in 5,266
modules (5,264 facade modules and 4,152 OAI modules), with the same axiom
boundary. The final synchronized results are recorded below.


**Incoming numerical bounds.** The merged `Proofs16VarietyScaleBounds`
proves the variety and spectrum family/density scale bounds in
`x = 2/(theta*gamma)`. `Proofs16ExplicitConstantBounds` bounds the named
recurrence/partition constants by `2^1700`, conditional on its explicit
per-degree Schmidt bounds. These two modules compile against the real
selected dependencies; the synchronized audit checks 7,777 public
Gowers theorems in 5,268 modules with the usual three-axiom boundary.
These estimates do not by themselves instantiate the final source
threshold or supply the missing deep variety structure.


**Final merged verification.** The incoming named relation-piece theorem
and `MultiplyLinearWith.variety_three_multiplyLinear` also compile
against the real selected dependencies. The latter converts the actual
piece controls under positivity of the width coefficient to parameter
`18*r/gamma + 64 + L`, where `L` is the maximum of the two logarithmic
losses. The final threshold comparison remains open. After both merges,
the complete audit checks 7,788 public Gowers theorems in 5,269 modules
(5,267 facade modules, including 4,152 OAI modules). Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The ledger and port-scope
checks pass unchanged. Consumer audit counts were updated; no source
port, adaptation notice, or license scope was changed.


### J.125 Simultaneous quadruple and higher-arrangement selection

The two concrete enlargement routes now terminate in one selection
state. Eight original modules prove sixteen named theorems. The result
records actual progression maps, selected finite indices, exact
frequency values and domain membership; it does not assume an abstract
improvement oracle.

**Shared parameters.** Put

```
C = max (pairSelectionCutoff d r) (2*bohrExtensionCutoff (8*d) r),
s = spanGeneratorBound (2*d) C,
sigma = higherPairSelectionRadius d C,
eta = min (pairSelectionGain delta d r) (higherEscapeDensity delta d r/4).
```

Both `sigma` and, for positive `delta`, `eta` are positive. The maximum
cutoff accommodates both actual escape theorems without requiring a
monotonicity lemma for `bohrExtensionCutoff`. The higher radius pays
both the eight-set, coefficient-four higher-arrangement budget and the
two-set quadruple budget throughout the iteration.

**One state and two steps.** `PairSelectionState.JointValid` requires
dissociated selected sets in the common ambient span, representation
of every selected frequency by a recorded map at its actual pair
difference, and total frequency cardinality at least
`maps.length * eta * N^2`. Each recorded map satisfies either the
quadruple control or one of the eight higher extraction-stage controls.
`extend_joint` preserves these invariants when given a concrete map
escaping on at least `eta*N^2` pairs. The two improvement theorems supply
exactly this input from their respective failed-containment families.
They prepend one map and retain all old selected frequencies.

**Termination with both error bounds.** The rank budget implies
`maps.length * eta <= s`. If there were no state with both failure sets
small, every valid state would admit at least one of the two genuine
improvements. Induction would then give valid states of arbitrarily
large length, contradicting this positive-gain budget. Thus
`exists_joint_frequency_selection` returns a state with fewer than
`delta*N^3` quadruple failures and fewer than `delta*N^11`
higher-arrangement failures at the same radius. Its count variant
bounds the length by `floor(s/eta)`.

`joint_frequency_selection` exposes this as a finite family
`g : Fin m -> PairFrequencyMap N` and actual index sets `I(x,y)`.
Every index set has at most `s` elements; its image of map values has
exactly the same cardinality and is dissociated in the common ambient
span. All selected indices satisfy the map-domain requirement. The
same frequency family meets both containment error bounds, and
`m*eta <= s`. The quadruple input family must be additive; the higher
parameterization already enforces its additive shift relation.

**Uniform map bounds.** `jointControlParameter` lists the nine possible
controls: one quadruple control and eight higher-stage controls.
`jointMapRank` is the finite maximum of their progression rank bounds;
`jointMapDensity` is the finite minimum of their positive progression
densities. The latter is positive. Every `JointControlled` map has a
proper progression of rank at most `jointMapRank`, cardinality at least
`jointMapDensity*N`, and is Freiman of order two on its translated
domain. This does not assume monotonicity of the control functions.

**Remaining work.** This completes the simultaneous selection step.
Popular shifts, coherent good anchors and Bohr gluing are still needed
before the selected family yields the required bilinear variety
structure. The deep structure hypothesis is still open, so no
numbered catalogue entry or final bound is discharged here. All eight
modules are original consumers of existing dependencies; no port or
license scope is added.

**Verification.** The complete uniform-control closure checks 329
modules. All sixteen named theorems pass individual axiom checks. Final
combined audit and synchronization results follow below.


**Incoming conditional dimension-three budget.** The merged variety
budget module now proves `section16VarietyThreeLoss_le`: if
`D <= 2^64` and the four named constants are at most `2^1700`, its
width coefficient is positive and its logarithmic loss is at most
`x^(64*2^256)`, where `x = 2/(theta*gamma)`. Together with
`MilicevicDeepVarietyStructure D`, this constructs
`Section16BudgetedPieceAt 3` and the corresponding conditional
`Theorem162At 3` and `Corollary1611At 3`. These statements compile
against the actual selected dependencies. Their unproved deep-structure
and constant hypotheses remain explicit; they are not closed catalogue
companions.

**Final merged verification.** The complete audit checks 7,823 public
Gowers theorems in 5,277 modules (5,275 facade modules, including 4,152
OAI modules), using only `propext`, `Classical.choice`, and `Quot.sound`.
The regenerated ledger adds precisely the two new conditional theorem
records; it still reports 115 companions and five open entries. The
port-scope check passes with 4,134 upstream and 17 compatibility
modules. No upstream source or license scope was changed.


### J.126 Selected Bohr gluing and shift-anchor coherence

Eight original modules prove seventeen named theorems connecting the
simultaneous frequency selection to actual local maps on the selected
Bohr domains. Compatibility of the chosen anchors and the original
column identities remain explicit hypotheses. In particular, these
lemmas do not assume global compatibility of all column quadruples.

**Local extension.** `selected_bohr_sum_extension` restricts the
existing, explicitly defined `bohrSumExtension` to any selected Bohr
set contained in the sum of the two quarter-radius neighborhoods.
The result is Freiman-linear there, is zero at zero, and agrees with
both original maps on their respective quarter-radius neighborhoods.
The original maps need to be normalized and Freiman-linear on their
full-radius domains, and to agree on the full intersection.

`columnDifferenceMap_freiman_of_local` obtains the required local
linearity from the two individual columns. `ColumnPairCompatible`
records agreement for just the chosen pair of differences, and
`column_pair_selected_extension` supplies the corresponding actual
`columnPairExtension`. No global bihomomorphism is used.

**Common representations preserve relations.** Suppose a set is
contained in the sum of the common quarter-radius domains of two
finite families. Each point then has one representation `u+v` valid
for every member of both families. The value formula for each glued
map is consequently `f_i(u)+g_i(v)`. Thus every fixed finite linear
relation which vanishes in each original family also vanishes in the
glued family (`bohr_sum_extensions_preserve_relation`). Its four-map
specialization transfers `f_0+f_1=f_2+f_3` and the corresponding
identity for `g` to the four extensions.

**The actual higher arrangement.** Three spectrum identities identify
the left and right sixteen-column unions with unions of the four
anchor-pair spectra and identify the selected union with the union of
the four selected anchor domains. `higher_anchor_extensions_coherent`
then applies the common-representation theorem to the actual higher
containment. Both original eight-column identities are required on
their respective common quarter-radius domains. The resulting identity
uses signs `+,+,-,-`, as appropriate for the additive shift relation;
this differs from the all-positive four-term sum used in the earlier
frequency escape argument.

`joint_good_quadruple_extension` and `joint_good_higher_coherence`
obtain their containments from membership in the complements of the
actual joint-selection failure sets. Thus the gluing lemmas apply
directly to the family selected in J.125.

**One map for each shift.** Anchor functions `x(a), y(a)` define
`shiftAnchorPair x a = (x(a)+a,x(a))`, and `shiftAnchorMap` glues the two
associated column differences. `shiftAnchorArrangement` places an
additive quadruple of shifts into the eleven-parameter arrangement.
Its left and right endpoint pairs are exactly the corresponding
shift anchors, and its selected frequency union is exactly the union
of their four domains. The definitions use the same anchors whenever
a shift repeats; no independence of repeated shifts is assumed.

`shiftAnchorMap_local` gives normalized local Freiman maps and both
quarter-domain restrictions for every good compatible anchor pair.
`shiftAnchorMaps_coherent` gives their additive quadruple identity on
the intersection of the four selected Bohr domains whenever the
corresponding higher arrangement is good and its two original
column identities hold.

**Remaining work.** The quantitative choice of anchor functions with
many good arrangements is still open. It must combine popular shifts,
high-degree compatible pairs, the joint containment error bounds, and
the original column identities. Repeated-shift dependence must be
handled in that averaging argument. These gluing results do not
construct the missing deep bilinear variety structure or close any
numbered catalogue entry. No upstream port or license scope is added.

**Verification.** The complete shift-anchor-map closure checks 337
modules. All seventeen new named theorems pass individual axiom checks.
Final merged audit results are recorded below.


**Incoming constant discharge and final verification.** The merged
`Proofs16VarietyTheoremThree` proves the per-degree Schmidt bounds from
the actual OAI recurrence definitions and the verified Weyl bounds.
It discharges the four named constant assumptions, so
`theorem_16_2_at_three_of_deep` and
`corollary_16_11_at_three_of_deep` require only deep variety structure
with `D <= 2^64`. The generalized loss lemma also accepts bounds on
the two Milićević values directly, retaining the original fixed-`D`
result as a corollary. All these sources pass the full kernel check.

The merged audit checks 7,867 public Gowers theorems in 5,286 modules
(5,284 facade modules, including 4,152 OAI modules), using only
`propext`, `Classical.choice`, and `Quot.sound`. The regenerated ledger
records the two new conditional consequences and refreshed source
locations; its 115 companions and five open entries are unchanged.
The port-scope check still reports 4,134 upstream and 17 compatibility
modules, with reciprocal-only dependencies excluded. No upstream
source or license scope was changed.


### J.127. Quantitative selection of coherent global anchors

Seven modules prove seventeen named results selecting one pair of global
anchor functions from a dense family of higher arrangements. The final
result `exists_dense_coherent_anchor_maps` produces at least
`(kappa/2)*N^3` additive quadruples of distinct shifts when the good family
has at least `kappa*N^11` members and `8 <= kappa*N`. Their actual selected
anchor maps are normalized local Freiman maps and satisfy the additive
quadruple identity on the intersection of their four selected Bohr domains.

**Exact restriction counting.** An injective coordinate restriction has
`|V|^(|I|-|J|)` extensions, by an explicit equivalence with functions on
the complementary coordinates. For four distinct shifts and pair-valued
anchors this gives the exact balancing identity
`card(realizations)*N^8 = card(all global anchor functions)`.
A finite incidence double count then selects a global function realizing
at least the average number of arrangements. Each realized arrangement
is reconstructed from its four shifts and the chosen anchors, so mapping
to shift quadruples preserves cardinality. No independent sampling of
repeated occurrences of the same shift is assumed.

**Repeated shifts.** Among shifts `a,b,c,a+b-c`, every repetition belongs
to one of four families: `a=b`, `a=c`, `b=c`, or `a=2*c-b`. Each family
has at most `N^10` higher arrangements, using explicit ten-coordinate
injective encodings. Thus at most `4*N^10` arrangements are removed.
The hypothesis `8 <= kappa*N` makes this at most half the original
mass. The four-family estimate improves the direct six-pair union bound
and works for every nonzero modulus, without dividing by two.

**Coherence.** `GoodHigherAnchorArrangement` records the four pair
compatibilities, their selected-domain containments, the higher
containment, and the two original column quadruple identities.
`shift_anchor_maps_of_good_arrangement` transfers these to the actual
shift-anchor maps by the previously checked gluing results. Quantitative
anchor selection applies this to a dense family satisfying that predicate.

**Remaining work.** The density of such a good family still has to be
proved from popular shifts, compatible-pair degrees, sparse containment
failures, and the original column identities. Further common-domain and
structural steps are also required. This is not a proof of the missing
deep variety theorem or a closure of a numbered catalogue entry.
No additional upstream code or license scope is introduced.

**Verification.** The production closure checks 344 modules. Individual
axiom checks and the merged facade audit are recorded below after completion.


**Final merged verification.** All seventeen new named theorems pass
individual axiom checks. The complete merged audit checks 7,899 public
Gowers theorems across 5,294 modules (5,292 facade modules, including
4,152 OAI modules), with only `propext`, `Classical.choice`, and
`Quot.sound`. The catalogue remains at 115 companions and five open
entries; regeneration changes only two source locations. These counts
do not remove the documented statement-fidelity qualifications.
The port-scope check still reports 4,134 upstream and 17 compatibility
modules, excluding reciprocal-only dependencies.

The merged two-scale variety refactor also passes against the actual
OAI closure: family and spectrum controls now use separate indices
`D` and `D₂`, including the width coefficient, logarithmic loss, and
piece parameter. The generalized loss theorem accepts separate bounds
at the two densities. The existing fixed-index dimension-three results
are recovered at `D₂ = D`. This enables separate future choices at the
two densities; it does not itself supply deep structure or discharge
the remaining quantitative bridge.


**Concurrent local-cover integration.** A fast-forward push race brought
in `Proofs16VarietyLocalPieces`. It constructs the dimension-three relation
pieces from two local `VarietyClassCoverAt` inputs and supplies
`section16_budgeted_piece_three_of_local` when their two numerical values
fit the budget. The new module and merged audit pass against the actual
sources: 7,909 public Gowers theorems, 5,295 combined modules and 5,293
facade modules. The axiom boundary and numbered ledger are unchanged.
The two local cover inputs remain hypotheses; no deep-structure closure
is asserted by this integration.


**Eventual polynomial-bound bridge verified.** A second concurrent merge
adds the least-index bound comparison and assembles the two local covers
from `MilicevicDeepEventuallyPrime Bnd`. The dimension-three consequences
now accept `Bnd c <= (4/c)^K` with `K <= 2^64`; the named numerical
constants are discharged. This resolves the two-density budget mismatch
in J.5b while retaining the deep-structure and polynomial-bound hypotheses.
The actual merged closure passes: 7,920 public Gowers theorems in 5,296
combined modules (5,294 facade modules), with the same three allowed
axioms. The ledger adds four conditional consequences and updates source
locations; its 115 companions and five open entries remain unchanged.


### J.128. Dense supported arrangements and sparse-failure removal

Eleven modules prove thirty-three named results constructing the dense good
family required in J.127. The final `exists_supported_coherent_anchor_maps`
starts with a column set `W` of density at least `alpha`, normalized local
Freiman column maps with spectra of size at most `d`, and quantitative
bounds on the two kinds of original column failures. It performs joint
frequency selection and chooses global anchors with at least
`(alpha^16 - 4*eps - 2*eta - 5*delta)/2 * N^3` coherent additive
quadruples of distinct shifts, provided
`8 <= (alpha^16 - 4*eps - 2*eta - 5*delta)*N`.
Here `eps*N^3` bounds incompatible supported anchor quadruples,
`eta*N^7` bounds unrespected supported eight-column tuples, and
`delta > 0` is the requested tolerance of each joint-selection failure
set. The modulus is prime, and `0 < r < 4`, as required by the existing
joint-selection theorem. Every resulting arrangement keeps all sixteen
columns in `W`.

**Projection fibres.** A matched anchor quadruple at one of the four
positions fixes the shared shift and both anchor bases, leaving eight
free coordinates. An explicit injective encoding proves the `N^8`
fibre bound; coordinate symmetries transfer it to every position.
Fixing all eight columns on one side fixes seven parameters and leaves
only the four bases on the other side. Another encoding gives `N^4`
fibres for both sides. These are bounds for arbitrary input families,
with no uniformity hypothesis.

**Actual failure removal.** `higherArrangementBadData` is a finite union
of the four anchor failure preimages, the two column failure preimages,
and the higher failure set. Its cardinality is at most
`4*|E|*N^8 + (|VL|+|VR|)*N^4 + |B|`. The complementary family has the
corresponding density lower bound. `columnTupleFailures` tests the
original four-difference identity on the actual common quarter-radius
Bohr domain, and `incompatibleAnchorQuadruples` tests the compatibility
needed for gluing.

`jointGoodHigherArrangements` removes these original failures together
with the actual `jointQuadrupleFailures` and `jointHigherFailures`.
Every retained member satisfies `GoodHigherAnchorArrangement`. A family
of density `kappa` retains density at least
`kappa - 4*eps - 2*eta - 5*delta`. The factor five comprises the four
individual containment preimages and the one higher containment failure.
`exists_joint_coherent_anchor_maps` combines this with actual joint
selection and anchor averaging, preserving input-family membership in
addition to normalized local linearity and common-domain coherence.

**The supported family is dense.** No progression overlap estimate is
needed for this counting step. The generic
`card_four_le_mapped_additive_quadruples` applies the existing finite
key-collision Cauchy--Schwarz bound to pairs of indexed objects; it does
not collapse objects with equal images. Applying the same argument to
differences of pairs in `W` gives at least `|W|^4/N` supported anchor
quadruples. Applying the mapped-quadruple bound to their shifts gives
at least `|W|^16/N^5` higher arrangements. An explicit reconstruction
recovers all four anchor quadruples, proving injectivity and preserving
all sixteen column values. Thus
`|W|^16 <= |supportedHigherArrangements W|*N^5`, and density `alpha`
of `W` gives density `alpha^16` of the higher family. Its projections
lie in the supported additive quadruple and eight-column families,
so the sparse-failure removal theorem applies directly.

**Remaining work.** The original compatibility and eight-column failure
bounds are still hypotheses and must be supplied by the preceding
column construction with suitable parameters. The next steps also need
sufficient agreement with many original columns, a fixed small family
of frequency maps with usable common progression domains, and the
subsequent structural argument. The finite averaging now constructs
its dense good family, but does not supply those further properties
or the missing deep variety theorem. No numbered entry or final
Gowers-bound improvement is claimed closed. No upstream port or license
scope is added.

**Verification.** The production closure checks 355 modules. Individual
axiom checks and final merged audit totals are recorded below.


**Final verification.** All thirty-three new named results pass individual
axiom checks. The merged full audit passes 7,974 public Gowers theorems
in 5,307 combined modules (5,305 facade modules, including 4,152 OAI
modules), with only `propext`, `Classical.choice`, and `Quot.sound`.
The regenerated source ledger is unchanged: 115 companions and five
open entries, with the documented statement-fidelity qualifications.
The port-scope check remains at 4,134 upstream and 17 compatibility
modules, excluding reciprocal-only dependencies. The merged remote
changes affect only the independent topology development.


### J.129. Global coherent anchors and a fixed small index set

Eleven modules prove twenty-six named results connecting the even-column
core to the coherent-anchor construction, then retaining many whole
quadruples under one small index set. The global construction starts with
the original dense Freiman bihomomorphism and retains its column witness
system; the compatibility, eight-column failure, and arrangement-density
assumptions from J.128 are now discharged through that core.

**Absorb the common spectrum.** On the retained core `P`,
`coreColumnSpectrum` is `Gamma union T(x)` and `coreColumnMap` is `L(x)`.
Outside `P` they are the empty spectrum and zero map. These extensions
have a global spectrum-cardinality bound and normalized local Freiman
linearity at the core radius. The common spectrum is therefore present
on every supported column domain used below.

The length-four even-core identity, applied in order
`[q0,q1,q3,q2]`, proves compatibility of the two matched column
differences. The length-eight identity, applied in order
`[v0,v1,v2,v3,v5,v4,v7,v6]`, proves the required four-difference
quadruple relation on the common quarter-radius domain. Consequently
both `incompatibleAnchorQuadruples` and `columnTupleFailures` are empty
for the supported families on `P`.

**Global construction.** `coherent_anchor_system_of_even_core` chooses
joint-selection tolerance `beta^16/10` for a core of density `beta`.
The J.128 error budget and anchor averaging give density `beta^16/4`
of coherent distinct-shift quadruples once `16 <= beta^16*N`.
`HasCoherentAnchorSystem` records the actual selected state, its map-count
budget, both global anchor functions, the quadruple family, and the local
linearity and coherence identities. Every realized arrangement remains
supported on `P`.

`global_coherent_column_anchors` supplies this system from
`global_even_zero_column_core` at maximum half-length four. Its parameters
are explicit functions of the original density `alpha`: core density
`globalEvenColumnZeroDensity alpha 4`, spectrum rank bound equal to the
core common rank plus the original column spectrum cap, core radius, and
modulus threshold equal to the maximum of the existing core threshold
and `ceil(16/beta^16)`. The original witness system, full-radius column
linearity, witness density, and core identities are retained in the
conclusion. No additional original-column failure oracle is assumed.

**Retain whole quadruples with common indices.** For a set of at most
`K` indices among `m`, `boundedIndexCode` sorts its elements and pads to
length `K` with `none`. Equality of codes implies equality of the sets.
A finite double count selects a nonempty subfamily with one common set,
losing at most `(m+1)^K`. Empty index sets and `m < K` require no special
exception. This counts bounded sets rather than all `2^m` subsets.

`joint_anchor_common_indices` chooses exact pair-frequency index sets
from the actual joint state. The union for a quadruple has size at most
`8*jointSelectionRank d r`. It retains a subfamily of the original
quadruples with one such common union `J`; the actual selected frequencies
at all four shifts lie in the image of `J`. Thus it preserves quadruple
relations, not merely the number of individually retained shifts.

`HasCoherentAnchorSystem.common_indices` restricts the anchor maps to
Bohr domains defined by this same index set. These domains are subsets
of the prior selected domains, so local linearity, normalization, and
all retained coherence identities persist. The loss is at most
`(m+1)^(8*rank)`. The proved map-count budget further yields the positive,
modulus-independent density
`kappa/(rank/jointSelectionGain delta d r + 1)^(8*rank)`, implemented as
`uniformAnchorIndexDensity` and used in `common_indices_uniform`.

**Quantitative and structural limits.** The even-core density preserves
its existing elimination formula, with test density
`1/(4*refinementCells(r/2)^(g+d))` and round count
`ceil(log(M+1)/testDensity)`. No bound establishing that the resulting
composite parameters satisfy the polynomial deep-structure budget has
been proved here. This global structural construction must not be
reported as a final Gowers-bound improvement.

The selected frequency maps are Freiman maps on their own translated
progressions. Membership in an original selected pair-index set gives
domain membership for that shift; membership in the larger common `J`
does not give membership in every map's domain at every retained shift.
The Bohr restriction above is valid because the maps have total value
functions, but further progression-domain work is required before using
joint Freiman linearity or algebraic regularity for that fixed family.
Agreement with sufficiently many original columns and the remaining
deep-structure argument are also still required. No numbered catalogue
entry or upstream port scope is changed.

**Verification.** The production closure checks 400 modules. Individual
axiom checks and the final merged audit are recorded below.


**Final verification.** All twenty-six new named theorems pass individual
axiom checks. The complete merged audit checks 8,033 public Gowers
theorems in 5,318 combined modules (5,316 facade modules, including
4,152 OAI modules), with only `propext`, `Classical.choice`, and
`Quot.sound`. The regenerated numbered ledger is unchanged at 115
companions and five open entries, with the existing statement-fidelity
qualifications. The selected dependency scope remains 4,134 upstream
and 17 compatibility modules, excluding reciprocal-only dependencies.
The fetched and merged remote delta changes only the independent
topology development; no upstream source or license scope is added.

## J.130 Popular shifts and dense agreement of coherent anchors (2026-10-09)

**Popularity before selection.** `columnShiftBases P a` consists of bases
`z` with both `z` and `z+a` in the exact core. For a fixed shift, a
supported anchor quadruple is determined by its two bases. Consequently
`unpopular_anchor_quadruples_card_le` bounds the number of quadruples
whose shift has fewer than `t*N` bases by `t^2*N^3`. This inequality even
holds for negative thresholds (the exceptional family is then empty).
The higher-arrangement projection bounds remove at most `4*t^2*N^11`
arrangements. Choosing `t = beta^8/4` leaves at least three quarters of
the original `beta^16*N^11` mass. Joint selection at tolerance
`beta^16/20` spends another quarter; anchor averaging therefore retains
the previous `beta^16*N^3/4` quadruple-density guarantee. Every retained
shift now has at least `beta^8*N/4` supported bases. The modulus condition
`16 ≤ beta^16*N` is unchanged.

**Preserve the actual family.** `HasCoherentAnchorSystemOn` records
membership in an arbitrary input arrangement family. The earlier
`HasCoherentAnchorSystem` is its supported-family specialization.
Both common-index restriction theorems now have generic versions that
preserve this membership, with the original statements retained as
wrappers. Thus popularity survives common-index selection. The global
popular-anchor theorem obtains all input core data from the original
dense bihomomorphism; it introduces no new compatibility assumption.

**Agreement and rank.** Compatibility on the exact even core and the
quarter-domain extension formula prove `core_shift_anchor_agrees`:
the anchor map equals `L(z+a)-L(z)` on the common quarter-radius Bohr
set, for every supported base `z`. Intersecting with any selected Bohr
domain `B(D;sigma)` retains that equality. The explicit domain of pairs
`(z,w)` uses radius `min(sigma,r/4)` and at most `k+g+4*d` frequencies
when `|D| ≤ k`, `|Gamma| ≤ g`, and each column spectrum has size at most
`d`. The common spectrum is counted once, improving the direct union
bound `k+4*(g+d)`. For every positive integer `Q` satisfying
`1 ≤ min(sigma,r/4)*Q`, its cardinality obeys
`t*N^2 ≤ Q^(k+g+4*d)*|domain|`.

This establishes dense agreement with the local column models. It does
not yet discharge the final deep-structure statement, the separate
progression-domain requirement for the frequency maps, or the polynomial
budget for the composite even-core parameters. No numbered catalogue
entry or upstream port scope is changed.

**Initial verification.** The production target through the agreement
domain checks 408 modules. The final axiom and merged-closure verification
is recorded below after the common-index agreement interface is added.

**Common-index agreement interface.** `coreAnchorAgreementDensity` uses
`Q = ceil(1/min(sigma,r/4))`, eliminating the auxiliary cell integer.
It is positive for positive input density and radii. The theorem
`popular_common_indices_agree` retains the joint state and map budget,
common index set of size at most `8*jointSelectionRank (g+d) r`, and
`uniformAnchorIndexDensity` of whole coherent quadruples. At each shift
it also retains popularity and an actual agreement domain of density
`coreAnchorAgreementDensity t (8*rank) g d r sigma`, with both column
endpoints in the core and the evaluation point in the selected Bohr set.
This domain and all equality assertions are constructed from the core;
none is an additional input hypothesis.

**Final verification.** The production closure checks 410 modules. All
22 new named theorems pass individual axiom checks. The full audit checks
8,070 public Gowers theorems in 5,327 combined modules (5,325 facade
modules, including 4,152 OAI modules), with only `propext`,
`Classical.choice`, and `Quot.sound`. The regenerated numbered ledger is
byte-for-byte unchanged at 115 companions and five open entries, subject
to the existing statement-fidelity qualifications. Port scope remains
4,134 upstream modules and 17 compatibility modules. No upstream code
or license scope is added. The fetched `origin/main` was already an
ancestor of the working branch.

## J.131 Exact row indices and progression rectification (2026-10-09)

**Resolve domain membership position by position.** A common union of
frequency indices does not put every map's progression domain around
every retained shift. The new construction fixes the exact index set
separately at each of the four positions. `exists_common_bounded_index_pattern`
codes `ell` sets of size at most `K` using `(m+1)^(K*ell)` possibilities.
For the four anchor positions, `K = 2*jointSelectionRank d r`, so the
loss remains `(m+1)^(8*rank)`, exactly the exponent used by the common-union
construction. Empty sets and fewer available indices than the size cap
are allowed.

`joint_anchor_row_indices` retains a subfamily of the original quadruples
and four sets `J j`. Their images equal the original selected frequencies,
and every map in `J j` has the actual shift `a j` in its domain. Thus
`HasCoherentAnchorSystemOn.row_indices_uniform` preserves the original
Bohr domains without shrinking them. It also preserves the arbitrary
arrangement family, additive distinct quadruples, normalized local maps,
coherence, the joint map-count budget, and the same positive uniform
density.

**Dense domains for the frequency maps.** Fixing one coordinate of an
additive quadruple leaves at most two free coordinates. The explicit
injection proves `|R| ≤ |anchorRowSupport R j|*N^2` at every position,
so quadruple density `kappa` gives row-support density at least `kappa`.
`joint_row_frequency_domains` proves every selected map is Freiman of
order two on the entire row support, with genuine membership in its
translated progression domain at every point. The final interface
`popular_coherent_anchor_rows` retains this together with popularity and
core-column agreement. Each row uses at most `2*rank` frequencies, so
its agreement-domain bound is now `2*rank+g+4*d`.

These are four possibly different dense supports. They have not been
identified with one common progression. That subsequent structural step
and the final polynomial budget remain required; no numbered catalogue
entry is closed by this interface alone.

**Initial verification.** The six new modules through the row interface
check in a 417-module production closure. All eight named theorems pass
individual axiom checks with only the three permitted axioms.

**Rectify the actual progression domains.** For a centered progression
coordinate of radius `r_i`, use cells of integer width `floor(r_i/8)+1`.
There are at most sixteen labels per coordinate. Two parameters with the
same label differ in that coordinate by at most `floor(r_i/8)`. Thus the
difference between sums of eight matched parameters has absolute value
at most `r_i`. Properness of the original progression makes any vanishing
ambient eight-term relation an exact relation in every integer coordinate.
`progression_cell_relation_lifts` proves this, including radius-zero and
rank-zero cases.

`translated_progression_coordinate_affine` applies the existing coordinate
affinity theorem to an order-two Freiman map on a translated progression.
The lifted coordinate relations then imply order-eight preservation on
every cell. The finite-sum-to-multiset bridge explicitly retains repeated
elements. `PairFrequencyMap.eightCover` covers the actual translated
map domain by at most `16^progression.rank` cells, each supporting the
original map as a Freiman homomorphism of order eight. The cells depend
on the progression alone. No new upstream module is ported.

**Retain whole quadruples through all covers.** `exists_dense_cover_pattern`
selects one cell from each finite cover and retains a subfamily of the
input configurations, with loss at most `M^|I|` for `|I|` covers of size
at most `M`. Apply it only to the actual row-index pairs `(j,i)` with
`i ∈ J j`. There are at most `8*jointSelectionRank d r` such pairs,
and every selected progression has rank at most `jointMapRank delta d r`.
Consequently `joint_rows_eight_density` retains quadruple density

`rowEightDensity delta kappa d r = kappa / 16^(8*rank*mapRank)`.

Each resulting row support has at least that density, and every selected
frequency map is order eight on the entire corresponding row support.
The retained family is a subset of the input family, preserving all
previous coherence, popularity, and column-agreement assertions.

**One Bohr difference domain for all four rows.** The spectrum in the
constant-radius Bogolyubov--Freiman theorem depends only on its dense
input set, not on the map. `dense_eight_shared_bohr_spectrum` makes this
uniformity explicit: all order-eight maps on a set of density at least
`eta` use one spectrum of size at most `16*eta^(-2)` and radius
`1/(8*pi)`. Taking the union of the four row spectra costs at most
`64*eta^(-2)`, independent of the number of selected frequency maps.
`four_row_common_frequency_bohr` provides normalized Freiman difference
extensions for all these maps on this same Bohr set, with agreement for
every pair of original row points whose difference lies in it.

The final `joint_rows_common_bohr` connects this result to the actual
joint selection state and retains the refined quadruple family. This
replaces the missing domain-membership inference by a proved finite
refinement and genuine common difference extensions. Further clustering
and translation are still needed to express the original row frequencies
affinely on a common progression, and the later regularity/BSG and final
quantitative steps remain open. The positive density and spectrum bounds
here are explicit; they are not yet a certificate for the final Gowers
threshold.

**Production verification.** All sixteen new modules check in a
428-module production closure. The full facade, individual axiom checks,
merged state, and unchanged catalogue are verified below.

**Final verification.** All 28 new named theorems pass individual axiom
checks. The complete merged audit checks 8,129 public Gowers theorems in
5,343 combined modules (5,341 facade modules, including 4,152 OAI modules),
with only `propext`, `Classical.choice`, and `Quot.sound`. The regenerated
numbered ledger is byte-for-byte unchanged at 115 companions and five
open entries, with the existing statement-fidelity qualifications. The
selected dependency scope remains 4,134 upstream and 17 compatibility
modules. The reviewed incoming changes concern only the independent
topology development; no Gowers dependency or licensing scope is added.


### J.132. Additive translation into one proper progression

**Whole-quadruple averaging.** For an additive family `Q` and any finite
set `P`, `exists_additive_translation_count` constructs an additive
translation `t` such that

`|Q| * |P|^4 <= N^4 * |{a in Q : all j, a j - t j in P}|`.

The proof counts pairs of additive quadruples and uses their first three
coordinate differences as the translation code. The fourth difference
is forced by additivity. The energy lower bound for `P` then supplies
the fourth-power density loss. Recentring is injective on configurations,
so all original quadruple properties can be pulled back without loss.
The new centred entries need not be distinct; distinctness is retained
for their original translates.

**Actual proper progression and affine frequencies.** Apply this averaging
to the proper progression inside the common frequency Bohr set at quarter
radius. Its rank is at most `ceil(64*eta^(-2))+1`, where `eta` is the
previous row-eight density. `joint_rows_on_proper_progression` retains
quadruple density `eta * bohrProgressionDensity(rank,1/(8*pi))^4` and
expresses every original row frequency as `c j i + psi j i (b j)`.
Each `psi j i` is normalized and Freiman of order two on the entire same
proper progression. The argument uses translation averaging, not an
assumption that an independently chosen vertex cluster preserves energy.

**Coherence on the new Bohr domains.** The fixed constants have a union
of size at most eight times the selection rank. One row adds at most two
times that rank in varying frequencies. Taking half the original radius
makes these actual Bohr domains subsets of the selected original domains.
`HasCoherentAnchorSystemOn.progression_rows` therefore retains all local
Freiman maps, their normalization, the four-map coherence identity,
original distinctness, and membership in the supplied arrangement family.
`HasCoherentProgressionRows` records this full quantitative conclusion.

All nine modules check in a 439-module production closure; the eighteen
new named theorems pass individual axiom checks with only `propext`,
`Classical.choice`, and `Quot.sound`. No upstream source is added. The
four row families still need the later regularity/BSG argument and a final
quantitative budget. This does not close a numbered catalogue entry or
improve the final Gowers threshold.


**Global input and dense column agreement.**
`global_popular_coherent_progression_rows` derives the progression-row
conclusion from the original dense bihomomorphism, retaining the original
column witness system, its witness density and spectrum bounds, and the
even-core relations. The modulus assumption is the already explicit
`globalCoherentAnchorModulusBound`; no additional geometric assumption is
introduced.

`popular_affine_row_agreement` applies the core agreement construction
inside the new affine Bohr domains. A bound of `K` selected frequencies
per row costs at most `5*K` frequencies, including the fixed constants.
For the actual selected rows, this gives agreement density

`affineRowAgreementDensity t g d r = coreAnchorAgreementDensity t (10*selectionRank) g d r (selectionRadius/2)`.

It is positive whenever the popularity density and core radius are
positive. Every agreement point has both endpoints in the original core,
lies in the new affine row Bohr domain, and equates the anchor map with
the difference of the original column maps. Applied to each member of
the retained family, the translated tuple is additive because both the
translation and centred tuple are additive. These two additional modules
check in the 441-module production closure. All 22 new named theorems
pass individual axiom checks. The full merged facade audit follows.


**Final merged verification.** The full audit checks 8,165 public Gowers
theorems in 5,354 combined modules (5,352 facade modules, including 4,152
OAI modules), with only `propext`, `Classical.choice`, and `Quot.sound`.
All 22 new named theorems also pass their individual axiom checks. The
regenerated numbered ledger is byte-for-byte unchanged at 115 companions
and five open entries, retaining the documented statement-fidelity
qualifications. The selected upstream scope remains 4,134 modules plus
17 compatibility modules, with no new port or license requirement. The
reviewed incoming main changes affect only the independent topology report
and its measurements.


### J.133. One coherent family from the four progression rows

**A shared domain makes pointwise row selection possible.** After J.132,
every selected frequency extension is defined and Freiman on the entire
same proper progression. We may therefore use the union of all four
varying frequency lists at every point. Together with the fixed constants,
this spectrum has size at most sixteen times `jointSelectionRank d r`.
Its Bohr domain is contained in each of the four original affine row
domains at that point. `exists_unified_freiman_family` enumerates the
varying part by one fixed finite list of at most eight times that rank;
every member is normalized and Freiman on the whole progression.

**Discard collisions, then select one row per point.** An additive tuple
with a repeated entry lies in one of four two-parameter families. Thus
`additive_quadruples_repeated_card_le` bounds all such tuples by `4*N^2`,
without a characteristic restriction. If the original tuple density is
`eta` and `8 <= eta*N`, at least `eta*N^3/2` distinct tuples remain.
Each distinct tuple consistently prescribes four values of a pointwise
label function `color : ZMod N -> Fin 4`. Indexed selection averaging
retains at least a `4^(-4)` proportion satisfying `color (b j) = j`.
There is no loss from identifying requirements with the same support.

`coherent_four_rows_to_single` chooses the local map at `u` from row
`color u`. On the union-spectrum Bohr domain, it is normalized and Freiman.
At least `(eta/512)*N^3` original centred tuples remain coherent for this
single chosen family; their entries belong to a set of size at least
`(eta/512)*N` in the same progression. This proves the row-unification
step without an unproved Cauchy--Schwarz transfer of local identities.

**Actual anchors and their agreement are retained.**
`HasCoherentProgressionRows.single_system` gives the reusable
`IsSingleCoherentProgression` witness. It retains a realizing popular
original arrangement for every point, with original shift
`t (color u) + u`. It also retains the original arrangement for every
selected tuple. `IsSingleCoherentProgression.popular_agreement` proves
that every selected point has dense agreement with original core-column
differences inside its actual unified Bohr domain. The explicit density
is `coreAnchorAgreementDensity popularity (16*selectionRank) g d r
(selectionRadius/2)` and is positive for positive popularity and radius.
The maps may use different translation labels; a later restriction to
one label is still needed when a common source translation is required.

**Global construction.** `global_single_coherent_progression` starts
from the original dense bihomomorphism. The modulus bound is the maximum
of the prior global anchor threshold and `ceil(8/eta)`, where `eta` is
the previously proved coherent progression density. Its conclusion
retains the column witness system, all even-core relations, and an actual
single coherent progression system with pointwise core agreement.
All geometric, frequency, and density objects are constructed rather
than supplied as assumptions. The later regularity/BSG step and a final
polynomial quantitative certificate remain open.

All eight new modules check in the 449-module production closure. All
22 new named theorems pass individual axiom checks with only `propext`,
`Classical.choice`, and `Quot.sound`. No upstream source is ported and no
numbered catalogue entry is claimed closed. Full merged verification is
recorded below.


**Final verification.** The complete audit checks 8,207 public Gowers
theorems in 5,362 combined modules (5,360 facade modules, including 4,152
OAI modules), with only `propext`, `Classical.choice`, and `Quot.sound`.
All 22 new named theorems also pass individual axiom checks. The regenerated
numbered ledger remains byte-for-byte unchanged: 115 companion proofs and
five open entries, with the existing statement-fidelity qualifications.
The selected port scope is unchanged at 4,134 upstream and 17 compatibility
modules. The branch is synchronized with main before the audit; no incoming
changes alter the verification closure.


### J.134. Relation-rank refinement preserving coherent quadruples

**Retain the full frequency domain.** The progression-row and single-family
conclusions now retain the spectrum already constructed in the proof:
its size is bounded by `rowCommonBohrRank`, the proper progression lies
in its quarter Bohr set, and every varying frequency map is normalized
and Freiman on the full Bohr set of radius `1/(8*pi)`. The global theorem
and the same-witness column-agreement theorem retain this stronger data.
No new assumption or density loss is introduced by this strengthening.

**Translations preserve the varying list.** For a normalized Freiman map
on `B(Gamma,rho)`, a centre in `B(Gamma,rho/2)` and a point in
`B(Gamma,rho/4)` satisfy `theta(t+u)=theta(t)+theta(u)`.
`translatedFrequencyBase` adds all four centre values of each map to the
fixed spectrum, costing at most `4*ell` frequencies. On the new vertical
domain at half radius, the old translated domain constraints hold. All
`ell` varying maps remain unchanged.

**Localize whole coherent configurations.**
`coherent_translation_localization` refines a coherent family of quadruple
density `kappa` into any target set of ambient density at least `p` inside
the same quarter Bohr set. Additive translation averaging first retains
`kappa*p^4`; collision removal and pointwise row selection then retain
`kappa*p^4/512`, provided `8 <= kappa*p^4*N`. The translation centres lie
in the half Bohr set: this follows from an actual surviving configuration,
not an assumption on the averaging output. The new single family retains
local Freiman linearity, normalization, dense coherent quadruples, and
actual translated witnesses in the original family.

`HasCoherentTranslationRefinement` packages these witnesses for iteration.
For a refined spectrum of size at most `d`, the quarter Bohr density is
bounded below by `quarterBohrDensity d rho = refinementCells(rho/4)^(-d)`.
`coherent_bohr_refinement` therefore provides a quantified refinement for
any enlarged spectrum, with the same varying maps and their Freiman
identities on the new full Bohr domain.

**Strict rank increase with coherence retained.**
`coherent_relation_rank_step` combines this result with the existing
bounded-bad-pair rank theorem. If the bad-pair estimate at error `epsilon`
and cutoff `R` fails, set

`D = relationRankStep epsilon ((2*R+1)^(|B|+2*ell)) cells |Gamma|`.

The constructed new spectrum contains `Gamma`, has size at most `D`, and
strictly enlarges the relation submodule of the unchanged varying family.
At the same time it yields a coherent translation refinement of density
`kappa*(quarterBohrDensity D rho)^4/512`. Thus the rank potential and the
coherent quadruple family can now be advanced in the same step. This
addresses the defect that retaining an arbitrary dense vertex subset
need not retain a dense coherent quadruple family. A uniform terminating
iteration, the subsequent BSG argument, and the final quantitative budget
are still required.

The four new modules check in a 461-module production closure. Eight new
named theorems and eight affected existing/global theorems pass individual
axiom checks with only `propext`, `Classical.choice`, and `Quot.sound`.
No upstream code is added and no numbered catalogue entry is closed.


**Final merged verification.** The complete audit checks 8,221 public
Gowers theorems in 5,366 combined modules (5,364 facade modules, including
4,152 OAI modules), with only `propext`, `Classical.choice`, and `Quot.sound`.
The eight new named theorems and eight affected existing/global proofs
also pass individual axiom checks. The numbered ledger is byte-for-byte
unchanged at 115 companions and five open entries, retaining all existing
statement-fidelity qualifications. The port scope remains 4,134 upstream
and 17 compatibility modules. Reviewed incoming changes concern only the
independent topology obstruction certificates, code, tests, and report;
they add no Gowers dependency or licensing scope.


### J.135. Terminating coherent regularity and an actual quasirandom graph

**One common budget for the iteration.**
`coherentRelationBudget epsilon R cells ell d` bounds the next domain rank
and the enlarged fixed-frequency set, including the `4*ell` possible new
centre frequencies. For a chosen final rank bound `D`, use the uniform
loss `q = coherentIterationLoss D rho = quarterBohrDensity(D,rho)^4/512`.
This loss is positive and at most one. A sufficient modulus condition is
`8 <= kappa*q^n*N`, which pays every collision-removal step of a refinement
lasting at most `n` rounds.

**Termination while retaining configurations.**
`coherent_relation_iteration_budget` uses strong induction on the remaining
relation codimension. Each failed bad-pair estimate strictly increases the
relation-submodule dimension of the same `ell` varying maps, so at most
`ell` refinements occur. Early stopping simply restricts the final vertical
radius to the promised `sigma/2^n`. The theorem retains vertex and coherent
quadruple densities at least `kappa*q^n`, domain rank at most `D`, and at
most `|B|+4*n*ell` fixed frequencies. Local Freiman linearity and zero
normalization hold on the actual final Bohr domains.

`CoherentFrequencyFamily` records the configuration hypotheses and makes
radius restriction explicit. Every refinement carries a source map into
the previous vertex set and maps every retained quadruple into a previous
quadruple. These maps compose through the induction; original point and
whole-configuration witnesses are therefore retained, not just their
cardinalities.

**Keep the number of source translations bounded.**
`sourceTranslationOffsets` records the values `source u-u`. One row-label
refinement has at most four such offsets, and composition multiplies their
counts. The terminating result has at most `4^n` offsets. This preserves
the option of a later common-translation restriction with an explicit
finite loss, once all relevant quadruples are known to be respected.
No claim is made that an arbitrary such restriction preserves the current
coherent-quadruple count.

**Uniform sparse-relation and quasirandom conclusions.**
`exists_coherent_sparse_relation_domain` takes `n=ell` and defines
`D = coherentRegularityRank = coherentRelationBudget^[ell] d`, retained
density `coherentRegularityDensity = kappa*q^ell`, and modulus bound
`ceil(8/retainedDensity)`. It constructs a domain on which the requested
bounded bad-pair estimate holds, retaining all the source and coherence
information above.

`exists_coherent_quasirandom_domain` uses the existing explicit Fourier
cutoff with frequency bound `|B|+4*ell^2+2*ell`. For any prescribed positive
box error at most one, with explicit cell and modulus conditions, it
constructs the actual Bohr graph and proves the box-error estimate on the
same refined domain that carries the coherent family. Its vertical fixed
radius is `tau = sigma/2^ell`, and its varying phase radius is `tau/4`.
The hypotheses include the explicit analytic smoothing bound and coherent
regularity modulus bound; neither a quasirandomness oracle nor a
coherent-subset oracle is assumed.

`IsSingleCoherentProgression.regularity_input` verifies that the previously
constructed global anchor family supplies the exact full Bohr-domain,
frequency, and coherent-density input. The needed upper bound on its
vertical radius is also proved. Applying a globally uniform numerical
threshold, obtaining the later BSG conclusion, transferring all source
agreement, and certifying the final Gowers budget remain outstanding.
In particular, prescribed box error here is not yet a certificate that it
is small enough relative to every subsequent retained-density requirement.

All seven modules check in a 484-module production closure. All nineteen
new named theorems pass individual axiom checks using only `propext`,
`Classical.choice`, and `Quot.sound`. No upstream source is added and no
numbered catalogue entry is claimed closed. The completed full audit checks
8,255 public Gowers theorems in a 5,373-module combined closure, with only
the same three axioms. The facade closure has 5,371 modules, including
4,152 OAI modules. The generated ledger is byte-identical to the tracked
115-companion / five-open ledger, and the port scope check passes for the
unchanged 4,134 upstream and 17 compatibility modules.

## J.136. Adaptive coherent regularity at the retained density

The prescribed-error construction in J.135 did not control its error relative
to the density lost during refinement. The new adaptive construction uses an
exact state `(d, kappa)`, recording both a rank bound and coherent-quadruple
density. At a failed regularity test the next rank is the coherent relation
budget at the current error/cutoff, and the next density is exactly
`kappa * coherentIterationLoss nextRank rho`. Error and cutoff may depend
on both coordinates; neither schedule is required to be monotone.

`coherent_adaptive_relation_iteration` stops after at most the remaining
relation-space dimension. It preserves the same varying frequency family,
source witnesses for original points and quadruples, and at most `4^s`
source offsets after `s` steps. Fixed frequencies grow by at most `4*s*ell`.
The conclusion uses the exact stopping state and vertical radius `sigma/2^s`.
A finite supremum of collision thresholds over the possible states supplies
a modulus bound independent of the ambient modulus.

`exists_coherent_adaptive_dense_graph` adds the Fourier smoothing thresholds
and constructs a graph on that same refined domain. For
`m = |B| + 4*ell^2 + 2*ell`, its density is at least
`1/(2*(4*H)^m)`. Its box error is the fourth power of an accuracy schedule
evaluated at the exact final state. All coherence and source data remain.

`exists_coherent_density_controlled_graph` specializes to
`min(1/(2*(4*H)^m), kappa^power/scale)`, for arbitrary natural `power` and
positive `scale`. Consequently its normalized box error is at most
`(retainedDensity^power/scale)^4`. This resolves the circular error choice
without assuming a favorable relation between a fixed input error and the
density subsequently lost. The finite adaptive modulus bound is explicit;
no favorable growth rate for it or final Gowers threshold is claimed.

**Uniform original-input application and agreement.** The finite supremum
`coherentUniformGraphModulusBound` covers both fixed-frequency cardinality
and varying-family length up to their common bound. For the actual anchor
family the cell count is `ceil(32*pi)` and
`H = ceil(2^(8*jointSelectionRank)/(jointSelectionRadius/2))`; all required
inequalities and positivity conditions are proved. The initial rank is the
maximum of the common Bohr rank and `8*jointSelectionRank`.

`IsSingleCoherentProgression.density_controlled_graph` constructs the graph
under this uniform bound. `global_coherent_density_controlled_graph` starts
from the original dense bihomomorphism and an explicit threshold depending
only on its density, the chosen power, and scale. It retains the original
column witness system, popular anchor witnesses and the graph of that same
family. There is no regularity or graph-existence oracle in its hypotheses.

`IsSingleCoherentProgression.refined_popular_agreement` transfers actual
agreement with the original columns to every final domain
`B' union image(theta_i(u))`. It uses the original popular-arrangement
witness at `source u`, and proves a fresh agreement density
`coreAnchorAgreementDensity popularity (fixedBound+ell) g d r tau`.
It does not infer a density bound merely by restricting an old agreement set.

All ten new modules compile in a 496-module production closure, comprising
nineteen new named proofs. All nineteen pass individual axiom checks using
only `propext`, `Classical.choice`, and `Quot.sound`. The completed merged
facade audit checks 8,299 public Gowers theorems with the same axiom boundary:
5,381 facade modules, including 4,152 OAI modules, and 5,383 combined audit
modules. The ledger is byte-identical to the tracked 115-companion / five-open
catalogue. Port scope remains 4,134 upstream and 17 compatibility modules;
no upstream source or licensing scope changes.
Graph extraction/weak transitivity, subsequent local linear structure,
original bihomomorphism transfer and the final quantitative certificate
remain outstanding. The current graph estimate is for the specified final
radii; no estimates at further shrunk radii are silently assumed. A finite
profile of radii can use the same sparse-relation certificate provided its
cell parameter covers the smallest radius, but this extension remains to
be formalized. No numbered entry is claimed closed.

## J.137. Uniform radius profiles and coherent weak transitivity

**One domain, all admissible radii.** `DenseBohrGraphProfiles` records
positive-density box estimates for every pair `0 < nu <= eta < 1/4` with
`1 <= nu*H`. The graph uses fixed frequencies at radius `eta` and varying
frequencies at radius `nu`. Its density is at least `1/(2*H^m)`.
`denseBohrGraphProfiles_of_sparse_relations` proves the entire profile from
one bounded-relation certificate and one smoothing threshold.
`exists_coherent_adaptive_profiles` constructs that certificate on the same
refined domain as the retained coherent quadruples, with the exact adaptive
state and all original source witnesses. No second refinement is needed
when a smaller admissible radius is chosen.

**Sharper coverage bound.** `box_empty_rectangle_card` and its finite-set
version apply directly to a real-valued graph function that is zero on a
rectangle. They prove `delta*|U|*|Z| <= epsilon*|B|*|C|` from a box bound
`epsilon^4*|B|^2*|C|^2`. In the Boolean case this improves the previous
variance-based missing-witness estimate: the density loss is linear in
`delta*bridgeDensity`, instead of quadratic. Passing the actual graph
function also avoids an expensive Lean definitional comparison between
different decision procedures for the edge predicate.

`quasirandom_freiman_zero` combines this estimate with
`freiman_nonzero_card_half` and the Bohr cardinality lower bound. If a
normalized Freiman map vanishes on all neighborhoods indexed by a set of
at least `kappa*N` bridges, then it vanishes on the half-radius Bohr set,
provided `2*M^|T|*epsilon < delta*kappa` and `(r/2)*M >= 1`.
The profile specialization uses `M=2*H` and the sufficient inequality
`4*(2*H)^|T|*epsilon < H^(-m)*kappa`.
This step works for every nonzero modulus; it does not use prime-target
frequency removal or its much smaller output radius.

**Actual bridge composition.** `freiman_frequency_bohr_complete` proves
that three frequency domains at radius `r/3` contain the fourth domain at
radius `r` whenever the four frequency values satisfy the Freiman identity.
`coherent_pair_weak_transitivity` applies this to bridges `(z+a,z)` between
`(x+a,x)` and `(y+a,y)`. The two bridge identities make the endpoint defect
vanish on the appropriate graph neighborhoods. The coverage theorem then
proves the direct endpoint identity at radius `r/6`.
All domains, endpoint memberships, bridge counts, and error conditions are
explicit. The varying maps must be Freiman-linear on the common parameter
domain, precisely as supplied by coherent regularity.

**Finite chains with a concrete accuracy schedule.** The cell count
`coherentRadiusProfileCells sigma ell depth =
ceil(3*2^ell*6^depth/sigma)` pays for the one-third radii at every level
`i <= depth`, after every possible regularity stopping time `s <= ell`.
For `beta=H^(-m)`, `coherentBridgeAccuracy H m k eta` is
`min(beta/2, beta*eta/(8*(2*H)^k))`. It is positive and satisfies the strict
coverage inequality for bridge density `eta`.

`exists_coherent_bridge_system` chooses
`eta = retainedDensity^power/scale` at the exact stopping state and
`k=4*(|B|+4*ell^2+ell)`. It constructs the original-witness-preserving
coherent refinement, all admissible graph profiles, and a
`CoherentBridgeSystem` along `tau/6^i`. The latter proves direct identities
from sufficiently many same-level bridges with one further factor-six
shrink. Here `power` and `depth` are arbitrary natural numbers and `scale`
is any positive real number.

The single-family and global wrappers choose all numerical parameters and
use finite suprema over bounded frequency cardinalities. The global
threshold depends only on the original density, chain depth, power, and
scale. It retains the original column witnesses and popular anchor
arrangements, so the actual-domain agreement theorem of J.136 still applies.

This is the weak-transitivity input for the next combinatorial extraction,
not the abstract Balog--Szemeredi--Gowers conclusion itself. Mixed-level
composition, the dense relation catalogue, robust graph extraction and the
subsequent local structure remain to be assembled. No numbered entry or
final Gowers bound is claimed closed.

All fourteen new modules compile in a 508-module production closure. All
twenty new named proofs pass individual axiom checks with only `propext`,
`Classical.choice`, and `Quot.sound`. The full audit checks 8,342 public
Gowers theorems with the same axiom boundary, in 5,397 combined modules;
the facade has 5,395 modules, including 4,152 OAI modules. The generated
ledger is byte-identical to the tracked 115-companion / five-open catalogue,
and port scope passes with the unchanged 4,134 upstream and 17 compatibility
modules. No upstream source or licensing scope is added.


### J.138. Dense coherent pairs and robust graphs with two radius losses

The coherent bridge system from J.137 now supplies the first combinatorial
extraction, with all witnesses retained through the global construction.
The ten new modules add twenty named proofs and require no new upstream port.

`CoherentRelationLevel` uses radius `sigma/6^(i-1)` at level `i`.
Monotonicity, symmetry, simultaneous endpoint swapping, crossing, and
mixed-level bridge composition are proved from the existing pair relation
and the constructed bridge system. Encoding a coherent quadruple as
`((a0,a2),(a3,a1))` injects its mass into level-one pair relations. Summing
over their common difference gives exactly the sum of difference-graph
edge counts.

For quadruple mass at least `kappa*N^3`, the density obeys `kappa <= 1`.
At least `kappa*N/2` differences have graph density at least `kappa/2`.
For each such difference, common-codegree extraction gives a set of at
least `3*kappa*N/16` vertices. Two applications of weak transitivity make
all pairs in that set related at level three, hence radius `sigma/36`.
The sufficient bridge threshold is `eta <= kappa^2/256`, with `eta > 0`;
only bridge indices zero and one are needed. This directly exploits the
existing common-codegree lemma, avoiding a longer path-compression step.

Encoding a vertex and its difference as `(u+a,u)` is injective. The union
of the selected sets therefore has at least `3*kappa^2*N^2/32` pairs,
and every two pairs with the same difference have the level-three identity.
For odd prime modulus, the proved orientation-and-symmetrization lemma
retains at least half this mass while preserving those identities. It is
not sufficient merely to union an arbitrary pair family with its reversal.

`HasCoherentRobustGraph` records a symmetric graph `E` of density at least
`delta = 3*kappa^2/64`, whose equal-difference edges have coherent identities
at radius `sigma/36`. It also records a subset `A` of density at least
`9*kappa^2/512`, such that every two vertices of `A` have at least
`delta^5*N^3/16384` four-edge walks in `E`.

The single-family and popular-anchor wrappers retain the exact refined
frequency system, source map, original coherent progression and original
popular witnesses. `global_coherent_robust_system` constructs them from
the original dense bihomomorphism. Its modulus threshold is
`max (globalCoherentBridgeModulusBound alpha 1 2 256) 3`.
The density in the graph estimates is the positive density at the actual
regularity stopping state. No arbitrary restriction to a source-offset
fiber is made; the previous agreement-transfer theorem remains applicable.

This establishes the first extraction with an explicit constant radius
loss. Matching walks to obtain rich cross-subset relations, the subsequent
local structure, and a comparison with the printed final Gowers budget
remain open. This checkpoint does not close a numbered catalogue entry
or assert a tighter final Szemeredi threshold.

All ten modules compile in a 518-module production closure. All twenty
named proofs pass individual axiom checks, and the full audit checks
8,387 public Gowers theorems with only `propext`, `Classical.choice`, and
`Quot.sound`. The combined audit has 5,407 modules; the facade has 5,405,
including the unchanged 4,152 OAI modules. The generated ledger is
byte-identical to the tracked 115-companion / five-open catalogue. Port
scope remains 4,134 upstream modules and 17 compatibility modules, with
no change to the retained licenses or provenance notices.


### J.139. Coherent mixed-subset richness via balanced walk compression

The fourteen new modules assemble the second graph-extraction step while
retaining the original column and anchor witnesses. They add twenty-seven
named proofs and no upstream ports.

**Two-level compression.** `graph_four_walks_le_of_small_common` counts
four-walks by their middle vertex. If codegree at least `t` in `G` implies
an edge of `H`, and the endpoints have at most `t` common neighbors in
`H`, their four-walk count in `G` is at most `2*t*n^2`.
For middle vertices outside the common `H` neighborhood, one `G` codegree
is below `t` and the other is at most `n`; inside it, both are at most `n`.
This proves the bound directly, including graphs with loops.

`CoherentBridgeSystem.four_walks` applies two successive common-neighbor
implications. More than `2*eta*N^3` four-walks at relation level `i+1`
force the endpoint relation at level `i+3`, provided `i+1 <= depth`.
Consequently four-walks of level-three relations give level five, at
radius `sigma/1296`. This balanced argument avoids sequentially composing
all four edges and does not use the old frequency-removal kernel radius.

**Matched walks and popular endpoint fibres.** Two walks with equal edge
steps are translates. Crossing the coherent edge identities gives a
four-walk in their common-difference relation. The three-coordinate key
`(u,u',v')` determines the endpoints; inside each key fibre the second
internal triple determines both walks. Thus every fibre has size at most
`N^3`, and injects into the corresponding coherent-relation four-walk set.

A walk family of mass `mu*N^5` has at least `mu^2*N^6` matched pairs by
Cauchy--Schwarz over the `N^4` possible edge-step sequences. At least
`mu^2*N^3/2` endpoint keys have fibre size at least `mu^2*N^3/2`.
When `4*eta < mu^2`, every such fibre passes the compression threshold.
The key maps injectively to the mixed endpoint quadruple
`(u,v',u',v'+u-u')`. Therefore endpoint sets of densities `beta1,beta2`,
with four-walk density `lambda`, have at least
`(beta1*beta2*lambda)^2*N^3/2` exact mixed quadruples at level five.
All endpoint memberships and the additive identity are checked.

**A nonvacuous density-dependent threshold.** For retained coherent
quadruple density `kappa`, J.138 supplies a set `A` of density at least
`9*kappa^2/512` and walk density
`lambda = (3*kappa^2/64)^5/16384 = c*kappa^10`, where
`c = 3^5/(64^5*16384)`.
`HasCoherentRichSet` records the resulting exact mixed-quadruple lower
bound for every two subsets of `A` above its specified threshold. It
retains the full factor `(beta1*beta2*lambda)^2/2` for any two supplied
density lower bounds `beta1,beta2 >= beta`. This dependence is needed
for the later tuple recursion; replacing it by the bound at the minimum
threshold would lose the quantitative input to that recursion.

The global construction uses a freely chosen natural parameter `p` and
subset threshold `beta = kappa^(p+2)/512`. Since `0 < kappa <= 1`,
`beta <= kappa^2/512`; the set `A` itself meets the threshold. The explicit
`HasCoherentRichSet.self_richness` theorem records this fact and the
resulting actual quadruple count. A threshold chosen independently of the
retained density would not establish this nonvacuity.

Choose the constant
`S = coherentRichPowerScale = 256 + 8*512^4/c^2`
and bridge accuracy `eta = kappa^(28+4*p)/S`. The proved estimates are
`eta <= kappa^2/256` and `4*eta < (beta^2*lambda)^2`.
They hold at the exact regularity stopping state, so neither is an
unproved error-budget hypothesis in the global result. Bridge depth three
suffices for both extraction stages. The earlier general accuracy lemmas
also remain available for independently specified positive thresholds.

`global_coherent_rich_system` takes only the original dense
bihomomorphism, `p`, and the explicit density-dependent modulus bound
`max (globalCoherentBridgeModulusBound alpha 3 (28+4*p) S) 3`.
Its single-family and popular-anchor packages retain the actual refined
frequency system and source map, original coherent progression, original
popular witnesses, and all-radius graph profiles. The radius loss is
constant `1296`, independent of `p`; the accuracy requirement carries
the increasing density exponent.

The recursive higher-tuple construction, subsequent local structure and
comparison with the printed final Gowers budget still remain. This
checkpoint does not close a numbered catalogue entry and does not claim
an improved final Szemeredi threshold.

All fourteen modules compile in a 529-module production closure. The
final interface passes all twenty-seven individual axiom checks and the
full audit of 8,442 public Gowers theorems, using only `propext`,
`Classical.choice`, and `Quot.sound`. The combined audit has 5,421 modules;
the facade has 5,419, including the unchanged 4,152 OAI modules. The
115-companion / five-open ledger is byte-identical, and port scope still
contains 4,134 upstream and 17 compatibility modules. No upstream source,
license scope, or provenance notice is changed.


### J.140. Compatible words and endpoint identities at controlled radii

Fifteen new modules extend J.139 to dense compatible representations of
every bounded-length list of anchors. They add thirty-five named proofs,
reuse the existing injective tuple splice, and add no upstream ports.

**Threshold-aware anchor and word counts.** `ThresholdColumnRichness`
retains the actual two subset densities and the factor one-half in J.139.
`popular_column_anchors_dense_above` shows that the anchor pruning argument
only needs richness for subsets of size at least half the guaranteed
ambient density. For ambient density `b` and walk density `eta`, this
retains at least `b*N/2` anchors, each with at least
`lambda*N^2` triple representations, where `lambda = eta^2*b^3/32`.
The subset cutoff must be at most `b/2`.

`threshold_column_word_representations_step` glues a triple family of
density `lambda` to a word family of density `delta`. It applies richness
only at the two popular endpoint densities `lambda/2` and `delta/2`.
With both above the cutoff, the output density is
`eta^2*lambda^3*delta^3/128`. The splice is injective, so no multiplicity
loss is hidden in this estimate. Keeping the two input densities separate
preserves a cubic recurrence.

Define `delta_0=lambda` and
`delta_(n+1)=(eta^2*lambda^3/128)*delta_n^3`.
The schedule is positive and decreasing when `0 < lambda,eta <= 1`, and
its exact formula is
`delta_n=(eta^2*lambda^3/128)^((3^n-1)/2)*lambda^(3^n)`.
The proved sum-of-powers version uses the same geometric exponent.
For words of at most `K+1` triples, choose the subset cutoff `delta_K/2`.
It is below every needed intermediate density divided by two.

**Parameters at the actual regularity state.** For retained density
`kappa`, set `b=9*kappa^2/512` and `eta=c*kappa^10`, with the same
`c=3^5/(64^5*16384)` as J.139. Then
`lambda=a*kappa^26`, where `a=c^2*(9/512)^3/32`.
`coherentWordDensity kappa n` is exactly `C_n*kappa^E_n`, with
`C_0=a`, `C_(n+1)=c^2*a^3*C_n^3/128`, and
`E_n=75*3^n-49`. Both the coefficient identity and exponent formula are
proved. The coefficients are positive; fixed losses are retained rather
than assumed absorbable by increasing a power of `kappa` near one.

For a positive monomial cutoff `q*kappa^e`, the bridge accuracy
`kappa^(20+4*e) / coherentRichBridgeScale q` satisfies both graph extraction
and mixed-subset error inequalities. Instantiate `q=C_K/2`, `e=E_K`.
This yields explicit `coherentWordBridgePower K` and
`coherentWordBridgeScale K`, known before the regularity stopping time.
`CoherentBridgeSystem.word_family` constructs the rich set and dense
anchor set at that stopping state. Every list of `n+1` anchors, `n <= K`,
has at least `coherentWordDensity kappa n * N^(3*n+2)` compatible word
representations. The anchor set has density at least `9*kappa^2/1024`.

**Recovering auxiliary domains without frequency removal.** Compatibility
alone initially gives identities on a recursive domain involving two
auxiliary indices per splice. `coherent_word_domain` recovers those domains
from the anchors and output entries when each varying frequency is
Freiman-linear on the ambient index set. The first auxiliary index follows
from its triple's additive relation with radius cost three; the second
follows from the gluing quadruple with another cost three. Induction thus
uses a factor nine per word level.

`CoherentWordEndpointIdentities` consequently gives `ColumnWordIdentity`
using only anchor and output domains at radius
`coherentWordEndpointRadius sigma m = sigma/(1296*9^m)` for a word of
`m` triples. The radius is positive for positive `sigma`. There is no
additional prime-modulus threshold or frequency-cardinality term in this
identity theorem. The existing large-cost frequency-removal proof is not
used to obtain it.

The single-family and popular-anchor wrappers retain the same refined
source map, original progression and popular witnesses, graph profiles,
word families, and endpoint identities. Freiman-linearity on the refined
index set follows from the actual refinement certificate. The global
`global_coherent_word_system` constructs all of these from the original
dense bihomomorphism under the explicit bound
`max (globalCoherentBridgeModulusBound alpha 3
  (coherentWordBridgePower K) (coherentWordBridgeScale K)) 3`.

This completes the bounded compatible-word counting step along the new
coherent route, including endpoint-only identities. The subsequent local
structure and comparison with the printed Gowers budget remain open.
No numbered catalogue entry or improved final Szemeredi threshold is
claimed closed by this checkpoint.

All fifteen modules compile in a 540-module production closure. All
thirty-five named proofs pass individual axiom checks. The full audit
checks 8,531 public Gowers theorems with only `propext`, `Classical.choice`,
and `Quot.sound`, in 5,436 combined modules. The facade has 5,434 modules,
including the unchanged 4,152 OAI modules. The generated ledger remains
byte-identical at 115 companions and five open statements. Port scope
passes with the unchanged 4,134 upstream and 17 compatibility modules;
no license or provenance scope is added.


### J.141. Two nested word families from the same refined system

Eleven new modules construct the two compatible-word layers needed by
the common-extension argument. They add twenty-seven named proofs and no
upstream port. The construction remains valid independently of the
quantitative weakness of the earlier zero-core parameters documented in
J.5c; it does not repair that weakness.

**Restarting on actual exact quadruples.** The first word extraction has
ambient set `A` and anchor set `P`, with densities at least
`9*kappa^2/512` and `9*kappa^2/1024`. Its inherited richness applies to
`P` itself: the word-density cutoff is below the guaranteed density of
`P`. Consequently `P` contains an exact quadruple family of density
`kappa2 = d*kappa^28`, where
`d = coherentRobustWalkCoefficient^2*(9/1024)^4/2` is positive.
`CoherentFrequencyFamily.exact_subfamily` supplies its normalized local
maps and all quadruple identities at radius `sigma/1296`.
This family is counted anew using richness; arbitrary restriction of the
original quadruple family would not justify the density.

The bridge-system restriction, threshold monotonicity and index-shift
lemmas allow the second extraction to use the same frequency system,
maps and regularity certificate. Its radius starts four levels later,
since `6^4=1296`. Depth seven suffices for both extraction stages.

**One accuracy schedule for both layers.** Let `P_K,S_K` be the word
bridge power and scale from J.140. For outer and inner bounds `K,J`, use
`P=max(P_K,28*P_J)` and `S=S_K+S_J/d^P_J`.
For `0 < kappa <= 1`, the chosen accuracy `kappa^P/S` is at most both
`kappa^P_K/S_K` and `kappa2^P_J/S_J`. All inequalities and the exact
monomial identity are proved. No second regularity loss is introduced.

`HasCoherentNestedWordFamily` retains the first layer's richness, triple
and word counts, the exact new quadruple mass, and a second word family
on `P`. Unpacking gives sets `D ⊆ C ⊆ P ⊆ A ⊆ X`. Words anchored in
`D` have entries in `C`, hence in the first layer's anchor set `P`.
The two endpoint identity systems use the same maps throughout.
`HasCoherentNestedWordFamily.layers` combines both counts and identities
on one common radius. For `K=35,J=11`, this supplies the nesting required
for twelve anchors to thirty-six entries, followed by thirty-six anchors
to one hundred eight entries.

**Reserve the later profile scale explicitly.** Choose bridge depth
`13+2*(K+J+2)` and common radius
`R = sigma/(1296^2*9^(K+J+2)*3000)`.
The denominator is bounded by `6^depth`. The original cell budget
therefore satisfies `3 <= R*H` at every regularity stopping time.
The common radius is below both layers' endpoint identity radii for all
relevant word lengths. The factor `3000` reserves room for the later
extension scales; no tuple-level coverage assertion is inferred from
this numerical comparison alone.

`DenseBohrGraphProfiles.nested_profile` gives an actual graph profile
with fixed radius `R` and varying radius `R/3`, provided the original
radius is below `1/4`. Its density and box-error bounds are those of the
retained profile certificate.

The single-family, popular-anchor and global wrappers preserve the
original source map, original witnesses, full refinement data, profiles,
both word layers and both endpoint identity systems. The explicit global
modulus bound uses the above depth, power and scale and depends only on
original density and the two word-length bounds.

The remaining local common-extension and structural arguments are not
proved here. In addition, the kernel-checked growth obstruction in J.5c
shows the current global input chain cannot meet the final polynomial
contract merely through improvements downstream. The generic nested
construction can be reused with a replacement input chain. Neither a
numbered catalogue entry nor a tighter final Gowers threshold is claimed.

Verification after merging the incoming growth-obstruction and abstract BSG
modules: all 27 new named nested-construction proofs pass individual axiom
checks. The full combined audit checks 8,702 public Gowers theorems across
5,457 modules (5,455 in the facade closure), using only `propext`,
`Classical.choice`, and `Quot.sound`. The selected OAI audit closure remains
4,152 modules. The generated catalogue is byte-identical: 115 companion
proofs and five open statements; this count does not certify fidelity to
every printed statement. The selected-port scope check passes.

After also merging `Proofs16AbstractBSGCore`, the final audit passes with
8,715 public Gowers theorems, 5,458 combined modules and 5,456 facade
modules. The axiom boundary, port scope and numbered catalogue are unchanged.

### J.142. Abstract BSG compatible words with polynomial losses

The replacement route now has an abstract BSG theorem for every tuple
of anchors of bounded length in a prime cyclic ambient group.
`abstract_bsg_rich_core` retains the union graph, its same-difference
coherence, the dense sets `B′ ⊆ B ⊆ A`, and the robust four-walk certificate.
The previous `abstract_bsg_core` is a corollary. The incoming restriction
of weak transitivity to indices whose sum is at most 16 is retained.

`Proofs16AbstractBSGWords` defines triple and word representations for an
arbitrary quadruple relation `R`. The original triples and every splice
quadruple satisfy that same relation. Output words lie in `B` and have
the alternating value of their anchor list. Thus this interface can be
instantiated by bounded-image relations; it does not assume exact map
identities. The existing injective splice geometry is reused.

`Proofs16AbstractBSGBridging` proves the bounded-length induction. Write
`λ` for the retained triple density and `η` for the mixed-quadruple
coefficient. Its densities are

```
δ₀ = λ,
δⱼ₊₁ = η² λ³ δⱼ³ / 128.
```

`abstract_bsg_word_system` combines this with the core. For every anchor
list of length `j+1 ≤ k+1` in `B′`, its actual compatible representation
family has at least `δⱼ N^(3j+2)` members. It also returns the threshold
richness needed by further consumers. Its explicit positive transitivity
budget is the minimum of the core budget and the mixed-quadruple budget
at the smallest subset cutoff; no model packing or elimination appears.
The four-walk variant uses `Q 16`, rather than the six-walk paper's
`Q 36`. The word recursion prepends triples, consistently with the
existing column-word geometry.

`Proofs16AbstractBSGWordBounds` proves the exact parameter dependence:

```
λ = λ(1,1) c^28 / K^18,
η = η(1,1) c^10 / K^7,
δⱼ = Cⱼ c^(80·3^j−52) / K^(52·3^j−34),   Cⱼ > 0.
```

For `0 < c ≤ 1` and `1 ≤ K`, the cutoff is exactly `δₖ/2` and has the
same monomial dependence. All displayed density losses are polynomial
in `c` and `K` at each fixed tuple length. The input budget is positive
and explicit; this is not yet a comparison with the final Gowers budget.

Remaining replacement steps include obtaining bounded-image relations
with the required weak transitivity from the original dense column data,
Proposition 6.1's almost-all tuple image bound, the robust
Bogolyubov–Ruzsa progression step, and the subsequent common-extension
and structural arguments. The generic compatible-word theorem alone
cannot replace the globally instantiated zero-core chain. The five
numbered open entries and the final quantitative bounds remain open.
No upstream code is ported at this checkpoint.

Verification: the final production closure compiles across 238 modules.
All 23 new named proofs pass individual axiom checks. The full combined
facade audit checks 8,804 public Gowers theorems across 5,462 modules
(5,460 in the facade closure), using only `propext`, `Classical.choice`,
and `Quot.sound`. The selected OAI audit closure remains 4,152 modules.
The regenerated catalogue is byte-identical, with 115 companion proofs
and five open statements. Companion counts do not certify fidelity to
every printed statement. The selected-port scope check passes.

### J.143. Word image bounds and direct global endpoint identities

Compatible words now carry bounded-image information and exact endpoint
identities, with their own parameter certificates. The ten new modules
are recorded separately from the unchanged numbered catalogue.

`relation_word_defect_image_card_le_of_relation` proves that a word of
`ell` triples has at most `M^(2*ell-1)` defect values on its recursive
common domain if each permitted quadruple defect has at most `M` values.
The proof multiplies two relation image bounds at each splice, keeping
the induction's word image bound separate. It reuses the existing
alternating defect and list spectrum definitions.

When the varying frequencies are Freiman-linear on the index set,
`coherent_relation_word_domain` recovers every auxiliary column domain
from the anchors and output entries at radius `r/9^ell`. Hence the image
bound holds on the endpoint Bohr set. In a prime cyclic target,
`coherent_relation_word_exact` then gives exact identities at radius
`r/(9^ell*M^(2*ell-1))`, with no new frequencies. The uniform radius for
all words of length at most `k+1` is

```
boundedImageWordRadius r M k = r/(9^(k+1)*M^(2*k+1)).
```

The endpoint spectrum has at most `4*(k+1)*(base rank+varying rank)`
frequencies. `abstract_bsg_bounded_image_words` retains the same actual
BSG word families and maps throughout the density, rank and identity
conclusions. `bounded_image_quad_word_system` instantiates the relation
levels with image bounds `E^i`, automatically proving all three symmetries
and doubling one. Its weak-transitivity and Freiman frequency-structure
inputs remain explicit; symmetry does not establish those inputs.

**Direct original-data construction after the incoming merge.**
The incoming `global_column_word_system` applies J.142's BSG engine to
J.98's column data through the direct zero-relation ladder. Its stronger
version `global_column_word_witness_system` now retains the original
`IsColumnWitnessSystem A phi X T L W`, the witness mass bounds and all
local-map data. The previous theorem remains a corollary.

`relation_word_exact_representation` transfers arbitrary-relation words
with exact local-map identities to the existing exact column words.
Thus `relation_word_identity_remove_aux` reuses the already proved kernel
removal theorem. It requires no Freiman structure for varying frequencies.

`global_column_word_endpoint_system` starts from the original dense
bihomomorphism and an explicit modulus threshold. It returns the original
witness-linked maps, dense sets `B′ ⊆ B ⊆ X`, threshold richness, every
bounded-length compatible word family and its endpoint identity. Put

```
d = columnSpectrumCap (columnEightDensity alpha),
r16 = zeroLadderRadius d (1/(4*pi)) (globalColumnIdentityRadius alpha) 15,
rout = refinementKernelRadius (4*(k+1)*d) (2*k*d) (1/(4*pi)) r16.
```

The new modulus threshold is the maximum of the existing global BSG
threshold and the corresponding endpoint kernel cap plus one. The radius
is positive. Rank monotonicity proves this single threshold and radius
work for every shorter word. Kernel costs are paid for a fixed number of
columns per word, independently of the total number of words or models.
No global model packing or elimination appears in this construction.

The original-data theorem supplies a concrete input for the
Proposition 6.1/Claim 6.2 route. It does not establish the almost-all
additive 16-tuple image conclusion, robust Bogolyubov–Ruzsa progression
extraction, the later common-extension and structure steps, or the final
printed numerical comparison. The five numbered open entries remain.
No upstream code is ported at this checkpoint.

Verification after merging the direct column BSG application, its word
construction, prime-target Step 4 and the BSG growth certificates:
all 31 new named proofs pass individual axiom checks. The complete global
endpoint production closure compiles across 245 modules; the generic
bounded-image integration closure has 475 modules. The full combined
audit checks 8,918 public Gowers theorems across 5,477 modules (5,475 in
the facade closure), using only `propext`, `Classical.choice`, and
`Quot.sound`. The selected OAI audit closure remains 4,152 modules. The
regenerated catalogue is byte-identical: 115 companion proofs and five
open statements; this count does not certify fidelity to every printed
statement. The selected-port scope check passes.

### J.144. Individual tuple classes and the prime-group sampling step

The direct original-data construction now groups fixed alternating-value
tuples into bounded classes and supplies the sample used by Claim 6.3's
almost-all tuple argument. It preserves the original witness system and
column maps throughout.

`fixedRelationWordRepresentations` places the compatible words in a common
fixed-length type, preserving cardinality, entries, alternating value and
endpoint identity. `column_tuple_class_cover` reuses the existing maximal
disjoint-family argument. It selects `J` with `|J|·delta ≤ 1`, assigns each
tuple to a representative, and proves pairwise identities inside a class.
The two kernel costs use only a fixed number of columns:

```
s = refinementKernelRadius (2*(k+1)*d) (3*(k+1)*d) rho rword,
t = refinementKernelRadius (2*(k+1)*d) ((k+1)*d) rho s.
```

`global_column_tuple_classes` instantiates this from the original dense
bihomomorphism, with the J.143 word density and endpoint radius. Each
representative has its own spectrum of size at most `(k+1)*d`, normalized
Freiman-linear map, and a class label. The number of representatives does
not enter either kernel radius. No union of all model spectra is formed.

**Finite sampling counts.** `linear_sample_preimage_card_le` recovers one
sample coordinate from a nonzero linear combination, proving
`# {e : Fin r → ZMod N | sum_i c_i e_i ∈ Z} ≤ |Z| N^(r-1)`.
Union over the at most `3^r` nonzero ternary coefficient vectors gives
`ternary_samples_meeting_card_le`. Boolean subsum collisions are a special
case with `Z = {0}`, giving at most `3^r N^(r-1)` colliding samples.

`sample_retention_sum_ge` counts retained indices through product domains.
`sample_bad_indices_sum_le` counts sparse-kernel tuple events by signed
subsums. `exists_sample_of_mean_bounds` combines the two estimates with a
collision penalty in one finite weighted average. It produces a sample
with many retained indices, few bad tuples and no Boolean collisions.

`prime_group_sample_selection` and `bohr_sample_selection` give the
explicit statement. If `|X| ≥ bN`, every sample domain has density at least
`beta`, kernel sets have size at most `eta N`, and `|Q| ≤ N^m`, it suffices
that

```
8·3^r·eta ≤ epsilon·b·beta^r,
8·3^r ≤ b·beta^r·N.
```

Then the retained set has size at least `b·beta^r N/2`, the Boolean cube has
`2^r` distinct points, and at most `epsilon N^m/2` original tuples hit a
kernel by a nonzero signed coefficient vector. The retained density does
not depend on `epsilon`. The Bohr specialization uses `beta = 1/q^d` and
`1 ≤ tau q` with a common rank bound `d`.

**Original-data sample.** `columnAnchorFibre_card_le` proves the exact
ambient budget `N^k` for `(k+1)`-tuples with a fixed alternating value.
`sparseColumnTuples` is the additive fibre whose local tuple zero level has
at most `eta N` points. `global_column_tuple_sample_system` constructs all
of this from the original dense bihomomorphism. Put

```
b = absBsgEps (globalColumnQuadrupleDensity alpha) 1,
tau = globalColumnTupleClassRadius alpha k/(100r),
q = ceil(1/tau),  beta = 1/q^d,
eta = epsilon·b·beta^r/(8·3^r).
```

Its explicit modulus threshold covers the class construction, `N ≥ 7`,
and `N ≥ 8·3^r/(b·beta^r)`. It is independent of `epsilon`, as is the
retained density `b·beta^r/2`. The output retains original witnesses,
individual model spectra, class labels and identities; the bad-tuple bound
is measured on the original index set, before retention.

For `k = 15`, this is the sampling step for additive 16-tuples. Remaining
work in Proposition 6.1 is to choose representative tuples in classes that
meet the retained set outside the bad family, separate their finite
sample-value sets by a logarithmic number of characters, take a popular
box of column values, and turn the resulting dense tuple zero levels into
image bounds. The robust Bogolyubov–Ruzsa progression step and subsequent
structure arguments remain open, as does the final printed numerical
comparison. No numbered catalogue entry or final bound improvement is
claimed here. No upstream code is ported at this checkpoint.

**Simplification to check next (not yet formalized).** The present tuple
classes give exact identities, rather than bounded-image differences.
For the balanced 16-tuple consumer this should allow separation only of
representative values at the `r` sampled points, instead of the entire
Boolean cube. In each class meeting the retained additive-tuple fibre,
choose any tuple in that fibre as the representative. Its value at each
sample equals the value of every retained tuple in the same class, because
all their corner indices satisfy the small sample-domain constraints.

The separating set then has at most `|J|·r` values. Put columns into common
Dirichlet cells for each character and sample. Balanced alternating sums
cancel the common cell centres, and a constant cell count depending only
on tuple length makes each tuple value too small in every chosen character
to be separated. Exact class agreement and separation force that tuple
value to be zero at every sample. Boolean injectivity ensures a sample is
nonzero. Thus a tuple with sparse zero level lies in the previously counted
bad family. Every other tuple has a dense zero level, from which the
existing dense-level image theorem supplies the desired image bound on a
half-radius Bohr domain. The cardinality, cell, and containment arguments
still need Lean proofs; this paragraph records the proposed simplification.

Catalogue hygiene: the incoming one-pair lemma from Milićević's Lemma 9.2
is named `milicevic_lemma_9_2_pair`. Its former name matched the Gowers
catalogue's related-theorem prefix for Lemma 9.2, even though it concerns
a different paper. The explicit source prefix removes that erroneous
association without changing its mathematical statement or proof.

Verification after merging the incoming Step 5 pairing and independence
results, and correcting the modern-source lemma name: all 32 new named
proofs pass individual axiom checks. The complete original-data sampling
production closure compiles across 269 modules. The combined audit checks
9,018 public Gowers theorems across 5,493 modules (5,491 in the facade
closure), using only `propext`, `Classical.choice`, and `Quot.sound`.
The selected OAI audit closure remains 4,152 modules. The regenerated
catalogue is byte-identical to the prior verified inventory, with 115
companion proofs and five open statements. These counts do not certify
fidelity to every printed statement. The selected-port scope check passes.

### J.145. Almost-all 16-tuple image bounds from one sample

The original-data prime-cyclic almost-all image stage is proved.
`global_column_almost_all_tuple_images` starts with the original dense
bihomomorphism and J.144's explicit modulus threshold, using `k = 15`
and **one** sampled point. It returns original witness-linked column maps
on a dense index set `U` and bounds their images on half-radius common
Bohr domains for all but `epsilon N^15/2` additive 16-tuples in `U`.
The retained density and modulus threshold are independent of `epsilon`.

The simplification recorded after J.144 is now formalized. Exact class
identities bound the number of tuple values at the common sample point by
`|J|`, without collecting the model spectra into one common spectrum.
`finite_class_value_image_card_le` and `column_tuple_value_image_card_le`
prove this finite compression directly; no choice of new model tuples is
needed.

`exists_tuple_zero_value_cell` separates the nonzero tuple values using
at most `clog 2 (M+1)` characters when their number is at most `M`. A popular
joint Dirichlet cell has mass at least `|V|/40^m`. The existing
`same_cell_even_not_separates` theorem, with eight pairs, proves that every
balanced 16-tuple value from this cell is too small in every chosen
character to be separated. Since a nonzero additive-tuple value belongs
to the separating set, its value at the sample must be zero. The constant
cell count is **40**, rather than the conservative 160 suggested earlier.

A Boolean-injective sample of length one is nonzero. The unit ternary
coefficient gives its single sampled point as a signed subsum. Thus every
additive tuple in `U` whose zero level is sparse belongs to the bad family
already bounded by J.144. For every other tuple, its zero level has density
at least `eta`. `column_tuple_image_card_le_of_dense_zero` applies the
existing dense-level image theorem to its normalized Freiman tuple map.
Its spectrum has at most `16d` frequencies. No new frequency-structure
hypothesis, model packing, or elimination is introduced.

Put

```
d = columnSpectrumCap (columnEightDensity alpha),
M = ceil(1/globalColumnTupleRepresentationDensity alpha 15),
m = clog 2 (M+1),
a = globalColumnTupleSampleDensity alpha 15 1 / 40^m,
eta = globalColumnSparseKernelDensity alpha 15 1 epsilon,
K = ceil((denseLevelCells (1/(4*pi)))^(16d)/eta).
```

The theorem gives `|U| ≥ aN`, with `a > 0`, and at most
`epsilon N^15/2` additive tuples have more than `K` values on the common
domain of radius `1/(8*pi)`. It also retains the nonzero common sample
and the exact zero identity there for every additive tuple in `U`.
All data remain linked to the original bihomomorphism through
`IsColumnWitnessSystem` and the original witness mass bounds.

`Proofs16AlmostAllTupleBudgets` proves that the character budget obeys

```
m ≤ 1 + log(M+1)/log 2,
```

and, for `0 < epsilon ≤ 1`, that the image cap satisfies

```
K(alpha,epsilon) ≤ (K(alpha,1)+1)/epsilon.
```

The latter is a reciprocal-linear exceptional-fraction bound. These are
intermediate certificates; they are not a proof of the final printed
Gowers threshold or an improvement of the final progression bound.

This closes the original-data prime-cyclic analogue needed from
Proposition 6.1. It does not assert the full arbitrary-group version or
its arbitrary bounded-image input interface. Next is the robust
Bogolyubov–Ruzsa progression extraction (Step 3), followed by the remaining
structure assembly and comparison with the final numerical budget. The
five numbered open entries remain. No upstream code is ported here.

Verification after merging the incoming Claim 9.4 selection, core and
escape proofs: all 16 new named proofs pass individual axiom checks.
The full production budget closure compiles across 282 modules. The
combined audit checks 9,055 public Gowers theorems across 5,502 modules
(5,500 in the facade closure), using only `propext`, `Classical.choice`,
and `Quot.sound`. The selected OAI audit closure remains 4,152 modules.
The generated catalogue is byte-identical: 115 companion proofs and five
open statements; these counts do not certify fidelity to every printed
statement. The selected-port scope check passes.

Step 3 lead: the selected port already contains
`OAI.Erdos3.CyclicCrootSisask.exists_quartic_bogolyubov_progression`
in `Estimates/LocalizedSiftingAlmostPeriods`. From density `exp(-p)` it
gives a proper centered progression in `2A-2A`, rank at most
`2+C(p+1)^4` and mass at least `exp(-C'(p+1)^8)N`. This is not yet the
robust representation-count input. Its pointwise almost-periodicity
engine can instead be applied to the popular-difference set, whose
difference multiplicities are at least `exp(-2p)N/2`. A proof that the
resulting Bohr set has uniformly many representations is still needed,
as is the progression-indexed transfer of the almost-all image data.
This lead requires no new upstream port; the relevant code is already
in the licensed selected closure.

### J.146. Robust progression geometry for the original tuple-image system

The geometric extraction required at the start of Proposition 7.1 is
proved in the prime-cyclic setting. Every point of the proper progression
has uniformly many four-term representations in the same original index
set whose additive 16-tuples have the J.145 image bound.

`unpopular_difference_pairs_card_le` bounds discarded pairs by
`theta N`. For a set of density at least `delta`, use the popular
threshold `theta = delta^2 N/2`. Then the popular differences carry at
least half of all pairs. `difference_event_probability_eq_pair_count`
identifies this with the selected Croot–Sisask difference-event
probability. A shifted event of probability at least `1/4` contributes at
least `delta^4 N^3/8` four-term representations: every shifted popular
pair has its whole difference fibre available.

`exists_difference_event_bohr_controller` adapts the width/rank
calculation from the selected upstream `exists_quartic_bogolyubov` proof
to an arbitrary difference event, with error `1/4`. It uses the
**pointwise** almost-periodicity theorem. It retains a regular Bohr set
with

```
rank ≤ 1 + C(p+1)^4,
radius ≥ exp(-C(p+1)),
```

where `C = 3*almostPeriodicityWidthConstant(1/4) > 0`, and controls every
shift in its carrier. Apply it to the popular-difference event to obtain
`exists_robust_difference_bohr`, whose every point has at least
`exp(-p)^4 N^3/8` representations.

`exists_robust_difference_progression` then uses the already selected
proper-progression extraction theorem. It gives a proper centered
progression `Q` with

```
rank ≤ 2 + C(p+1)^4,
|Q| ≥ exp(-Cprog(p+1)^8) N,
Cprog = 11(C+2)^2 > 0,
```

and preserves the same representation bound at **every** point. This is
the robust count needed by the next argument, rather than only inclusion
in a fourfold difference set. No eightfold convolution is required: the
published Proposition 7.1 starts with four-term representation families
and uses four of those families to read the additive 16-tuple bound.

`global_almost_all_images_with_robust_progression` starts from the
original dense bihomomorphism and retains its original witness system,
local maps, the J.145 dense set, common nonzero point, and almost-all tuple
image cap. Put `p = max(1,-log(globalColumnAlmostAllTupleDensity alpha))`.
It returns the proper progression and its uniform representation families
with rank and mass bounds independent of `epsilon`.

The two adapted proof consumers have prominent source/modification
notices. Their provenance, upstream copyright attribution, and full
Apache-2.0 terms are recorded in the adjacent `LICENSE.openai-math` and
`lib/openai-math/LICENSE.provenance`. The port manifest identifies the
useful Gowers consumer. The upstream module was already in the selected
licensed closure; no additional upstream module is ported.

Next is the progression-indexed map transfer in Proposition 7.1:
choose representative four-tuples with controlled image failures, construct
normalized local maps on the progression, and purify the remaining
relations. In a direct independent-choice argument, repeated progression
indices make the four representation choices correlated; they must be
handled explicitly rather than treating them as independent. Likewise,
cancelling map values does not remove their Bohr constraints. Additional
fixed helper spectra can be included in the chosen domains at `O(d)` cost,
but this must be proved in the map-transfer interface. These are remaining
proof obligations, not consequences of the robust geometric theorem.
The subsequent structure assembly and final printed numerical comparison
also remain open. No numbered catalogue entry or final bound improvement
is claimed at this checkpoint.

Verification after merging the incoming span-ball split: all 14 new named
proofs pass individual axiom checks. The complete original-data production
closure compiles across 374 modules. The combined audit checks 9,089 public
Gowers theorems across 5,508 modules (5,506 in the facade closure), using
only `propext`, `Classical.choice`, and `Quot.sound`. The selected OAI audit
closure remains 4,152 modules. The generated catalogue is byte-identical,
with 115 companion proofs and five open statements. These counts do not
certify fidelity to every printed statement. The selected-port scope check
passes. Adaptation licensing and the useful consumer are recorded without
expanding the upstream closure.

### J.147. Selected progression maps and linear-cap auxiliary removal

The first progression-indexed map selection is proved from the original
bihomomorphism. The maps retain their four-term representatives in the
original image-controlled index set, and their normalized common domains
are stated explicitly. Repeated-index queries are counted separately.

**Auxiliary constraints.** `freiman_image_remove_frequencies` proves a
stronger bounded-image readout than the earlier zero-removal interface.
If `f` is Freiman-linear on `B(T;rho)`, `|T| ≤ d`, `|U| ≤ e`, and its
image on `B(T∪U;rho)` has at most `K > 0` values, then

```
#Im(f on B(T;rho/2)) ≤ K * refinementKernelCap d e rho rho.
```

A popular level of the restricted image has density at least
`1/(K*ceil(1/rho)^(d+e))`; the existing dense-level theorem gives the
half-radius estimate. There is no new frequency and no prime-target or
modulus-size hypothesis. Dependence on `K` is linear. This estimate is
available for the remaining bridge-domain cancellation arguments.

**Independent selection.** `pinned_choice_count_product` counts exact
coordinate fibres of finite choice boxes. `four_choice_fibre_count_product`
and `four_choice_bad_count_product` prove the product law for four distinct
queried progression indices. Choices at every other index cancel.
`exists_independent_choice_few_bad_queries` then selects a valid global
assignment with the finite averaged error bound.

`flattenFourRepresentations` swaps adjacent pairs in the negative rows and
injectively embeds four representation rows into one original additive
16-tuple. Its index and map-value equations are proved. A bad original
tuple determines all four rows and their represented indices, so
`represented_bad_four_blocks_total_le` charges it at most once. Uniform
representation density `kappa N^3` therefore gives at most
`epsilon N^3/(2*kappa^4)` failed distinct-index queries.

**Repeated indices.** `repeated_additive_quadruples_card_le` gives at most
`6N^2` repeated-index additive queries. Each of the six coordinate pairs
has at most `N^2` possibilities, proved by recovering the remaining
coordinates. No independence is asserted for these queries.

**Local maps and their domains.** Chosen four-tuples define the local
maps. Subtracting the index-zero reference normalizes the index variable;
local normalization in the other variable is inherited from the original
maps. Each normalized map uses at most eight original spectra and remains
Freiman-linear on its common original-radius domain.
`normalized_quad_image_transfer` proves its half-radius defect image is
bounded by the original 16-tuple image. Reference-map values cancel, while
reference-map frequencies are retained in every normalized domain.

`exists_selected_progression_maps` combines these results with failure
bound

```
epsilon N^3/(2*kappa^4) + 6N^2.
```

`global_selected_progression_maps` uses the original-data robust
progression, with `kappa = exp(-p)^4/8`. For a requested error `eta > 0`,
choose original source error `epsilon = eta*kappa^4` and add the explicit
modulus condition `N ≥ 12/eta`. The output retains original witnesses,
local maps, robust representation counts, progression rank/mass bounds,
and the selected representatives. The normalized maps have codimension
at most `8d`, are Freiman-linear at radius `1/(4*pi)`, and their quadruple
images at radius `1/(8*pi)` exceed the inherited cap on at most `eta N^3`
additive queries. They vanish at both the vertical origin and index zero.
The progression rank and mass bounds remain independent of `eta`.

This proves the representative-selection/image-control part needed from
Claim 7.2. Its stronger source-approximation conclusions and the subsequent
purification/extension in Claims 7.3–7.5 remain open. Compatibility on every
quadruple of a smaller progression, the eight-term source agreement, the
remaining structure assembly and the final printed numerical comparison
are not yet proved. The five numbered open entries remain. No upstream
code is ported at this checkpoint.

Verification after synchronizing the independent repository updates:
all 26 new named proofs pass individual axiom checks. The full original-data
selected-map production closure compiles across 383 modules. The combined
audit checks 9,169 public Gowers theorems across 5,518 modules (5,516 in the
facade closure), using only `propext`, `Classical.choice`, and `Quot.sound`.
The selected OAI audit closure remains 4,152 modules. The generated catalogue
is byte-identical, with 115 companion proofs and five open statements.
These counts do not certify fidelity to every printed statement. The
selected-port scope check passes; no upstream code or licensing scope is
added at this checkpoint.

### J.148. Quantitative progression bridges and the good-pair image profile

Continuation checkpoint 293, 2026-10-09. Six original modules add 23 named
proofs for the first purification step after J.147's selected maps.

**Progression geometry.** `centered_progression_mem_iff` expresses the
existing OAI centered progression through bounded signed coordinates.
Resizing preserves its generators and rank. Smaller radii give subsets
and inherit properness. Integer shrinking by `m > 0` has cardinality loss
at most `(2*m)^rank`; every `m`-fold sum from the shrinking belongs to the
parent. No primality or positive-modulus hypothesis is needed for these
coordinate statements.

For `x,y` in the quarter shrinking, every `u` in the half shrinking
satisfies `u,u+(x-y)` in the parent. Thus `progressionBridgeSet C (x-y)`
has at least `|C|/4^rank` points, uniformly in the chosen pair. This proves
an explicit version of the geometric abundance needed in Claim 7.3.

**Domains survive cancellation.** `column_quad_image_bridge` combines
relations on `(a,b,v,u)` and `(c,e,v,u)` by subtracting their defects.
It first keeps the spectra of all six indices. The combined image has
size at most `K*J`. Removing the two auxiliary spectra by J.147's
linear-cap theorem gives an endpoint-only relation at half radius with
cap

```
K*J*refinementKernelCap (4*d) (2*d) rho rho.
```

The endpoint defect is proved Freiman-linear on its actual endpoint Bohr
set. Bridge values cancel, but their frequencies are removed only through
that proved range estimate. No vanishing premise or cap-dependent radius
shrink is introduced.

**Failure counting and good pairs.** `columnPairImageFailures` records
bridges whose quadruple image exceeds `K`. Each pair/bridge exception maps
injectively to an additive query of the exact type counted by
`progressionMapImageFailures`. Summing all pair fibres therefore costs no
additional exception mass. Pairs with more than `b` failed bridges satisfy

```
(b+1)*number_of_bad_pairs <= number_of_failed_quadruples.
```

Two pairs of a quarter-progression additive quadruple admit a common good
bridge whenever `4^rank` times their summed failure counts is below the
parent cardinality. `progression_good_pairs_image_relation` then gives the
endpoint half-radius image bound.

**Profile from the selected maps.** Set
`b = |C| / 4^(rank+1)` using natural division. The proved reserve
`4^rank*(2*b) < |C|` includes the small-cardinality case `b=0`.
`progression_image_purification_profile` starts with at most `eta*N^3`
failed additive queries and constructs an exceptional pair set `E` with

```
|E| <= eta*N^3/(b+1).
```

Every additive quadruple in the quarter shrinking whose two pairs avoid
`E` has image cap `K^2*refinementKernelCap (4*d) (2*d) rho rho` on its
endpoint domain at radius `rho/2`. Its only inputs are the proper
progression, local frequency/Freiman data, positive radius/cap, and the
selected-query exception bound. All of those are supplied by J.147's
original-data construction, after restricting local Freiman domains to
the query radius.

This is the good-pair stage of Claim 7.3. Selecting a dense vertex set
with few exceptional incident pairs, removing the pair exception
condition via a second bridge selection, completing eight-term relations,
and the original eight-tuple source agreement remain to be proved. The
five numbered statements stay open, and the final printed numerical
comparison is still required. No upstream code or licensing scope is
added here.

**Verification.** The production profile compiles in a 389-module closure.
The completed combined audit checks 9,244 public Gowers theorems in 5,528
modules, with 5,526 modules in the facade closure. All 23 new named proofs
are included; only `propext`, `Classical.choice`, and `Quot.sound` occur.
The selected OAI audit closure remains 4,152 modules, and the port scope
check passes. The generated catalogue is byte-identical to the tracked
115-companion / five-open ledger, with the existing fidelity qualifications.
Incoming Claim 9.4, common-value Freiman extraction, and subset-sum
independence are included in the same audit. Independent report updates
were merged before verification.

### J.149. All-quadruple purification on a dense original-data core

Continuation checkpoint 294, 2026-10-09. Eight original modules add
28 named proofs. They remove J.148's exceptional-pair condition on a
quantitatively dense vertex core and instantiate the construction from
the original dense bihomomorphism.

**Directed pruning.** `directedExceptionCore D E t` keeps vertices with
both incoming and outgoing exceptional degrees at most `t`. Fibrewise
counting bounds each total degree by `|E|`, even when the prescribed
vertex domain `D` is smaller than the endpoints of `E`. The removal bound
is `(t+1)*|D\\S| <= 2|E|`, with real mass form
`|S| >= |D| - 2|E|/(t+1)`. No symmetry of the exceptional pairs is assumed.

**Candidates away from the boundary.** Nested shrinking composes exactly:
`(Q/m)/n = Q/(m*n)`, including zero factors. Apply J.148's bridge geometry
to `Q/4`: for endpoints `a,c` in `Q/16`, every `y` in `Q/8` has
`y,z=y+(c-a)` in `Q/4`. This restriction avoids assuming a uniform overlap
for extreme boundary differences of the quarter progression.
Set `t = floor(|Q/8|/8)`; the reserve `4t < |Q/8|` includes `t=0`.

**The second bridge.** Each translated exceptional row has cardinality
at most its original degree, since translation is injective. Thus four
rows with degree at most `t` leave a common candidate `y`. For an additive
quadruple `a-b=c-e`, the good relations on `(a,y,c,z)` and `(b,y,e,z)`
subtract to the desired defect on `(a,b,c,e)`. The middle-coordinate
permutations preserve the actual Bohr domain and defect. The second
shared-image bridge removes its auxiliary spectra at another half radius.
All quadruples on the vertex core therefore have endpoint image cap

```
M^2 * refinementKernelCap (4d) (2d) (rho/2) (rho/2),
M = K^2 * refinementKernelCap (4d) (2d) rho rho,
```

at radius `rho/4`. There is no exceptional-pair premise in that conclusion.

**Nonvacuity and mass.** Real quotient lower bounds account for both
natural thresholds `b = floor(|Q|/4^(rank+1))` and `t`. If the parent has
mass at least `delta*N`, the pruning loss is bounded by half the guaranteed
sixteenth-progression mass whenever

```
eta <= delta^3 / (128 * 2048^rank).
```

`exists_dense_progression_all_quad_image_core` then gives a nonempty core
in `Q/16`, of mass at least `delta*N/(2*32^rank)`, with every additive
quadruple controlled on the endpoint-only domain above. Its inputs are the
parent progression, original local frequency/Freiman data, and the selected
quadruple failure bound `eta*N^3`; no structure hypothesis is added.

**Original-data assembly.** For `p = globalColumnProgressionLogDensity alpha`,
let `R = ceil(2 + C_B*(p+1)^4)` and
`delta = exp(-C_P*(p+1)^8)`. Use the uniform accuracy
`eta = delta^3/(128*2048^R)` in J.147's original representative selection.
`global_progression_all_quad_image_core` preserves the original witness
system, witness masses, column data, index-set density, uniform original
four-representation counts, chosen representatives, and both map
normalizations. It constructs the proper progression and nonempty core;
normalized spectra use at most `8d` frequencies. All core quadruples have
the explicit image cap at radius `1/(32*pi)`. The modulus threshold is the
existing selected-map threshold at this chosen accuracy.

The uniform core density `delta/(2*32^R)` satisfies the proved lower bound

```
exp(-(C_P + 94 + 31*C_B)*(p+1)^8).
```

This keeps the same degree-eight exponential density scale as the robust
parent. The extra rank-dependent losses do not introduce another
exponential level.

This completes the all-quadruple part of the purification in Claim 7.4,
on a smaller explicitly dense core. It does not yet prove compatibility
for all additive eight-tuples, progression-indexed difference maps on a
new proper progression, or the original eight-tuple source agreement.
Those obligations and the final printed numerical comparison remain.
The five numbered statements stay open. No upstream modules or licensing
scope are added here.

**Verification.** The original-data global core production closure compiles
across 398 modules. All 28 new named proofs are included in the completed
combined audit: 9,314 public Gowers theorems across 5,538 modules, with
5,536 modules in the facade closure. Only `propext`, `Classical.choice`,
and `Quot.sound` occur. The selected OAI audit closure remains 4,152
modules, and its port scope check passes. The regenerated catalogue is
byte-identical to the tracked 115-companion / five-open ledger, retaining
the existing fidelity qualifications. The incoming Proposition 9.3
iteration, uniform escape argument, and subset-sum invariant changes are
included in the same full audit. Independent reports were merged before
verification.

### J.150. Eight-term compatibility and actual maps on a proper progression

Continuation checkpoint 295, 2026-10-09. Twelve original modules add
31 named proofs. They complete the compatibility part of the Section 7
progression-map transfer from the original dense bihomomorphism.

**Common anchors and the closed chain.** A finite family of translations
charges each missing core vertex at most once. Its common-good candidate
count is at least the candidate cardinality minus the number of shifts
times the core complement cardinality. For an additive eight-tuple,
encoded by four ordered pairs, take the four partial alternating sums.
Every partial sum uses at most six endpoints. Signed-coordinate bounds
show that a common candidate in `Q/32`, translated by any partial sum of
endpoints in `Q/256`, stays inside `Q/16`.

When four times the missing `Q/16` mass is smaller than `|Q/32|`, a common
candidate puts all four chain vertices inside the core. The eight-tuple
index equation closes the chain. Summing its four quadruple defects
cancels the anchor values exactly, while retaining the actual endpoint
and anchor Bohr constraints.

**Images and their domains.** `image_sum_defects_card_le` bounds a finite
sum's image by the product of its summands' image sizes. Four core
quadruples with image cap `H` therefore give eight-column cap `H^4` on the
common domain. The eight-column endpoint defect is Freiman-linear on its
endpoint spectrum, of size at most `8d`. The four auxiliary anchor spectra
have size at most `4d`. Removing them through the linear-cap theorem gives

```
H^4 * refinementKernelCap (8d) (4d) sigma sigma
```

at endpoint radius `sigma/2`. No cancelled anchor frequency is dropped
without that proved removal estimate.

**Reserve enough mass for both extension and difference maps.** The
stronger accuracy

```
eta <= delta^3 / (1024 * 65536^rank)
```

bounds the missing larger-core mass by `delta*N/(16*1024^rank)`. This
reserves four common chain vertices and a later two-point anchor pair.
`exists_progression_all_eight_image_core` constructs a tiny endpoint core
`C = S intersect Q/256`, with mass at least `delta*N/(2*512^rank)`, on which
every additive eight-tuple has the endpoint image bound. The larger core
and its explicit complement bound remain available.

For every `a` in `Q/1024`, a candidate `u` in `Q/512` has `u,u+a` in
`Q/256`. Missing-vertex counting gives at least
`delta*N/(2*1024^rank)` valid anchors in `C`. This is a cardinality bound,
not merely existence of one pair. It preserves the linear-size family
needed for the later original eight-tuple agreement count.

**The final difference maps.** Choose a valid anchor `v(a)` for every
index `a` of the proper progression `P=Q/1024`, and set

```
psi_a(y) = F(v(a)+a,y) - F(v(a),y),
T'_a = T(v(a)+a) union T(v(a)).
```

They use at most twice the original local rank, retain Freiman-linearity,
and vanish at both the vertical origin and index zero. Their quadruple
defect is an eight-column defect from `C`, with the correct signs in the
two negative pairs. The difference-map common domain retains all eight
anchor spectra. Consequently `exists_compatible_difference_progression_maps`
controls every additive quadruple on the whole proper progression, with
no exceptional set or supplied compatibility hypothesis.

**Original-data assembly and uniform bounds.** Use
`R=globalProgressionPurificationRank alpha`,
`delta=globalProgressionPurificationParentDensity alpha`, and
`eta=delta^3/(1024*65536^R)` in the original representative selection.
`global_compatible_difference_progression_maps` retains the original
witness system, witness masses, column data, index density, robust
four-representation families, chosen representatives, and normalized local
maps. It constructs the tiny core, all anchor families, and the actual
proper progression `P` of rank at most `R`. The final maps use at most
`16d` frequencies and are Freiman-linear at the original radius
`1/(4*pi)`. Every additive quadruple has the explicit image cap at
`1/(64*pi)`. Both origin normalizations and the raw tiny-core eight-term
compatibility are retained.

The proper progression has density at least `delta/2048^R`. The proved
comparison `2048=2^11 <= exp(11)` yields

```
delta/2048^R >= exp(-(C_P + 33 + 11*C_B)*(p+1)^8),
```

where `p=globalColumnProgressionLogDensity alpha`. Thus both the
compatibility and shrinking steps remain on the robust parent's
degree-eight exponential density scale.

This proves the compatibility conclusion of Proposition 7.1 in the
original-data cyclic setting. Its agreement with many original additive
eight-tuples is still separate and unproved. That requires enough
alternative original four-representations at the selected vertices; the
current selection guarantees quadruple errors but not that additional
property. The anchor counts proved here supply one of the three factors
needed for an `N^7` source agreement family. The five numbered statements
and the final printed numerical comparison remain open. No upstream code
or licensing scope is added at this checkpoint.

**Verification.** The original-data production closure compiles across
409 modules. All 31 named proofs are included in the completed combined
axiom audit: 9,394 public Gowers theorems across 5,552 modules, with 5,550
modules in the facade closure. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. The selected OAI audit closure remains 4,152 modules,
and its port scope check passes. The regenerated catalogue is
byte-identical to the 115-companion / five-open ledger, retaining the
existing fidelity qualifications. Independent main updates were merged
before the full audit.

**Final merged verification.** The incoming Claim 9.5 twelve-tuple
construction and sharp common-value counting are included in a second
completed combined audit. The final counts are 9,394 public Gowers
theorems in 5,552 modules, with 5,550 facade modules and the unchanged
4,152-module selected OAI audit closure. The catalogue remains
byte-identical at 115 companions and five open statements.

The density comparison in this checkpoint uses the specific parent
parameter `p` supplied by the column sampling construction. It does not
prove that this parameter is polynomial in `log(alpha^-1)`, or that all
initial and final controls meet `milicevicBound D alpha` or the printed
Gowers numerical contract. Those parameter comparisons remain required.

### J.151. Joint selection and a source-agreeing compatible core

Continuation checkpoint 296, 2026-10-09. Fourteen original modules add
28 named proofs. They supply the missing joint representative selection
and retain source agreement on the same core as all-quadruple compatibility.

**Exact replacement counting.** `alternative_coordinate_total` counts
replacements in a finite choice box. Each original bad configuration
contributes exactly one term for each possible unused old coordinate:

```
sum_b number_of_bad_replacements(b,i) = |F_i| * |Bad|.
```

A fixed four-term sum has at most `N^3` representations, by projecting
onto its first three coordinates. Hence configurations with more than
`kappa*N^3/2` bad alternatives at one row have cardinality at most
`(2/kappa)*|Bad|`. Union the four heavy replacement events with the
selected bad 16-tuple event. Their summed query mass is at most
`(1+8/kappa)*|Bad16|`, charged to the same original tuple family by the
injective flattening argument.

**One joint selection.** `exists_joint_progression_representatives`
uses the existing four-coordinate product law to choose one global
assignment with at most `9*|Bad16|/(kappa^5*N^12)` bad distinct-index
queries, for `0<kappa<=1`. All other coordinate products cancel.
Every good query has a good selected original 16-tuple and at least
`kappa*N^3/2` good alternatives in each of its four rows. The factor
`kappa^-5` uses the `N^3` upper bound for the unused row; it is a fixed
local loss, with no power depending on the number of progression points.

`exists_joint_selected_progression_maps` retains the actual valid
representatives, normalized local-map data and index-zero value. It
explicitly marks the at most `6N^2` repeated-index queries. Normalized
quadruple image failures are a subset of the joint exceptional queries.
The full error bound is

```
9*epsilon*N^3/(2*kappa^5) + 6*N^2.
```

**Original alternatives compare with the raw selected maps.** A good
selected 16-tuple and a good row replacement have bounded images on their
actual original domains. Subtract the defects, reversing their order in
the two negative rows. This gives the selected raw four-column map minus
the alternative original four-column map. Its endpoint spectrum has size
at most `8d`; the three remaining selected rows contribute at most `12d`
auxiliary frequencies. Keep those frequencies in the intermediate domain,
then remove them through the linear-cap theorem. The resulting comparison
has image cap

```
K^2 * refinementKernelCap (8d) (12d) (rho/2) (rho/2)
```

on its endpoint-only Bohr set at radius `rho/4`. No reference-map value is
cancelled from a source comparison: these statements use the raw
representation maps, before index-zero normalization.
`query_original_representation_agreement` gives the half-mass family of
actual original alternatives for every coordinate of every good query.

**Original-data joint queries.**
`global_joint_progression_maps_with_source_queries` uses
`epsilon = eta*kappa^5/9`, with the existing condition `N>=12/eta`, to
bound both query events by `eta*N^3`. Its witness system, witness masses,
column data, robust original representation families, progression geometry,
and normalized maps remain linked to the original dense bihomomorphism.
The source comparison holds at `1/(16*pi)`, with its explicit image cap,
for every coordinate of every nonexceptional query.

**Query participation gives good vertices.** A vertex `x` in `Q/16`
and two points `y,z` in `Q/32` form the parent query
`(x,y,z,x-y+z)`. The final point lies in `Q/8`; signed-coordinate bounds
prove all parent memberships. This completion is injective in the three
free points. Therefore vertices with no good query satisfy

```
number_of_bad_vertices * |Q/32|^2 <= number_of_bad_queries.
```

If `|Q|>=delta*N` and there are at most `eta*N^3` bad queries, the vertex
exception mass is at most `eta*4096^rank*N/delta^2`. A vertex with too few
original agreement alternatives belongs only to bad queries. Thus the
same bound controls the actual source-agreement exceptions, rather than
assuming good-vertex participation separately.

**Preserve the anchor reserve while pruning.** The stronger accuracy

```
eta <= delta^3 / (4096 * 4194304^rank)
```

absorbs both the earlier quadruple-core loss and the new source-vertex
loss. `exists_source_agreement_quad_core` retains a single core in `Q/16`
whose missing mass is at most `delta*N/(16*1024^rank)`. Every quadruple
on that core satisfies the prior endpoint image bound, and every core
vertex has at least `kappa*N^3/2` original source-agreement alternatives.

`global_source_agreement_quad_core` chooses that accuracy from the
original density and the uniform rank ceiling. It constructs the actual
core and preserves the original witnesses, representation choices and
normalized map data. The core is nonempty, with density at least the
previous `globalProgressionPurificationCoreDensity`; the stronger pruning
accuracy does not change its proved degree-eight density scale in the
parent parameter. Quadruple compatibility holds at `1/(32*pi)`, and
pointwise raw source comparison at `1/(16*pi)`.

This supplies the joint and vertex source-agreement inputs to the final
map transfer. A full `N^7` family of original eight-tuples still needs to
be assembled from the valid anchor pairs and the two alternative families,
with its map-value and domain identities proved. That assembly must use
this same jointly selected system; the independently chosen system in
J.150 cannot be combined with it merely because both have compatible
maps. The five numbered statements and the final parameter comparisons
remain open. No upstream modules or licensing scope are added here.

**Verification.** The original-data source-agreement core compiles in a
413-module production closure. All 28 new named proofs are included in
the completed combined audit: 9,525 public Gowers theorems across 5,572
modules, with 5,570 modules in the facade closure. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The selected OAI audit closure
remains 4,152 modules, and its port scope check passes. The source ledger
is byte-identical to the 115-companion / five-open catalogue, with the
existing fidelity qualifications. Incoming twelve-tuple iteration, glued
pair maps, final pair/window choices and deterministic assembly tools are
included in the same full audit. No source agreement for an `N^7` family
or final printed bound is inferred from these checks.

### J.152. Full original eight-tuple transfer on the natural domains

Continuation checkpoint 297, 2026-10-10. Twelve original modules add
26 named proofs. The same jointly selected original-data system now
supplies both progression compatibility and the full `N^7` source
agreement family, on the maps' full original-radius domains.

**Distinct original tuples.** `joinSourceRepresentations` concatenates two
original four-term representations, swapping adjacent entries in the
negative block. Its index equation is the difference of the two original
four-sums, and its map value is the difference of their original column
maps. Both the value identity and the endpoint-domain identity are proved.

`sourceEightFamilies` varies `u` over the valid anchor pairs for an index
`a`, then takes one original alternative at `u+a` and one at `u`. Joining
is injective: the eight-tuple determines both four-tuples, and the negative
four-tuple determines `u`. Thus an anchor mass `lambda*N` and two
alternative masses `kappa*N^3/2` give

```
lambda*kappa^2/4 * N^7
```

distinct original additive eight-tuples. No representation multiplicity
or missing factor of `N` is hidden in this bound.

**Image agreement from one system.** The tiny-core eight-term relation
compares the selected difference map at `v(a)` with every other valid
anchor `u`. Use the paired tuple
`[(v+a,v),(u,u+a),(v,v),(v,v)]`. Padding adds no frequency outside the
existing selected-map domain. The normalized reference-map values cancel
in the defect; their frequencies remain in the selected and auxiliary
spectra.

Combine this cross-anchor image bound `J8` with the two actual raw
source comparisons, each of cap `Jsrc`. The endpoint spectrum consists
of the selected-map spectrum and the eight original column spectra, with
size at most `24d`. The variable anchor contributes at most `16d`
auxiliary frequencies. The three-defect image bound and explicit
auxiliary removal give cap

```
Jorig = Jsrc^2 * J8 * refinementKernelCap (24d) (16d) sigma sigma
```

at endpoint radius `sigma/2`, where initially `sigma=1/(64*pi)`.
`original_eight_agreement_mass` proves the mass bound for the actual
agreement predicate, including original index-set membership, the
additive sum, the map values, and the endpoint Bohr domain.

**Preserve the source-agreeing core.** The prescribed-core helpers extend
J.151's actual core to its tiny intersection and choose the final anchors
there. They do not choose another representative system or another core.
`global_original_eight_progression_transfer` constructs the proper
progression `P=Q/1024` and actual normalized maps. It preserves the original
witness system, witness masses, source columns, index density, robust
representation families and chosen representatives. It proves every
quadruple compatible and gives an original agreement family at every
index of `P`.

The uniform agreement density is

```
gamma(alpha) = delta(alpha)*kappa(alpha)^2/(8*1024^R(alpha)).
```

The verified comparison `globalOriginalEightAgreementDensity_lower` gives

```
gamma(alpha) >= exp(-(C_P + 47 + 10*C_B)*(p+1)^8).
```

Here `delta=exp(-C_P*(p+1)^8)`, `kappa=exp(-p)^4/8`, and the integer rank
ceiling has its earlier bound. Powers of two give the logarithmic costs
`512<=exp(9)` and `1024<=exp(10)`. The agreement mass stays on the parent's
degree-eight exponential scale.

**Full natural domains, with no remaining radius loss.** Shrinking every
original column domain would control a smaller set than the natural
intersection used in the sum. `freiman_image_expand_radius` closes this
fidelity obligation. A Freiman-linear map on `B(T;rho)` with image cap `K`
on `B(T;r)` takes at most `ceil(1/r)^|T|*K` values on its entire original
domain. Partition residues by their Dirichlet-cell signatures. Two points
of the same cell have difference in `B(T;r)`; the Freiman equation then
puts each cell's image in one translate of the small-domain image.
There are at most `ceil(1/r)^|T|` signatures.

Every original eight-tuple defect is proved Freiman-linear on the full
endpoint intersection at `rho=1/(4*pi)`. Expand its small-domain image
bound, and expand the quadruple defect similarly. The final uniform cap
is

```
max( refinementCells(1/(64*pi))^(64d) * J8,
     refinementCells(1/(128*pi))^(24d) * Jorig ).
```

`global_original_eight_full_domain_transfer` proves both conclusions on
`1/(4*pi)`: every quadruple of the proper index progression has bounded
image, and every index has at least `gamma(alpha)*N^7` original eight-tuples
agreeing on the full natural intersection of the selected and original
column domains. Both origin normalizations and the `16d` local rank bound
remain. The extra cap factors are independent of the modulus and linear
in the previous caps; the original tuple family is retained.

This completes compatibility and original eight-tuple correspondence in
the original-data cyclic map transfer. The remaining bilinear/variety
assembly and the initial and final parameter comparisons are still
required for the five numbered open statements. A bound in the parent
sampling parameter `p` does not by itself establish the modern
`milicevicBound D alpha` interface or the printed Gowers contract.
No upstream code or licensing scope is added here.

**Verification.** The full-domain original-data transfer compiles in a
434-module production closure. All 26 named proofs are included in the
completed combined audit: 9,683 public Gowers theorems across 5,594 modules,
with 5,592 modules in the facade closure. Only `propext`, `Classical.choice`,
and `Quot.sound` occur. The selected OAI audit closure remains 4,152 modules,
and its port scope check passes. The source ledger is byte-identical to
the 115-companion / five-open catalogue, retaining its fidelity caveats.
Incoming Sanders linear-part/thickening results, Proposition 9.3
prerequisites, single-piece anchor/section/spectrum lemmas and the
linearity-bound correction are included in the same full audit.

### L.2. The raw local inputs cannot have growing width

Continuation checkpoint 298, 2026-10-10. The production module
`Proofs16SmallDomainLocalObstruction` proves nine results auditing the
local inputs of the single-piece lift. These are original proofs using
the existing weighted-energy API; no additional upstream port is used.

The issue is normalization. `HasProductProperty` has denominator the
ambient modulus `N`, whereas `LocalMultilinearPieceAt` measures density
relative to a possibly much shorter box. If every coordinate section has
at most `sqrt(N)` points, **every map** has the unit product property.
Indeed, for a nonempty parallel family, its common test domain `E` has
`|E|^2 <= N`. The support of all simultaneous graph-pair sums has at most
`|E|^2` elements. The existing weighted collision bound gives

```
(sum_E weight)^4 <= N * weightedSimultaneousAdditiveEnergy.
```

This includes arbitrary real weights in the support estimate. The
zero-size parallel family is handled separately by ordinary additive
energy, so no empty-family case is omitted. Consequently arbitrary maps
on an interval box of width `L` have genuine unit product property when
`L^2 <= N`, in every dimension. Unit property also supplies every
parameter `0 <= gamma <= 1`.

Now take dimension one and the quadratic `phi(z) = (z 0)^2`. Over the
prime field, it agrees with any multilinear (hence affine) map at at most
two points, on any partial domain. The proof subtracts the equations at
two roots to obtain `(x-r)*(x+r-a)=0`; all roots lie in `{r,a-r}`.

For any `L >= 1`, place the proper interval box in a prime modulus
`N >= L^2`, and take `B` to be its whole carrier, so its local density is
one. A proper one-dimensional sub-box has cardinality equal to width.
The raw input would therefore imply the necessary budget

```
c(1) * w(1,L) <= 2.
```

`not_localMultilinearPieceAt_of_quadratic` formally refutes the input
whenever this budget fails, for every `0 <= gamma <= 1`. Its positive
density and growing-width specialization cannot be proved, even in
dimension one. `LocalMultilinearPieceAt.unit_density_width_budget` records
the necessary inequality directly. Averaging a relation cover into a
function piece gives the same obstruction for `LocalRelationCoverAt`:
with `Qc(t,1) >= 1`, its controls must satisfy

```
(c(1)/Qc(1,1)) * w(1,L) <= 2.
```

**Scope and next route.** This refutes auxiliary interfaces, not Theorem
16.2 or Gowers's final conclusions. The original global theorem can
discard a small part of ambient space; the short-box example does not
refute that conclusion. The single-piece averaging, capture, remainder
and retiling lemmas remain valid conditional deductions. Their raw local
inputs cannot be discharged with growing-width controls. A usable lift
must construct providers for the actual retained structured slices and
spectrum relation, or derive a suitably normalized local energy input
from the original data. Merely renaming a stronger premise does not
complete that derivation. The numbered targets and their requested
bounds remain unchanged; the ledger remains 115 companions / five open.

**Verification.** All nine named results compile in a 131-module production
closure. After merging the incoming conditional frequency-box reduction,
the full combined audit checks 9,777 public Gowers theorems across 5,599
modules; the facade closure contains 5,597 modules. Only `propext`,
`Classical.choice` and `Quot.sound` occur. The selected OAI audit closure
remains 4,152 modules, and the 4,134-upstream / 17-compatibility port scope
check passes. The source ledger remains byte-identical at 115 companions
and five open statements. The incoming frequency-box theorem is included
in the audit and retains the local inputs refuted here for growing controls.

### J.153. Exact original-data transfer on one proper progression

Continuation checkpoint 299, 2026-10-10. Five original modules add
19 named proofs. Prime-cyclic small-image rigidity turns the completed
original-data map transfer into exact compatibility and genuine exact
source agreement on explicit smaller natural domains. All original
column witnesses, representations, ranks and normalizations are retained.

**Quadruples and original source tuples.** A normalized Freiman defect
with at most `K<N` values vanishes on the same frequency set at radius
`rho/K`. Applied to a bounded quadruple image, this is precisely
`ColumnPairCompatible` for its two difference maps. Applied separately
to every original source eight-tuple defect, it gives
`originalEightExactAgreementSet`: the chosen map equals the alternating
sum of the eight original column maps on the intersection of all their
domains. The same family is retained, with no tuple-count or agreement
density loss. The common positive cap `K0` is the maximum of one and
checkpoint 297's full original-domain cap. The exact modulus bound is
the maximum of the earlier selection bound and `K0+1`.

**Every additive eight-tuple.** On a full progression `P`, exact
quadruples have defect image at most one. The shared-anchor chain gives
bounded eight-tuple defects on `P/256`. Its intermediate domain retains
the anchor constraints. The existing linear-cap theorem removes them
with endpoint budget `8*dpsi` and anchor budget `4*dpsi`, where
`dpsi=16*d` is the chosen-map rank cap. Prime-cyclic rigidity then gives
exact eight-tuple relations on the natural endpoint domains. There is
no iterative local-model packing in this conversion.

Write `rho0=1/(4*pi)` and

```
sigma = rho0/K0,
K8 = refinementKernelCap (8*dpsi) (4*dpsi) sigma sigma,
rExact = sigma/(2*K8),
R = P/256.
```

`K0`, `K8` and `rExact` are positive. Under the explicit maximum of the
earlier exact-transfer modulus bound and `K8+1`,
`global_original_fully_exact_progression_transfer` constructs the same
original-data system and one proper `R` with all of these properties:

- rank at most `globalProgressionPurificationRank alpha`;
- density at least the old difference-progression density divided by
  `512^globalProgressionPurificationRank alpha`;
- exact compatibility for every additive quadruple in `R`;
- exact alternating-map sum for every additive eight-tuple in `R`;
- at every index in `R`, at least
  `globalOriginalEightAgreementDensity alpha * N^7` distinct original
  source tuples agree exactly with the chosen map.

All three exact statements use the common positive `rExact` and their
natural endpoint domains. The local chosen maps remain Freiman-linear
on their full original-radius domains, with both zero normalizations.
Shrinking the index progression changes its density, not the pointwise
source-agreement density or the selected representation system.

**Native interface.** `balancedColumnPairs` swaps the endpoints in the
last two pairs. The index and map-defect identities are proved, and its
frequency union is unchanged. Thus the paired-sum relation becomes
`ColumnDifferenceQuadruple`, and
`column_tuple_respected_of_paired_exact` supplies the existing
`ColumnTupleRespected` predicate with its documented quarter-radius
convention. This bridge keeps the actual endpoint spectra.

**Scope.** This closes exact compatibility and source-agreement inputs
for the progression maps, not the full structural assembly. In
particular, an eight-tuple relation here has eight endpoints; no
sixteen-endpoint or arbitrary-order Freiman relation is asserted. The
new explicit modulus and radius bounds have not been compared with the
printed Gowers thresholds or the deep bound in the original density
parameter. All five numbered targets and their requested bounds remain
open and unchanged. The false raw growing-width local inputs of L.2
are not used. No upstream modules or licensing scope are added.

**Production checks.** The generic exact-agreement source compiles in
a 435-module closure; the first global exact transfer in 450; the
progression eight-tuple extension in 436; the fully exact global
transfer in 452; and the native interface in 551. These closures include
up-to-date dependencies. The completed combined audit includes all 19 new
named proofs and checks 9,818 public Gowers theorems across 5,604 modules;
the facade closure contains 5,602 modules. Only `propext`,
`Classical.choice` and `Quot.sound` occur. The selected OAI audit closure
remains 4,152 modules, and its 4,134-upstream / 17-compatibility scope check
passes. The source ledger remains byte-identical at 115 companions and
five open statements. The incoming local-input retraction is synchronized.

### J.154. Exact sixteen-endpoint coherence and the dense active graph

Continuation checkpoint 300, 2026-10-10. Five original modules add
23 named proofs. The original-data transfer now has native order-eight
Freiman coherence in the index variable, on the actual active fibres,
and a dense exact Freiman bihomomorphism on the active pair graph.
The same original witness system and source-agreement families are kept.

**Closed chain.** A sixteen-endpoint tuple consists of eight pairs. Its
eight consecutive differences define nine prefix vertices. A padded
sixteen-entry signed word bounds every vertex in the full parent
progression when endpoints lie in its `1/256` shrinking. The last vertex
equals the first when the index sum is zero. Thus at most eight
anchor positions are charged, including the starting vertex. Every
quadruple step has the required index equality; the eight map defects
telescope to the original sixteen-endpoint defect. Repeated endpoints
are allowed throughout.

**Natural endpoint domain.** On the intersection with the anchor Bohr
constraints, exact quadruple compatibility makes the defect zero. Its
endpoint rank is at most `16*dpsi`, and its anchor rank at most
`8*dpsi`. `freiman_zero_remove_frequencies` removes all anchor constraints
at the explicit radius

```
sigma/(2*K16),
K16 = refinementKernelCap (16*dpsi) (8*dpsi) sigma sigma.
```

The theorem requires `K16<N`. No temporary anchor frequency is retained
in the final endpoint domain. The cap for eight endpoints is at most
`K16`; the radius and modulus comparisons are proved.

**Native order-eight coherence.** For every fixed argument `y`, the map
`x ↦ psi(x,y)` is a genuine `FreimanHom 8` on

```
R.filter (fun x => y in bohr(Tpsi(x),rExact)).
```

The proof uses finite enumeration of multisets of cardinality eight,
including repetitions. Equal sums become sixteen-endpoint relations.
Only the local domains which actually contain `y` are used; there is
no implicit extension to inactive indices or to a common frequency set.

**Actual dense graph.** Define

```
B = {(x,y) : x in R and y in bohr(Tpsi(x),rExact)}.
```

Its exact cardinality is the sum of its Bohr-row cardinalities. If
`deltaR*N <= |R|` and every local rank is at most `dpsi`, the existing
Dirichlet-cell lower bound gives

```
|B| >= deltaR / ceil(1/rExact)^dpsi * N^2.
```

The density is explicitly positive. The native order-eight property
reduces to order two on each horizontal fibre, and the existing local
Freiman maps handle the vertical fibres. Hence the actual map
`(x,y) ↦ psi(x,y)` on `B` satisfies `IsEBihomomorphism B psi {0}`. This is
a constructed domain and map, not an assumed extraction contract.

**Global integration.** `global_original_sixteen_endpoint_transfer`
constructs one original-data system and a proper `R=P/256` with all of
the preceding fields. It uses

```
sigma = (1/(4*pi))/K0,
rExact = sigma/(2*K16),
N >= max(originalExactTransferModulusBound(alpha),K16+1).
```

Both the progression density and the original pointwise
`globalOriginalEightAgreementDensity alpha * N^7` source family are
unchanged from checkpoint 299. Quadruple, eight- and sixteen-endpoint
compatibility, native order-eight fibres, dense graph and exact source
agreement use one common positive radius. Full original-radius local
Freiman data, original column witnesses, representations, anchors and
both zero normalizations remain in the conclusion.

**Scope.** The compatibility input now includes sixteen endpoints, so
the missing order-eight index identity of J.153 is supplied. Structural
assembly, coherence on retained chart windows and final quantitative
comparisons remain separate. In particular, the new active graph must
not be confused with a proved global-to-local cover or with agreement of
the original bihomomorphism on a final Bohr variety. The five numbered
targets remain open, with their requested bounds unchanged. The false
raw local hypotheses of L.2 are not used. No new upstream port or
license scope is introduced.

**Production checks.** The chain source compiles in a 437-module closure;
the sixteen-endpoint relation in 438; the native fibre interface in 439;
the active graph in 440; and the complete global integration in 457.
The completed combined audit includes all 23 new named proofs and checks
9,860 public Gowers theorems across 5,609 modules; the facade closure has
5,607 modules. Only `propext`, `Classical.choice` and `Quot.sound` occur.
The selected OAI audit closure remains 4,152 modules, and its
4,134-upstream / 17-compatibility scope check passes. The source ledger
remains byte-identical at 115 companions and five open statements.
Independent incoming reports and polylogarithm updates are synchronized.

### J.155. Complete and recenter the active chart windows

Continuation checkpoint 301, 2026-10-10. Seven original modules add
27 named proofs. This supplies a coherent common-domain chart construction
from dense order-eight chart domains and a good quadruple family tested
on its actual active frequencies. The original chart domains need not
intersect, and inactive original values are not forced to agree.

**Stronger active assembly.** `milicevic_prop_9_3_active_domains` retains
Proposition 9.3's numerical window, map-family and quadruple bounds, with
local-map and quadruple tests on the indices active at each individual
vertex. `twelve_good_respected_active` proves that the good twelve-tuple
split needs only these active values. The legacy full-window conclusion
alone would be too weak to change inactive frequencies afterwards.

A completed window which agrees with every active value still imposes
every original active constraint, even if its other values change. Hence
it preserves the glued maps' local Freiman data and all good quadruple
identities. The completed windows retain the original fixed frequencies
when there is an existing fixed base.

**Cell completion.** Given a chart `theta_i` on `D_i` and its Sanders
linear part `psi_i`, choose a base in `D_i ∩ C` when that intersection is
nonempty. Otherwise choose a base in the cell and use zero offset. Set

```
completed_i(x) = offset_i + psi_i(x-base_i).
```

This agrees with `theta_i` on `D_i ∩ C` and is Freiman-linear on all of
`C` when cell differences lie in the linear part's Bohr domain. Even an
empty active intersection uses the same slope `psi_i`. After recentering
at any `t` in the cell,

```
completed_i(x) = completed_i(t) + psi_i(x-t).
```

No agreement is asserted for an inactive original chart value.

**Common Sanders data.** For `ell` chart domains of density at least
`exp(-p)`, with genuine `FreimanHom 8` maps and `p>=0`, the proved
`sanders_linear_part` theorem supplies all linear parts on one domain:

```
rho = exp(-C*(p+1))/(2*pi),
|Gamma| <= ell*(1+C*(p+1)^4),
C = quarticBogolyubovConstant.
```

Only the linear-part Bohr sets are intersected. No intersection of the
original `D_i` is used. Dirichlet signatures with `M >= 4/rho` give
`M^|Gamma|` cells whose differences lie in `B(Gamma;rho/4)`. The completion
and Freiman-linearity proofs include empty cells.

**Choose cells for good quadruples.** A four-cell pattern retains at least
`1/M^(4*|Gamma|)` of the already-good quadruples. Choose one retained
quadruple `t` as the translation. Recenter each row by its own `t_j`, then
apply the existing row-label selection, so the resulting maps form one
function of the recentered point rather than conflicting coloured values.
The retained quadruples still realize original members of the good family.
There is no attempt to choose one dense cell first and then bound errors
inside it.

Every recentered point lies in `B(Gamma;rho/4)`. The chart offsets at the
four translation points become a fixed frequency base `B'` with

```
B subset B',   |B'| <= |B|+4*ell.
```

On `B(B' union {psi_i(u)};eta/2)`, all original active constraints at the
source point `t_color(u)+u` hold. This preserves the original local map,
its value at zero, and the quadruple identity. The variable maps `psi_i`
are normalized native `FreimanHom 2` maps on the common Bohr domain.

**Uniform numerical wrapper.** Put

```
D = ceil(ell*(1+C*(p+1)^4)),
M = ceil(1/(rho/4)),
lambda = kappa/(512*M^(4*D)).
```

`exists_coherent_completed_sanders_charts` requires
`8 <= (kappa/M^(4*D))*N` and `kappa*N^3` good original quadruples. It
constructs a common Bohr family with rank at most `D`, a retained vertex
set of size at least `lambda*N`, and at least `lambda*N^3` respected
quadruples. The source-index translations are recorded explicitly;
source agreement at `t_color(u)+u` must not be silently relabelled as
agreement at the unshifted index `u`.

**Scope and next input.** This proves the chart-completion and common-
domain recentering step under ordinary dense Freiman chart data and
active tests, without a new structural-existence hypothesis. The
strengthened Proposition 9.3 provides the active tests, but its current
output does not yet record a uniform density lower bound for every
`D_i`. That bound must be retained from the actual chart-selection
construction before applying the uniform Sanders wrapper to all of its
charts. Applying the global frequency iteration to the actual retained
progression, subsequent structural assembly, original-bihomomorphism
agreement and final printed-budget comparisons remain separate. All
five numbered targets remain open and unchanged. No raw growing local
input or newly ported upstream module is used.

**Production checks.** The affine completion source compiles in 165
modules; active glue in 458; the strengthened Proposition 9.3 in 462;
Sanders cells in 166; recentered frequency domains in 534; chart
localization in 535; and the uniform Sanders wrapper in 536. The combined
axiom audit includes all 27 new named proofs and checks 9,939 public
Gowers theorems across 5,618 modules, with a 5,616-module facade closure.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The selected
OAI audit closure remains 4,152 modules, and its 4,134-upstream /
17-compatibility scope check passes. The 115-companion / five-open source
ledger is byte-identical. The incoming global-to-local provider calculus
and repaired single-piece lift are included in the same audit.

### J.156. Dense frequency iteration and coherent Proposition 9.3 output

Continuation checkpoint 302, 2026-10-10. Eight original modules add
20 named proofs. The uniform chart-domain density needed by J.155 is
now retained from the actual extraction and through the full iteration.
The resulting active Proposition 9.3 output feeds the coherent common-
domain construction without a new chart-density assumption.

**Derive domain density.** Each Claim 9.4 or 9.5 extraction supplies a
pair support `P` of size at least its claim density times `N^2`, with
every second coordinate in the new domain `B`. At most `N` pairs carry
each value, hence `|B| >= delta*N`. The deterministic append keeps all
older domains unchanged and installs `B` only at the new index. The
stronger append records every domain density and the same exact
potential increase `|P|`.

Take the common lower bound

```
delta = min(claimNineFourDensity eps R d,
            claimNineFiveDensity eps R d).
```

Both rounds carry `delta*N <= |D_i|` at every constructed index. The
finite-potential termination theorem retains this field, alongside its
original bad-triple, bad-twelve-tuple and family-size bounds:

```
ceil(delta*N^2)*m <= N^2*s0,
therefore m <= ceil(s0/delta).
```

`milicevic_prop_9_3_dense_active_domains` records the same density in the
actual assembled output, with the active-domain tests of J.155 and all
existing numerical counts unchanged.

**Finite windows and padding.** Reindex the chosen finite `J` as
`Fin J.card`. At indices below `m`, use the original domain and map.
Other indices are inactive everywhere in the retained set; replace them
by zero maps on the full domain. This gives a genuine dense order-eight
chart family even when the common window contains padding. Its active
frequency image is proved exactly equal to the original active image.
No active value is changed, and no inactive original value is forced
to agree. Put `p=max(0,log(1/delta))`; then `p>=0` and `exp(-p)<=delta`.

`complete_dense_index_window_charts` consumes these proved fields and
constructs the common Sanders charts. It retains the original fixed
frequencies, source maps, good quadruples and source-index translations.

**Uniform good-quadruple density.** Let `a` be Proposition 9.3's original
quadruple coefficient, and set

```
W = choose(ceil(s0/delta)+8*s0, 8*s0),
kappa = (a/2)/W.
```

`W>0`. If `12<=a*N`, the `6*N^2` repeated-index term costs at most half
of `a*N^3`. The N-independent family-size bound and binomial monotonicity
then give at least `kappa*N^3` good quadruples in the selected window.
This uses the original good-family count before chart localization,
without a new error estimate after selection.

**Coherent Proposition 9.3.** `milicevic_prop_9_3_coherent_charts` starts
from the standard column-map, rank, iteration and almost-all-relation
inputs. In the positive-coefficient regime, with the explicit conditions

```
12 <= a*N,
8 <= (kappa/coherentChartCells(p)^(4*coherentChartRankCap(8*s0,p)))*N,
```

it constructs the original active selection plus one coherent chart
family. Its common Bohr rank is at most
`coherentChartRankCap(8*s0,p)`, its fixed frequency set has cardinality
at most `32*s0`, and both retained vertex and quadruple densities are
at least `coherentChartDensity(kappa,8*s0,p)`. The varying maps are
normalized native Freiman 2-homomorphisms on one common Bohr domain;
the retained vertices lie in its quarter-radius subset. Every local
map is the original chosen glued map at the recorded source index
`t_color(u)+u`, and every retained quadruple realizes an original good
active quadruple. Relating back to the original column differences is
retained. The extra chart-domain density is constructed, not assumed.

**Scope and next application.** This closes the missing density bridge
and constructs the common-domain coherence output under Proposition
9.3's stated ambient input conditions. The exact original-data transfer
of J.154 has a retained progression; its local anchor candidates and
relative error counts must be used to supply a suitable localized
selection, rather than silently assuming N/2 good global columns or
applying an ambient error bound to a small retained set. Subsequent
structural assembly, original-bihomomorphism agreement and final printed
Gowers budget comparisons remain open. All five numbered targets are
unchanged. No raw growing local input or new upstream port is used.

**Production checks.** The append and both rounds compile in a
176-module closure; the dense iteration in 177; the dense active
assembly and finite-window modules together in 574; completion in 538;
the uniform quadruple budget in 538; and the coherent Proposition 9.3
in 577. The completed combined audit includes all 20 new named proofs
and checks 9,985 public Gowers theorems across 5,627 modules, with a
5,625-module facade closure. Only `propext`, `Classical.choice` and
`Quot.sound` occur. The selected OAI audit closure remains 4,152 modules,
and its 4,134-upstream / 17-compatibility scope check passes. The source
ledger is byte-identical at 115 companions and five open statements.
The incoming global-cover frequency-box reduction and independent
repository updates are included in the same audit.
