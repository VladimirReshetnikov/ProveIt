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
  (D/e)^D·(2·10⁸)^D ≲ 2^(2^512). That holds for every D up to about
  2^500, and the paper's O(1) is certainly far below that.
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
formalizing the paper is the only way to discharge it. The work starts with
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
- Next: step 2 proper ([49] Lemma 19 and Corollary 20): random selection
  f(y) ∈ U_y, averaging, then Corollary 7.6 + Lemma 7.8 in place of
  Theorem 17.

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
Discharging `MilicevicDeepVarietyStructure` is therefore months of work,
not a session. Per J.5, polynomial rather than quasi-polynomial bounds
would still fit Theorem 16.2's budget, so a weaker-bound formalization
(classical Bogolyubov, Gowers's Freiman lemma in `Proofs07BohrHom`) is
a legitimate shortcut wherever it applies.

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
