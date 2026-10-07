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
