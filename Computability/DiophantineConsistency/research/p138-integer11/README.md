# Package 138's eleven-integer equation (924/107): Lean route (in progress)

This record tracks the iPRA endpoint of package 138's equation
[`parity_saturated11_native.json`](../../con-zfc-diophantine-forms/138-semantic-signs/integer11/parity_saturated11_native.json).
The equation has eleven unknowns over ℤ, degree 924 and 107 operations. Its proof is in
[`PROOF.md`](../../con-zfc-diophantine-forms/138-semantic-signs/integer11/PROOF.md), whose parent is
`132-signed-caps-free-scales/integer_lowops/PROOF.md`. The modules live in
`Lean/DiophantineConsistency/P138/`.

The sentence is the ℤ convention of [`zrows-toolkit`](../zrows-toolkit/README.md):
`nativeNoZero (signedSplit e)`. The endpoint therefore needs `IntegerModelBridge e`: in every
model of `𝗜𝚺₁`, `e` has a zero in `DiffRing V` iff machine 215 halts internally.

## Route

* **Soundness:** an integer zero gives a positive valuation `![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]`
  of `CompactLeafFacts.LeafFacts` at `Source34Ports.ports`, where `α = q − F − C` and
  `ζ = k − η`. Then `Source34Converse.halt_iff_facts` gives halting. Lean's `ycoord n a`
  has discriminant `(a+1)(a+3)`, so package 138's main base `A = a + 2` is exactly the
  `ycoord` convention.
* **Completeness:** from `Source34Seeds.halt_first_gamma` (canonical data), using
  `ModelPellExistence` for the guard and `Intersective19.root` for the residue. Interpolation
  steps the auxiliary index linearly by `4·I·f·w`, where `n₀ = g·w` with `g ∣ I` and `w`
  coprime to `I` (see `zrows-toolkit`, stage 3).

## Built (9 November 2026)

| Module | Content |
|---|---|
| `P138Ports` | `coneA = 2^1113`, `coneB = 2^666104`, `ports6`; `PortFacts` (the port facts the proofs use) and `portFacts` |
| `P138Value` | `value`, the register record `Regs`, and `value_eq`: identity (4) of PROOF.md, `Q(Z² − RG·V²) + (RG − Z²) = (Q−1)Z² − RG(QV²−1)`, proved at register level |
| `P138Syntax` | `literal`, generated node for node from the JSON; `evalRing_literal`; `literal_zero_iff` |
| `P138Bootstrap` | facts that need no zero: residues of `q, X, A, H, Dt`, `Budget ≡ 0, 12 (mod 16)`, `P ≡ 1 (mod 4)`, nonvanishing of `BP, Df, δ, Cy` |
| `P138NoRoot` | `z³ ≠ 19h³` for `h ≠ 0`, `Ac ≠ 0`, and `s, r ≠ 0` at a zero |
| `P138Squares` | pairwise Bezout relations among `BP, Df, Da`; `(δZ)² = S²·BP·Df·Da`; positive square roots `p₀, f, e` |
| `P138Budget` | `12 ≤ Budget`; centered signs and cone bounds; `|k|(2|Y|−1) < 2|c| < |k|(2|Y|+1)` |
| `P138Window` | the signed packing window `|q|(q²−1) < R < q⁴ − 2`; `3R+1 < |E|`, `R+1 ≤ |k|` |
| `P138Adjacent` | the auxiliary root is integral (`e = δy`), via `quotient_of_scaled_norm` |
| `P138EarlyFold` | the record `EarlyFold`: the strong pair, the odd auxiliary index, residues, and the main root `|c| = ψ`, `Dm = χ²` at an odd index; the guard split `Dt = τ²`, `Dg = g²`; `S ∣ Ac`; `H ∣ Kq⁵` |
| `P138Rank` | the record `MainIndex`: `R = ι Rn`, with `Rn` odd the index of the main root (`cn = ψ_b(Rn)`, `Dm = χ²`, `2Rn < cn`) |
| `P138FirstIndex` | the record `FirstIndex`: `2n = R + 1` for both signs of `X`, using a new alternating residue for the negative first base; `k = ±2ψ_bF(n)` |
| `P138Ratio` | `|H| ≥ |X|(2|Y|+1)`, and `H_large`: `xn·(xn−3)^t < |H|` when `R = 2t+1` |
| `P138Projector` | the negative-base congruence `neg_projection_odd`; the fifth-power height bound; `projector`: `σX = 2^R` and `x₈ = σ·cn` with `σ = ±1`, for either sign of the main base |
| `P138Orientation` | `q > 0` (because `2^N − 1 ∤ 2^m + 1`), and the record `Oriented`: positive `J, F, C, α, Y`, `X = 2^R`, `c = ψ` |
| `P138HalfBinomial` | the sharpened upper sandwich, and `eta_pos`: `kY < c`, so `η > 0` |
| `P138Leaf` | `leaf_of_zero`: positive `LeafFacts Source34Ports.ports` at `![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]`; and `sound`: a zero gives an internal halt of machine 215, through `Source34Converse.halt_iff_facts` |

**Soundness is closed.** In every model of `𝗜𝚺₁`, a `DiffRing` zero of `value portsR` gives an
internal halt. Together with `P138Syntax.literal_zero_iff`, this is the forward half of
`IntegerModelBridge`.

Completeness, first layer:

| Module | Content |
|---|---|
| `P138Quarter` | the canonical `4η < k`, from a quartered sandwich slack and `4v < D` in the central split |
| `P138Kernel` | `c0 = 105534389824824194647382298625`, the radix-`ρ` digit of the lower kernel at 5495 (kernel `decide` on the sparse list, `ρ` never evaluated); `c0·ρ^5495 ≤ lower < (c0+1)·ρ^5495` |
| `P138Cone` | the cone calibration `q ≤ 2·coneA·F ≤ 3q` and `q ≤ 2·coneB·C ≤ 3q`, for every packed halt word |
| `P138Canonical` | the record `Canonical`: every canonical quantity from a halt, with the parities `J ≡ 1 (mod 6)`, `W ≡ 4 (mod 12)`, `sY` odd, `R ≡ c ≡ 3 (mod 4)`, and `H ∣ K`. Also `Matches` and the register bridge, `2·Derr ≤ q²`, `q²k² < 4·Budget` and `Budget > 64` |
| `P138Guard` | the guard Pell pair `g² = 1 + Dn·τ²·s²` with `Dn = Budget − 4`, and `P = (τg)²`, `BP = (dτg)²` |
| `P138Interp` | `interp`: from the canonical data and the guard, `r` with `s ∣ r` and `f`, such that for every target `a₀` there are `T ≡ a₀ (mod s·r)` and `y` with `Df = f²` and `QV² − (Q−1)y² = 1`; it uses `ZRowsLinearInterpolation.supported_interpolation` with `N = 4·s·A·p₀·c²` |

[`tools/gen_literal.py`](tools/gen_literal.py) generates `P138Syntax.lean`. With `--check`, it
confirms:

* the regeneration is byte-identical;
* the Lean literal matches the pinned JSON node for node;
* the JSON output equals PROOF.md (1) numerically modulo `2^127 − 1`;
* six mutation controls are rejected.

Every module was re-elaborated serially with no errors. Axioms are within `propext`,
`Classical.choice` and `Quot.sound`. The ports beta, K0, MC and MF are `Source34Ports.ports`, as in
[`source34-calibration`](../source34-calibration/README.md). The cones are bound to the values
PROOF.md states, which are also the `cone_A`/`cone_B` payloads that `source34-calibration`'s
`check_recipe.py` reproduces.

## Remaining

* **Completeness:** the assembly. It takes the residue root `a₀` of `π(·+κ)` modulo `s·r` from
  `Intersective19.root`, sets `n = (Ac + S·p₀·f·y)/S`, and concludes with `value_eq`, at the
  unknowns that `P138Canonical`'s header lists.
* The endpoint `IntegerModelBridge`, then the short 840/108 form.
