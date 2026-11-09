# Package 138's eleven-integer equations (924/107 and 840/108): iPRA endpoints (closed)

This record documents the iPRA endpoints of package 138's two equations,
[`parity_saturated11_native.json`](../../con-zfc-diophantine-forms/138-semantic-signs/integer11/parity_saturated11_native.json)
(eleven unknowns over ℤ, degree 924, 107 operations) and its short form
[`parity_saturated11_short.json`](../../con-zfc-diophantine-forms/138-semantic-signs/integer11/parity_saturated11_short.json)
(degree 840, 108 operations). They differ only in the index modulus of
`k = R + 1 + h·M_index`: `M_index = E` (native), `M_index = 4q⁴` (short). Their proof is in
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

### One circuit, two `k`

`P138Value.regsK p x κ` is the circuit with the `k` register supplied as a parameter `κ` (no
other register reads `h = x 3`). The native form is `regs = regsK · · kN`, `kN = 1 + R + hE`;
the short form is `regsS = regsK · · kS`, `kS = 1 + R + h(q²(q²·4))`. The soundness chain
`P138Bootstrap` … `P138Leaf` is stated for an arbitrary `κ`. It uses `k`'s definition at one
point only, the hypothesis `P138Window.IndexModulus p x κ`: `κ = R + 1 + hμ` with `μ ∣ E` and
`4q⁴ ≤ |μ|`. Both forms satisfy it (`native_modulus` with `μ = E`, `short_modulus` with
`μ = 4q⁴`). From the window `R + 2 < q⁴`, `P138Window.modulus` gives a natural `m = |μ|` with
`m ∣ E`, `m ∣ k − (R + 1)` and `3R + 1 < m`. `P138FirstIndex` runs its first-index argument
modulo this `m`: residues of `ψ_bF(n)` (since `m ∣ E ∣ XY²`), the alternating residue for a
negative first base, and no wrap. That gives `2n = R + 1` for either form.

Completeness of the short form is a substitution. `E = 4q⁴(3w+1)(2v+1)`, so
`P138Value.valueS_update` proves, as a polynomial identity, that the short value with
`h ↦ h(3w+1)(2v+1)` is the native value. The native zero of `P138Complete.complete`
therefore gives a short zero (`P138Short.complete`).

## Built (9 November 2026)

| Module | Content |
|---|---|
| `P138Ports` | `coneA = 2^1113`, `coneB = 2^666104`, `ports6`; `PortFacts` (the port facts the proofs use) and `portFacts` |
| `P138Value` | the register record `Regs`; `regsK`/`valueK` with the `k` slot as a parameter; the native `regs`/`value` (`kN`) and the short `regsS`/`valueS` (`kS`); `value_eq`: identity (4) of PROOF.md, `Q(Z² − RG·V²) + (RG − Z²) = (Q−1)Z² − RG(QV²−1)`, proved at register level; `regsK_update` and the transfer `valueS_update` |
| `P138Syntax` | `literal`, generated node for node from the JSON; `evalRing_literal`; `literal_zero_iff` |
| `P138Bootstrap` | facts that need no zero: residues of `q, X, A, H, Dt`, `Budget ≡ 0, 12 (mod 16)`, `P ≡ 1 (mod 4)`, nonvanishing of `BP, Df, δ, Cy` |
| `P138NoRoot` | `z³ ≠ 19h³` for `h ≠ 0`, `Ac ≠ 0`, and `s, r ≠ 0` at a zero |
| `P138Squares` | pairwise Bezout relations among `BP, Df, Da`; `(δZ)² = S²·BP·Df·Da`; positive square roots `p₀, f, e` |
| `P138Budget` | `12 ≤ Budget`; centered signs and cone bounds; `|k|(2|Y|−1) < 2|c| < |k|(2|Y|+1)` |
| `P138Window` | the signed packing window `|q|(q²−1) < R < q⁴ − 2`; `IndexModulus`, `native_modulus` (`μ = E`), `short_modulus` (`μ = 4q⁴`); `modulus`: `m ∣ E`, `m ∣ k − (R+1)`, `3R+1 < m`; `k_ge`: `R+1 ≤ |k|`; `R_ge`: `4080 ≤ R` |
| `P138Adjacent` | the auxiliary root is integral (`e = δy`), via `quotient_of_scaled_norm` |
| `P138EarlyFold` | the record `EarlyFold`: the strong pair, the odd auxiliary index, residues, and the main root `|c| = ψ`, `Dm = χ²` at an odd index; the guard split `Dt = τ²`, `Dg = g²`; `S ∣ Ac`; `H ∣ Kq⁵` |
| `P138Rank` | the record `MainIndex`: `R = ι Rn`, with `Rn` odd the index of the main root (`cn = ψ_b(Rn)`, `Dm = χ²`, `2Rn < cn`) |
| `P138FirstIndex` | the record `FirstIndex`: `2n = R + 1` for both signs of `X`, modulo the index modulus `m` (`E` or `4q⁴`), using a new alternating residue for the negative first base; `k = ±2ψ_bF(n)` |
| `P138Ratio` | `|H| ≥ |X|(2|Y|+1)`, and `H_large`: `xn·(xn−3)^t < |H|` when `R = 2t+1` |
| `P138Projector` | the negative-base congruence `neg_projection_odd`; the fifth-power height bound; `projector`: `σX = 2^R` and `x₈ = σ·cn` with `σ = ±1`, for either sign of the main base |
| `P138Orientation` | `q > 0` (because `2^N − 1 ∤ 2^m + 1`), and the record `Oriented`: positive `J, F, C, α, Y`, `X = 2^R`, `c = ψ` |
| `P138HalfBinomial` | the sharpened upper sandwich, and `eta_pos`: `kY < c`, so `η > 0` |
| `P138Leaf` | `leaf_of_zero_k`: positive `LeafFacts Source34Ports.ports` at `![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]` at any `k` slot with an index modulus; `sound_k`: a zero gives an internal halt of machine 215, through `Source34Converse.halt_iff_facts`; the native `leaf_of_zero` and `sound` |

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

[`tools/gen_literal.py`](tools/gen_literal.py) generates `P138Syntax.lean` (native) and, with
`--form short`, `P138ShortSyntax.lean`. With `--check` (both forms unless `--form` is given), it
confirms for each form:

* the JSON's pinned SHA-256 and operation counts;
* the regeneration is byte-identical;
* the Lean literal matches the pinned JSON node for node;
* the JSON output and the parsed literal equal PROOF.md (1) numerically modulo `2^127 − 1`,
  with `M_index = E` or `4q⁴`;
* seven mutation controls are rejected, among them the other form's index modulus.

With both forms it also checks the transfer `short(h(3w+1)(2v+1)) = native(h)` numerically.

Every module was re-elaborated serially with no errors. Axioms are within `propext`,
`Classical.choice` and `Quot.sound`. The ports beta, K0, MC and MF are `Source34Ports.ports`, as in
[`source34-calibration`](../source34-calibration/README.md). The cones are bound to the values
PROOF.md states, which are also the `cone_A`/`cone_B` payloads that `source34-calibration`'s
`check_recipe.py` reproduces.

## Endpoint

| Module | Content |
|---|---|
| `P138Complete` | `complete`: an internal halt gives a `DiffRing` zero of `value portsR`. The residue root `a₀ = t − κ` comes from `Intersective19.root` at `s·r`, and `n = H⁴e₀ + p₀·f·y` makes `Z = S·p₀·f·y`; the proof then closes by `value_eq_product`, with no division |
| `IPRAInteger138` | `expression` (the literal at `ports6`), `bridge : IntegerModelBridge expression`, and `native_equivalence`, `standard_equivalence`, `reference_equivalence` |
| `P138ShortSyntax` | the short literal, generated node for node from `parity_saturated11_short.json`; `evalRing_literal` (to `valueS`); `literal_zero_iff` |
| `P138Short` | `sound`: the generic soundness chain at `κ = kS` with `short_modulus`; `complete`: the native zero with `h ↦ h(3w+1)(2v+1)` (`valueS_update`) |
| `IPRAInteger138Short` | the same three endpoints for the 840/108 `expression` (the short literal at `ports6`) |

The three endpoints say that the native, standard and equality-only iPRA theories each prove
`nativeNoZero (signedSplit expression)` equivalent to `∼mappedNativeRefutation embedding`,
the Foundation ZFC consistency predicate: the equation has no integer zero iff Con(ZFC). The
equality-only theory proves the order-erased form. This holds for each of the two equations.

[`tools/check_ports138.py`](tools/check_ports138.py) binds the six ports. In both JSONs the port
leaves are nodes 11–16, symbolic `["coefficient", name]` in the same order, and
`coefficient_binding` names `coefficients/BINDING.json`; the checker verifies this for each.
It follows `RESTORED_DEPENDENCIES.json` to the restored binding and the six payloads, and verifies each pinned SHA-256, byte count and bit count. It
then evaluates `ports6` from a verbatim-checked transcription of the Lean definitions and
compares it with the payloads, and it rejects six mutation controls.

## Remaining

Nothing for package 138: both forms are closed.
