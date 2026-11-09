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
  steps the auxiliary index linearly by `lcm(4n₀f, 4I)`. It needs two new lemmas: a
  `mod 4ρ²` quotient congruence, and `v_p(n₀) ≤ v_p(I)`.

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

* **Soundness:** the main index; the first index, including an alternating residue for
  `X < 0`; the ratio bound; the projector, including the negative-base congruence for odd `R`;
  orientation, including `q > 0`; the sharpened half-binomial; and the `LeafFacts` assembly.
* **Completeness:** the canonical data and their parities; the cone calibration
  `q ≤ 2·cone·F ≤ 3q`; the guard Pell pair; the interpolation lemmas; and assembly.
* The endpoint `IntegerModelBridge`, then the short 840/108 form.
