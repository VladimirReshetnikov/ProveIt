# Package 172's eleven-integer equations (298/146 and 300/144): iPRA endpoints (closed)

This record documents the iPRA endpoints of package 172's two equations,
[`integer11_degree298_ops146.json`](../../con-zfc-diophantine-forms/172-pooled-powers-round21/part2/ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/integer11/integer11_degree298_ops146.json)
(eleven unknowns over ℤ, degree 298, 146 operations) and
[`integer11_degree300_ops144.json`](../../con-zfc-diophantine-forms/172-pooled-powers-round21/part2/ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/integer11/integer11_degree300_ops144.json)
(degree 300, 144 operations). They are the two lowest-degree points of the eleven-integer row.
Their proof is the package's
[`PROOF.md`](../../con-zfc-diophantine-forms/172-pooled-powers-round21/part2/ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/integer11/PROOF.md).
The proof modules live in `Lean/DiophantineConsistency/LinCof/` and the syntax and endpoint
modules in `Lean/DiophantineConsistency/P172/`.

The sentence is the ℤ convention of [`zrows-toolkit`](../zrows-toolkit/README.md):
`nativeNoZero (signedSplit e)`. The endpoint therefore needs `IntegerModelBridge e`: in every
model of `𝗜𝚺₁`, `e` has a zero in `DiffRing V` iff machine 215 halts internally. The unknowns
`j C z h r v w T c n s`, the six ports `beta K0 MC MF cone_A cone_B` (`P138Ports.ports6`, the
source34 tuple) and the canonical halt data are those of
[package 138](../p138-integer11/README.md).

## One circuit, five slots

Both equations are one register circuit, `LCValue.regsK p x κ ω Λ ψ wt`, over any commutative
ring. It is called *linear-cofactor* because the strong cofactor is `B = r·A·Dm`, linear in the
unknown `r`. Five registers are supplied as parameters:

| Slot | Register | 298/146 | 300/144 |
|---|---|---|---|
| `κ` | the index `k` | `k298` | `k300` |
| `ω` | `kq2` | `kq298` | `kq300` |
| `Λ` | `L` | `L298` | `L300` |
| `ψ` | the centre `Psi` | `psi298` | `psi300` |
| `wt` | the radical weight in `pc = wt·S²·B·Df·Cy` | `1024` | `1024` |

The proofs use the slots only through three hypotheses:

* `SlotLaw p x κ ω Λ e`: `kq2 = k·q^(2+e)` and `L = X·Y²·k` (`slotLaw298` with `e = 0`,
  `slotLaw300` with `e = 1`);
* `LCWindow.IndexModulus`: `k = R + 1 + hμ` with `μ ∣ X·Y²` and the conditional size bound
  `|q|^(2+e) < |Y| → 4q⁴ ≤ |μ|` (`modulus298`, `modulus300`, for every `ψ` and `wt`);
* `LCNorm.Weight wt`: `wt` is a nonzero even square (`weight1024`; also `weight64`, `weight4`,
  for the sibling points of packages 144 and 135).

Completeness needs, in addition, that the centre does not read `x 9 = n`, and it takes the
weight as `wt = lw²` for an arbitrary ring element `lw`.

## Route

* **Soundness:** an integer zero gives the two-radical norm equations `P = g²`,
  `δ(Z − S·g) = l·S·w`, `w² = B·Df·(δ·Cy)` (`wt = l²`), then square roots of the coprime factors,
  the budget and window bounds, the index modulus, the first index `2n = R + 1`, the projector
  and the orientation `q > 0`. New against package 138: `Y` is a free unknown, so the scale
  `Y = (2t + 1)·q³` is recovered at a zero (`LCScale`), from `M ∣ H·(Y − q³)` with `M = 2q³` a
  power of two and `H` odd. The result is a positive valuation of `CompactLeafFacts.LeafFacts`
  at `Source34Ports.ports`, and `Source34Converse.halt_iff_facts` gives halting.
* **Completeness:** from package 138's canonical record `P138Canonical.Canonical`, unchanged.
  The guard `Budget − 4` is `≡ 12 (mod 16)`, hence not a square, and `ModelPellExistence` gives
  the guard pair. The strong pair needs `B = r·A·Dm = u²`, so `r = A·t²` carries the factor `A`
  and the interpolation modulus `u·s·r` divides only `I⁴`: the interpolation is the quartic
  `ZRowsQuarticInterpolation.supported_interpolation4`. The residue is a root of
  `(t² + 3)(t³ − 19)` modulo `s·r` (`ZRowsIntersective19.root`), shifted by `κ + v`. The
  assembly is `n = H⁴e₀ + lw·u·f·y + τ·g − ψ`, which makes `Z = S·(α + β)` with `β² = P` and
  `δα² = wt·B·Df·Cy`. No division and no three-square theorem is used.

## Modules

Soundness (`LinCof/`, generic in the five slots):

| Module | Content |
|---|---|
| `LCValue` | the register record `Regs`; `regsK`/`valueK` with the five slots; `SlotLaw`, `slotLaw298`, `slotLaw300`; `regs298`/`value298`, `regs300`/`value300`; `pc_eq`, `value_eq_product`, `value_eq_zero_of` |
| `LCBootstrap` | facts that need no zero: `q` even, `|q| ≥ 2^64`, `|X| ≥ 2^66`, `H` odd, residues modulo 4, nonvanishing; under a `SlotLaw`: the guard facts `Dt_facts`, `budget_mod`, `P_mod`, `P_ne` |
| `LCNoRoot` | `Ac ≠ 0`; at a zero `S ≠ 0`, `s, r ≠ 0`, `B ≠ 0` |
| `LCNorm` | `Weight`; `Z ≠ 0`; `norm`: `P = g²`, `δ(Z − S·g) = l·S·w`, `w² = B·Df·(δ·Cy)` |
| `LCSquares` | Bezout identities; `roots`: `B = u²`, `Df = f²`, `Da = e²`, all positive; `12 ≤ Budget` |
| `LCBudget` | from `0 < Budget`: `Y ≠ 0`, centred signs, `|q|^(2+e) < |Y|`, `2^128 < |Y|`, `8 ≤ Δ`, the interval of `c` |
| `LCWindow` | the packing window, `R ≥ 4080`, `IndexModulus`, `modulus298`, `modulus300`, `modulus`, `k_ge` |
| `LCAdjacent` | `Q > 1`; the auxiliary root is integral (`e = δ·y`, `Q·V² − (Q−1)·y² = 1`) |
| `LCCarrier` | `Z = S·(g ± l·u·f·y)`, `S ∣ Ac`, `M ∣ zc`, `M ∣ H·(Y − q³)`, `Y`, `a`, `A` even, `H ∣ q^15·Kq⁵` |
| `LCEarlyFold` | the record `EarlyFold` (strong ordinate `I₀ = cn²·u`, base `|A|`) |
| `LCRank` | the record `MainIndex` |
| `LCFirstIndex` | the record `FirstIndex`: `2n = R + 1` modulo the index modulus |
| `LCRatio` | `|A|` and `|H|` lower bounds, `H_large` |
| `LCProjector` | the fifth-power height bound with multiplier `q^15`; `projector` |
| `LCOrientation` | `q > 0`, `q` a power of two; the record `Oriented` |
| `LCScale` | at a zero with `X = 2^R`: `Y = (2t + 1)·q³` |
| `LCLeaf` | `leaf_of_zero`, `sound` (generic); `sound298`, `sound300` |

Completeness (`LinCof/`):

| Module | Content |
|---|---|
| `LCCanonical` | `LCMatches` (`x 5 = Y` directly; `x 3` free); the registers at the canonical record; `Y − q³ = v·M`; `X < Y`, `1 ≤ v`; `lcBudget` with `64 < lcBudget Cn e` for `e ≤ 1` and `16 ∣ lcBudget Cn e`; the index slot at the record (`k300_canonical`, `k298_exists`, `k298_canonical`) |
| `LCGuard` | `lc_guard`: `g² = 1 + D·τ²·s²` with `D = Budget − 4`; `lc_P`: `P = (τ·g)²` |
| `LCInterp` | `lc_interp`: `u, r, f` such that for every target `a₀` there are `T ≡ a₀ (mod s·r)` and `y` with `B = u²`, `Df = f²`, `Cy = δ·y²` |
| `LCComplete` | `lc_zero`, `lc_complete` (generic in the slots, the centre and `lw`); `lc_complete298`, `lc_complete300` (every centre that does not read `x 9`, every `lw`); `complete298`, `complete300` |

Syntax and endpoints (`P172/`):

| Module | Content |
|---|---|
| `P172Syntax` | the 298/146 literal, generated node for node from the JSON; `evalRing_literal` (to `value298`); `literal_zero_iff` |
| `P172Syntax300` | the same for 300/144 (to `value300`) |
| `IPRAInteger172` | `expression` (the 298/146 literal at `ports6`), `bridge : IntegerModelBridge expression`, and `native_equivalence`, `standard_equivalence`, `reference_equivalence` |
| `IPRAInteger172b` | the same three endpoints for the 300/144 `expression` |

The three endpoints say that the native, standard and equality-only iPRA theories each prove
`nativeNoZero (signedSplit expression)` equivalent to `∼mappedNativeRefutation embedding`,
the Foundation ZFC consistency predicate: the equation has no integer zero iff Con(ZFC). The
equality-only theory proves the order-erased form. This holds for each of the two equations.

Every module was elaborated serially, one target per `lake` call, with no errors. Axioms are
within `propext`, `Classical.choice` and `Quot.sound`.

## Checkers

[`tools/gen_literal172.py`](tools/gen_literal172.py) generates `P172Syntax.lean` (`--form 298`)
and `P172Syntax300.lean` (`--form 300`). With `--check` it confirms the JSON's pinned SHA-256
and operation counts, that the regeneration is byte-identical, that the Lean literal matches the
JSON node for node, numeric agreement, and that mutation controls are rejected.

[`tools/check_ports172.py`](tools/check_ports172.py) binds the six ports. Package 172's
`coefficients/` directory is not in the repository; its `MANIFEST_SHA256.json` pins the binding
and the six payloads by byte count and SHA-256, and the checker resolves each to the repository
copy that package 138 is bound to, then compares the payloads with `P138Ports.ports6`.

## Reuse

The slot and weight generality is deliberate. Five further eleven-integer Pareto points are the
same circuit with the 300-type slots, their own centre and a smaller weight: package 135's
352/125, 340/129 and 328/130 (`wt = 4`) and package 144's 316/133 and 308/140 (`wt = 64`).
For each of them `LCLeaf.sound` and `LCComplete.lc_complete300` already apply; what remains is
the generated syntax module, the centre's independence of `x 9`, and the endpoint module.

## Remaining

Nothing for package 172: both forms are closed.
