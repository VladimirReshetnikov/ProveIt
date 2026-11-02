# Compact44 calibration: exact boundary and reuse ladder

This is a read-only source survey and proposed proof plan. It is not a Lean
proof of the compact44 compiler, of the 12-variable equation's equivalence,
or of an iPRA derivation. In particular, the original 2011 tuple and the
original compact44 tuple are different fixed instances, not interchangeable
instantiations of an already established parameterized endpoint.

## Exact instance and current evidence

The target 95-operation free-J graph uses all four **original** compact44
ports `(beta,K0,MC,MF)` described by
`Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/port-binding/README.md`
and `research/manuscript115-reconstruction/README.md`. Here
`beta=2^590069-1`, `K0=K`, and `MF=MF_native+beta` is already shifted.
The recorded manuscript-bound raw K hash is
`c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e`.
The separately supplied BFS-renamed tuple has the same beta, MC and MF raw
payloads but a *different* K raw hash
`4364134a56b54cf132beeb9acd8e832be68f9083f4359ace4a588a1ea76a60f7`.
Do not infer calibration for the target from the shared name, three equal
ports, or a calibration of the BFS-renamed K. The target 2011 endpoint has
beta `2^94517-1` and yet another tuple.

`candidates/free-j-polarized-positive/source/positive/coefficients/README.md`
and its `recipe/PROOF.md`, `build_coefficients.py`, `k215_transitions.json`
and `COEFFICIENT_BINDING.json` retain the original compact44 recipe and its
finite data. The Python generator reconstructs the four payloads without
executing K215. Its observations and the separately checked full raw byte
binding are finite external evidence: they are not an internal all-model
compiler theorem or an identification of a JSON/gzip/PDF with a Lean term.
The recipe gives

```
rho=2^67, L=8807, d=67*8807=590069, B=2^d,
beta=B-1, K0=DC+B*DR, MC=MC, MF=MF_native+B-1.
```

All four values must be bound together; the `MF` shift occurs once. Section 2
of the recipe establishes a general complement-sum selector/copy argument;
sections 3–6 give the 943-tile language, support/carry/alignment and the
prime `581197` rank controller. The ordinary proof itself explicitly says it
is not an end-to-end Lean/Rocq certificate. The stated inherited references
are proof obligations until their exact hypotheses and model scope are checked.

## Existing entry points and scopes

* `Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean`,
  `scalar_rank_window`, is uniform in beta and both masks, and holds in an
  arbitrary IΣ₁ model subject to its actual positivity, `MC<beta`,
  `MF<2*beta` and transport-gap assumptions. It does not identify any
  compact44 numeral or prove checker calibration.
* `ArithmeticCyclicWord.lean` contains arbitrary-model rotation and
  `kernel_rotation_congr`; `ArithmeticWindowCarry.lean` has parameterized
  `CarryInput` and `carry_column`; `ArithmeticWindowBits.lean` has
  `low_mask_decode` and `high_mask_digits`; `ArithmeticBinaryPopulation.lean`
  has `complement`; and `ArithmeticPackingBlocks.lean` supplies model-level
  definable block packing. Each has its own hypotheses; none by itself proves
  the compact44 decoder. `ArithmeticControllerLift.lean` gives the generic
  odd-modulus `lte`, `coordinates_surj` and `coordinates_inj` in IΣ₁ models;
  `ArithmeticControllerStride.lean` gives a generic model-level stride.
* `NativeSourceMask.Interface` in `NativeSourceMask.lean` is a useful
  **standard-natural** abstract port interface: it asks for the exact beta,
  `MF=MF_native+beta`, positivity/bounds, mask parities and population sum.
  Its truth over ℕ is not automatically an arbitrary-model compiler theorem.
  `NativeCyclicCarryWord`, `NativeCyclicConvolution`, and
  `ControllerResidueLift.exists_subset_boolean_sum` likewise use ordinary
  naturals or `ZMod`; they are not substitutes for internal-model claims.
* Existing machine calibration can be reused at the end:
  `ArithmeticCheckerMachine215.refutation_iff_blank_halts` is an all-model
  statement linking the selected checker to `ArithmeticMachineRun215.run`.
  `HAExpressionAssembly.PolynomialBridge` requires in **every** IΣ₁ model
  the selected expression's no-zero sentence iff that same run does not halt.
  `HAExpressionAssembly.isigma1_equivalence` and
  `IPRAExpressionNative.equivalence_of_bridge` then provide the established
  syntax/negative-translation route, subject to their own exact interfaces
  and replay provenance. A theorem only over ℕ cannot fill this premise.

## Exact hardwired cut

`CurrentMaskData2011.lean` fixes `radix=2^47`, `width=47*2011`, and the old
low/high masks. `CurrentKernelData2011.lean` fixes
`Entry := Fin 942 ⊕ ...`, the old literal K, and
`CurrentWindowCarry2011.ports`. `WangTiles942TableData.lean` defines
`tile : Fin 942 → Tile` for its particular table. `ArithmeticWindowInterface`
fixes 47, 2011, the 979-term kernel and a carry bound of 57. Higher specialized
modules include `ArithmeticAdaptiveWindow2011`, `ArithmeticControllerChoice`
(with 120198/120199), `ArithmeticController`, and `ArithmeticConstructionUnit`
(with exponent 94517 and current-K residues). They cannot be applied unchanged
to 67/8807 and the 581197 controller.

The retained compact44 generator builds `tiles = [start,forbidden] + sorted(...)`
from the dense K215 actions: start is `(2,435,3,1)` and the additional
forbidden tile is `(5,0,0,0)`. It pins 943 rows and an ordered-language hash.
The maintained 942-tile Lean compiler instead uses the decimal machine's
discovery-order state names. `DecimalMachine215.action_conjugacy` already
proves a finite 430-action conjugacy with the checked dense machine via an
explicit `stateEquiv`, and `WangTiles942Data.action_eq_decoder` binds the old
942-row table's action source. These do not by themselves prove that the new
943-row ordered selector table and aggregate complement encoding simulate the
same machine inside every IΣ₁ model. In particular the forbidden extra row,
its masked treatment, the state permutation, and the model-level run transport
must all be dealt with explicitly. The external theorem
`WangTiles942Completeness.existsMarked_iff_blank_halts` is about its particular
942-tile marked word over ℕ, not the requested 943-tile all-model theorem.

## Suggested proof sequence

1. Introduce a Lean finite-data module for the **original** four compact44
   ports from the retained explicit recipe, and an exact 943-row language
   connected to the pinned 430 dense K215 actions. Prove the necessary finite
   bounds, mask parities/populations, and that beta, K0, MC and shifted MF are
   exactly the selected literal's four coefficients. A digest comparison or
   Python `#eval`/output comparison alone is not an internal equality theorem.
   `NativeCoefficientBounds.weighted_rowCoefficient_lt_published` is a
   parameterized *standard-integer* published-size bound; it is not compiler
   semantics and does not establish equality to this tuple.
2. Formalize the recipe's aggregate complement-selector lemma in an arbitrary
   IΣ₁ model, with explicit Boolean copy bits, the selector-count bound, the
   empty-cell case, and no hidden assumption that internal payload additions are
   carry-free. Supply the exact 943-entry coefficient and mask identities to
   the generic carry/rotation framework. Prove soundness from a literal graph
   zero to the same modeled machine halt, including alignment and all shifted
   mask conventions.
3. Adapt the coefficient-independent parts of the construction to the new
   actual tuple and explicitly establish the `581197` prime/order/residue and
   unit facts, bounded Boolean-set controller, safe dummy positions, and
   padding for model-internal, potentially nonstandard times and dimensions.
   `ArithmeticControllerLift` is generic but `ArithmeticControllerChoice`
   is currently specialized to 120199 and requires refactoring or a new
   instantiation. The standard-natural subset lemmas are useful guides only.
   Prove the reverse modeled halt-to-positive-zero direction, rather than
   relying on standard-natural cofinal tilings.
4. Join the signed ordinary-tail and positive-coordinate results for the
   *95-operation free-J* graph, instantiate the complete tuple, and supply
   the resulting all-model `PolynomialBridge`; apply the existing iPRA
   transfer and verify both directions, exact literal binding and dependency
   provenance. This final step also needs the independently open ordinary
   integrality/rank and compact44 graph-to-checker arguments.

## A concrete first model-level lemma

The local finite-sum selector/copy equivalence outlined below has since been
proved under the stated count, value, copy and no-carry bounds in arbitrary
`IΣ₁` models over an external finite index type. Its [paired replay](../compact44-decoder-iff-prototype/README.md)
passed an [independent artifact audit](../../../reviews/compact44-decoder-iff-independent-audit/README.md).
That result does not yet bind the 943-row data, derive the graph hypotheses,
or prove the machine simulation.

For the recipe's selector count `n<2^10`, selector/copy payload `P`,
`S=n+2^10 P`, and mask `mu=2^51-2`, one can aim to prove the aggregate
lemma directly in an arbitrary IΣ₁ model:

1. `ArithmeticWindowDigits.noCarry_dig` transports `NoCarry S mu` to their
   51-bit low digits. Since `mu<2^51`, `noCarry_ones_two` (with `m=50`)
   makes the low 51-bit digit of S at most 1.
2. Since `2^10` divides `2^51`, reduction to low 10 bits gives `n<=1`.
   The fixed sum of nonnegative Boolean selector values then has either no
   selected index or exactly one; the precise selected-index extraction is
   a separate finite-sum lemma.
3. In the zero-selector case, Boolean selectors vanish and
   `P=W<2^41`, so `2^41 | P` forces `W=0`. In the one-selector case for i,
   `P=2^41-v_i+W`, with `1<=v_i<2^41` and `W<2^41`; thus
   `0<P<2^42` and `2^41 | P` imply `P=2^41`, hence `W=v_i`.
4. Conversely, verify the empty and one-selector prescribed-copy cases
   against `NoCarry` using the explicit bit interpretation.

This outline relies on additional model arithmetic for nested remainders,
subtraction, the finite 943-term Boolean sum, the direct converse and the
41-bit copy bound. `dig_mod`, `fbit_dig`, and `noCarry_iff` are candidate
interfaces; none of these ingredients has been newly compiled here. It never
assumes the ordinary sum S is globally below `2^51` or that payload carries
are absent. Nor does it prove alignment, table-to-machine semantics or the
completeness controller.

The 51-bit quantity above is the *low selector/copy clause limb* tested by
`mu=2^51-2`; it is not the 67-bit tile radix width. The arithmetic carry and
window machinery still uses `rho=2^67` for each of the 8807 positions. More
explicitly, take 943 Boolean selectors `x_i`, `n=Σ_i x_i<2^10`, copies
forming `0<=W<2^41`, and literal payloads `1<=v_i<2^41`, and put

```
P = Σ_i (2^41-v_i)*x_i + W,
S = n + 2^10*P.
```

`noCarry_dig` has the hypothesis `NoCarry S mu` and yields no carry between
`dig 51 S 0` and `dig 51 mu 0`. The latter digit equals mu because mu is
below `2^51`; the former is below `2^51` by `dig_lt`. Applying
`noCarry_ones_two 50` requires rewriting `51=50+1`, yielding the at-most-one
low limb. For the modular reduction, `mod_mod_of_le` is parameterized by radix
width and exponent indices, so an instantiation at width 1, indices 10 and 51,
plus the `n<2^10` and `S=n+2^10 P` equations should yield the selector bound;
the exact simp and cast steps remain to be checked. A full lemma must prove the
reverse implication as well and keep the separate outer 67-bit carry bound.
