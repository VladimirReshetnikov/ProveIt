# Formalizing the current nine-variable split form

The working numerical target is the package-59 free-carrier split form,
now also instantiated with the entire compact package-54 coefficient
tuple. It has nine positive coordinates `b,g,h,s,w,C,i,j,n`, 473 live
binary operations, and exact degree 1,910,404. The natural-coordinate
translation has 480 operations. The concrete circuits, signed constants,
provenance and finite replay receipts are in
[candidates/split116-compact](candidates/split116-compact/README.md).
The preferred `compact54-sharp` binding uses height `2^864014`, radix floor
`2^864026` and threshold scale `2^6912197`. Its factored height bound saves
one raw stored byte relative to the first compact54 instance; operation
count, degree and compressed storage are unchanged.

These numerical claims do not yet describe a new Lean theorem equating
this particular circuit's unsolvability with consistency. The closed
`ExplicitZFC` and `NativeZFC` equations remain the checked external
consistency endpoints. An actual derivation inside object-language ZFC
is a further obligation for both the old and new routes.

## Completed generic contracts

The following modules and their corresponding `Lean/checks/` files pass
Lean 4.32.0 without new axioms or proof placeholders. The theorem audits
use only `propext`, `Classical.choice`, and `Quot.sound`.

* `DegreeSeparatedCoding` extracts a source row from
  `encoded(y)^2*D2 + encoded(y)*D1 + D0`. Only interactions within the
  same homogeneous degree need isolation. Linear and quadratic labels
  may coincide; a regression example exercises this permitted collision.
* `SplitCoefficientBounds` bounds every coefficient, including collisions,
  by `H*(S^2+S+1)`, where `S` is the sum of the coordinate absolute values.
  With 31 coordinates bounded by positive `b`, the bound is `993*H*b^2`.
  A radix of at least `4096*H*b^2` therefore gives the strict quarter-base
  bound used by the signed-borrow decoder. Tests attain both signs of
  the factor 993 with all weights colliding.
* `SparseBorrowCarry.tau_polynomial_iff` proves the sparse `+1` monitor
  test for an arbitrary signed polynomial of degree below the word length.
  Coefficients have absolute value below a quarter of the binary-power
  radix, and the monitored evaluation is nonnegative. Zero binary carries
  against the sparse `(B-2)` mask hold exactly when every monitored
  coefficient vanishes. The proof constructs the borrow recurrence and
  proves its final borrow is zero; it does not assume a dense positive bias.
* `ReducedRankCarry` proves the population identity for
  `R=(L-1)*S+L*T+(L-1)`, where `L=2^u` and `S<L`.
  The identity requires no bound on `S+T`. Its split116 specialization
  checks the exact central-binomial threshold, including `b=1`.
* `MaskPopulation` proves the population of arbitrary low digit masks
  and sparse high masks. With 31 low positions and 22 high positions,
  their packed population is `139*nu-31*k-22`, expressed as an additive
  identity to avoid truncated subtraction. Combined with the reduced
  rank, this proves the calibrated binomial test from the actual masks.
* `SplitWordBounds` proves source positivity for every nonnegative `g`,
  before any weak cap or decoding assumption. It controls the negative
  linear and constant layers by their 18- and 442-degree gaps below the
  positive quadratic layer. With the later weak cap it proves
  `S+T<B^2279` and `S<b*B^2279`, as required by the outer rank.
* `FreeCarrierRatio` supplies the free positive carrier `C`, normalized
  margin and quotient shift. Positive margin recovers the former carrier
  domain, and the actual finalizer has a strictly positive final witness.
  Its soundness and completeness use the existing Jones numerical theorem.
* `SplitCarry`, `SplitSourceBounds` and `SplitSourceCarry` combine the low
  digit decoder with the sparse high borrow test, deriving the product's
  degree below 2162 and quarter-base coefficient bound from the kernel data.
* `SplitNineRatio` supplies the exact outer base, rank, threshold and cap.
  Its soundness recovers the power-of-two base and weak cap; completeness
  constructs the required positive coordinates. The threshold is checked
  for either parity of the fixed radix exponent.
* `SplitSourceWords` proves that the actual high word is positive before
  the cap, that the natural and integer word/mask expressions agree, and
  that the weak cap gives both required code ranges. `SplitSourceContract`
  assembles the calibrated binomial test with bounded positive digits and
  all monitored source coefficients zero. No supplied degree, population,
  quarter-bound or source-word positivity premise remains in this theorem.

The detailed decoder and finalizer contracts are in
[SPARSE_BORROW_CARRY.md](SPARSE_BORROW_CARRY.md),
[SPLIT_COEFFICIENT_BOUNDS.md](SPLIT_COEFFICIENT_BOUNDS.md), and
[FREE_CARRIER_RATIO.md](FREE_CARRIER_RATIO.md).

## Literal binding and remaining work

The authoritative source is package 59's expanded `parent_source.json`.
It uses the old positive transport quotient. The inherited
`source_system60.json` copy agrees with package 52's data but is an
auxiliary comparison, not a replacement for the authoritative predicate.
The two source row operations, all 89 weighted records and 22 target positions
are now bound literally in Lean by `SplitCertificate59`, `SplitKernelData59`
and `SplitKernels59`. The independent finite geometry is checked in
`SplitGeometry59`; all three kernels equal the extracted source channels
over any commutative ring. The sharp port-box height bound is also checked.

`SplitSourceExistence` supplies the unbounded cofinal construction and exact
nine-coordinate translations. `SplitNineSource59` joins this to the literal
source, with only the four port bounds left explicit. See
[SPLIT_SOURCE59.md](SPLIT_SOURCE59.md) for the equation and theorem. The counted
473-operation DAG then needs a checked evaluation identity with the
literal polynomial. Generic lemmas above do not discharge that identity.

Finally, the authentic whole-tuple native compiler must be connected to
the K215 ZFC-refutation endpoint. Existing ordinary Pell/native proofs and
finite certificate replays are evidence for that task, not Lean proofs
of it. The internal ZFC unsolvability/consistency equivalence also remains
open. No global minimum over all Diophantine encodings is claimed.

## Reproduction

From the repository root:

```sh
lake build DiophantineConsistency
lake env lean Computability/DiophantineConsistency/Lean/checks/DegreeSeparatedCoding.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/ReducedRankCarry.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/MaskPopulation.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SparseBorrowCarry.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitCoefficientBounds.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitWordBounds.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitCarry.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitSourceBounds.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitSourceCarry.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitNineRatio.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitSourceWords.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitSourceContract.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitSourceExistence.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitGeometry59.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitCertificate59.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitKernelData59.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitKernels59.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitNineSource59.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/FreeCarrierRatio.lean
python3 -B Computability/DiophantineConsistency/tools/generate_split116_compact.py --all --check
```

The last command reconstructs the two concrete instances from pinned Git
archive objects and compares all sealed files. It requires only Python's
standard library. It is independent of the Lean proof checks.
