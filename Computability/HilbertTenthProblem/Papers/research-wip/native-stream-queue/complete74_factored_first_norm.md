# A factored first norm lowers the complete comparison bound to74

The complete fixed-program universal comparison construction costs **74=40M+34A arithmetic operations**, one fewer multiplication than the established75 source. The change is an exact polynomial refactoring: all supplied coordinates, ordinary input, fixed compiler numerals, comparison operands and witness domains remain unchanged. It applies to the original30-witness/19-equation source and to the established22-witness/11-equation and20-witness/9-equation projections.

| Selected complete source | Positive witnesses | Equations | Certificate M+A | Fully paid SOS M+A | SOS total | Exact SOS degree |
|---|---:|---:|---:|---:|---:|---:|
| Original supplied-coordinate source (`raw30`) |30|19|40+34=74|59+71|130|52|
| Positive triangular projection (`positive22`) |22|11|40+34=74|51+55|106|84|
| Signed intermediate projection (`signed20`) |20|9|40+34=74|49+51|100|84|

Each resulting comparison system has exactly the same full supplied positive zero set as its own parent, with no coordinate map required for this new step. Each resulting SOS source is the **same polynomial** as its own parent on all integer or rational tuples. The separate **86-operation universal polynomial** is unchanged; its85-operation one-comparison certificate and this74-operation multi-comparison system use different finalizers. No optimality or new minimum-degree claim is made.

The source-pinned emitter is [complete74_factored_first_norm.py](complete74_factored_first_norm.py); its deterministic [receipt](complete74_factored_first_norm.json) contains all three complete comparison sources and all three complete SOS sources. Six parent source/receipt files are authenticated before their literal sources are read. Historical modules are never imported or executed.

## Exact local identity at the actual source ports

In all three parent sources, the paid registers include

```
X = wn2 = w*q³
Y = sn2 = s*q³
E = UM = X*Y
kY = ksn2.
```

The actual first factor coefficient is computed by four gates:

```
UM2 = E*E
scaled_norm_coefficient = UM2+X
ratio_product2 = (kY)*(kY)
L9 = scaled_norm_coefficient*ratio_product2.
```

The comparison is `L9=R9`, where the unchanged paid right side is `R9=tau²−1`. The ordinary positive root `tau` is already supplied in these sources. Define the two new registers and retain the comparison output name:

```
L = first_root_base = E*(kY)
first_next = L+k
L9 = L*first_next.
```

This costs2M+1A instead of3M+1A. Its exact algebra is

\[
 (E^2+X)(kY)^2
 =X^2k^2Y^4+Xk^2Y^2
 =L^2+Lk
 =L(L+k),\qquad E=XY,\quad L=XY(kY).
\]

Here `E=XY` and `ksn2=k*Y` are literal computed definitions, not retained equations being assumed at a nonzero tuple. Crucially, **the k operand is selected from the actual `ksn2` instruction**:

- In `raw30`, it is the supplied witness `k`; `R10b=eta+zeta` is a distinct computed value and their comparison must not be assumed off-zero.
- In `positive22` and `signed20`, it is the computed register `R10b`, because those already reviewed projections eliminated supplied k.

The implementation checks that distinction explicitly. Thus the new `L9` equals the old `L9` on every supplied tuple, even when any or all comparisons fail. No root translation, division, norm-sign recovery or new positivity argument is needed.

## Complete source transfer and inherited theorem

The discarded `UM2`, `scaled_norm_coefficient` and `ratio_product2` registers have only their declared private first-coefficient consumers and are not comparison outputs. `UM` and `ksn2` remain paid and live for the rest of the kernel. The replacement keeps the original `L9` output and every comparison pair, including its original comparison index. All other source definitions are unchanged. The ordinary input bridge, raw bound, both ratio slacks, actual auxiliary square, strong condition, masks, synchronization and compiler layout remain wherever the selected parent retains them.

The polynomial identity for `L9`, followed by topological induction over the unchanged definitions, proves equality of every complete comparison operand. Hence every residual is the same polynomial. The literal sum of those residual squares is also the same complete polynomial. This is stronger than equality only at natural zeros or equality after imposing another equation. The identity holds over any commutative ring; the universal acceptance theorem continues to use the parent's strictly positive integer witnesses and ordinary positive input.

For the30-witness form, this directly transfers the complete theorem of [FIXED_RAW_UNIVERSAL_75_PROOF.md](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md), represented by [complete75_half_binomial.py](complete75_half_binomial.py). The22-witness form retains the exact positive triangular projection of [complete75_positive_elimination.py](complete75_positive_elimination.py). The20-witness form retains the complete positive-zero bijection of [complete75_signed_projection_elimination101.md](complete75_signed_projection_elimination101.md), including its conditional recovery of positive C, W, mu and the omitted input gap. Those projections' proof obligations are inherited without modification; the present all-value refactoring does not need their comparisons to hold while proving its local identity.

The supplied witness names are recorded for every form. The signed20 evaluator permits signed intermediate C or W off the zero set, as its parent does; its supplied witnesses remain strictly positive in the universal theorem. The source has no external computation-time horizon. Fixed program numeral ports remain `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`, with the parent’s meanings and actual compiler restrictions, including the shifted MF convention. Giving arbitrary integers to those ports for an algebra test does not itself create a valid compiled program or a new scalar program decoder.

## Fully charged ledgers and degree

The comparison model charges every surviving binary addition, subtraction and multiplication, including uses of nontrivial fixed numerals. A comparison is recorded separately and costs no arithmetic gate until converted to a residual. The exact replacement removes one multiplication and changes no addition count, so all three complete comparison schedules cost74=40M+34A. Their comparison outputs jointly use every emitted gate.

For e comparisons, the explicit SOS finalizer computes e residual subtractions, e squares and e−1 additions. Its complete cost is `74+3e−1`, giving130,106 and100 operations. All gates in these finalized circuits are ancestors of the single output. The metadata distinguishes a comparison certificate from a one-polynomial evaluator; no zero test or finalizer is hidden in74.

Since the SOS polynomials are unchanged, their degrees are unchanged. For the original30-coordinate source, q and k are independent supplied coordinates. The first coefficient has leading term `w²*s⁴*k²*q^18`, of degree26. All other comparison residuals have smaller degree, as follows directly by propagating degrees through their actual source cones. Thus its squared residual supplies the unique top term

```
w⁴*s⁸*k⁴*q^36,
```

of degree52. There is no cancellation with another square at that degree. For the22- and20-coordinate projections, the authenticated parent proofs give the exact degree84 top term

```
16*(B−1)^60*delta⁴*w^10*s^10*Jrep^60.
```

This remains a nonzero polynomial at every admissible fixed B>1. Six exact univariate executions of the entire new SOS sources, at two fixed bases per form, independently expand every coefficient and attain52/84/84 with these displayed top coefficients. These finite degree witnesses supplement the uniform symbolic upper-bound and leading-term arguments.

## Source guards, replay and limitations

`canonical_parent(root,mode)` reconstructs one of the three authenticated complete parent packets. `rewrite(root,mode,supplied=None)` accepts only that exact selected packet when a caller supplies one, including its source, comparison list, witness interface and metadata. `checked(root,packet)` similarly authenticates a complete emitted child. The canonical data are rebuilt rather than exposed through a mutable public cache. All comparisons are recursive and type-sensitive, so Boolean and floating-point aliases of integer coefficients do not pass. `evaluate(root,packet,values,signed=False)` checks the complete canonical child, exact input dictionary and integer types; its default checks strict positivity of supplied entries, while exact `signed=True` allows integer off-zero algebra tests. Program admissibility still means the actual inherited fixed compiler numerals, not just a successful arithmetic evaluation.

The receipt records:

- Three exact literal coefficient expansions and120 comparison-operand, residual and complete-output DAG identities.
- 288 whole-polynomial identities, including144 signed cases and48 rational cases;3,744 residual identities and40,608 shared-register identities.
- 240 calls through the canonical public integer evaluator.
- 597 malformed selected-parent/child rejections,12 invalid coordinate/domain rejections and6 defensive-copy checks.
- All three complete old/new ledgers, current comparison-index mappings, witness lists, full emitted sources and six exact degree/leading-coefficient executions.

The all-value proof establishes preservation of the existing universal theorem. None of the finite fixtures materializes a full accepting Pell tower, and none is used as a substitute for that proof. This is a bounded refactoring of three authenticated sources, not an arbitrary circuit search or a Lean formalization.

Python3's standard library suffices; no historical compiler or SymPy is needed:

```sh
python3 complete74_factored_first_norm.py \
  --root /path/to/native-stream-queue \
  --expect complete74_factored_first_norm.json
```

`--output PATH` writes a deterministic receipt. Execution under `python -O` is rejected. All source and receipt dependencies are authenticated on each reconstruction. A fresh replay from a different working directory reproduces the saved receipt. The frozen historical75 and86 artifacts remain unchanged.
