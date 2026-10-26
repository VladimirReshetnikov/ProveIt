# Checked two-block split-kernel carry contract

[`SplitCarry.lean`](Lean/DiophantineConsistency/SplitCarry.lean) combines the
checked low-digit mask and sparse signed-borrow decoder. Its block length is
generic; the selected source can later use `lowLen=117`.

The numerical data are

```
S=g+B^lowLen*J.toNat,
T=indexedLowMask+B^lowLen*(B-2)*sum(target q) B^q.
```

`packedMask_eq` identifies `T` with the separately population-counted
`MaskPopulation.packedMask`. The low-mask range follows from bounded distinct
weight positions, powers of two `b<=B`, and the mask digit theorem. Together
with the explicit range `g<B^lowLen`, this gives a blockwise carry equivalence
without a bound on the high word or high mask.

`tau_family_iff` permits a polynomial `P(z)` depending on the decoded digits.
For every bounded digit tuple compatible with `g`, the caller supplies the
explicit arithmetic identity

```
J=2*P(z).eval B+sum(target q) B^q.
```

With the polynomial degree, strict quarter-base coefficient bound, and
`J>=0`, the theorem proves

```
tau 2 S T=0
  iff exists z, all z_i<b, g=sum_i z_i*B^w_i,
                all monitored coefficients of P(z) are zero.
```

The fixed-polynomial variant is `tau_polynomial_iff`. Neither theorem
introduces a source predicate or treats an evaluation identity as a semantic
compiler assumption.

`eval_encoded_add_one` proves that the positive-coordinate word for `z_i+1`
is exactly `sum_i B^w_i+g` when the low code equals `g`.
`highInt_eq_eval_product` then proves the evaluation identity for arbitrary
three split kernels. `tau_product_iff_31` uses this explicit high integer and
derives the quarter-base coefficient bound from the checked `993*H*b^2`
estimate and `4096*H*b^2<=B`. Kernel coefficient bounds, high-word positivity,
polynomial degree, and the low range remain explicit numerical hypotheses.
The weights need no cross-degree isolation for this contract; coefficient
extraction from a particular finite source is a separate theorem.

`calibrated_family_iff` composes the same contract with the shorter
central-binomial rank. It explicitly requires `S<2^u` and the population
calibration `u+pop(T)=2*v`; it concludes the corresponding square-power
binomial divisibility iff the same bounded digit/coefficient condition.
No source, coefficient-tuple, machine, or consistency premise is discharged.

Regression checks combine a passing low digit with a high word containing
an actual negative lower-digit borrow, reject a low digit equal to `b`,
exercise the complete polynomial interface on `X^2-1`, and check the empty
low-block boundary. All audited proofs use only the standard Lean axioms.
