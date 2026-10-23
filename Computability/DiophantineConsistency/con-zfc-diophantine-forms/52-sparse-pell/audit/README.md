# Independent round-7 audit

## Findings

No correctness defect was found in the delivered offset-free nine-variable
construction or in the shared homogeneous source optimization. The independent
checks do not import or execute any builder or another verification program.

`CONDITIONAL_SEPARATION_THEOREM.md` contains the reusable positivity-first
merger theorem, the exact CRT witness bijection, the sharper product-Pell
majorant, and the final removal of both quotient offsets. It distinguishes
mathematical proof from finite implementation checks.

The audit contributed two further simplifications during review:

1. `T=k(8D^2-4D-1)` and its positive defect
   `T^2-64DF=(8D+1)k^2-64D`, reducing the final degree.
2. The offset-free merger `Theta=Jn+Q-Jm(V0+V1)`, saving four arithmetic
   gates because `V1>Q>Q/J` already gives the completeness bound.

These are improvements within this construction. No historical priority or
absolute-minimality claim is made.

## Reproduce

Run from any working directory:

```
python diophantine_zfc_round7/audit/verify_nine_independently.py
python diophantine_zfc_round7/audit/verify_shared_source_symbolically.py
```

The first independently reconstructs the complete nine-variable formulas,
checks the actual coherent tuple modulo three primes, checks both domain
translations, evaluates the cancellation-resolved degree DAG with exact
symbolic powers of the radix coefficient, enumerates every target-isolation
condition, and tests the abstract mergers and CRT/majorant identities.

The second expands the source subcircuit **exactly** in
`Z[B,beta,K0,MC,MF]`, treating the base register as a cut. It compares the
entire polynomial with all certified source terms, without numerical
specialization. It also re-evaluates the original 60-gate source at all 31
affine inputs `n_i+1`, verifies all 22 rows, and checks the constant/pure-square
diagonal correction. All 33 delivered nine- and ten-variable source circuits
have the expected 159 independent-port monomials, including shifted packed
and homogeneous shared variants.

## Receipts and artifacts

* `INDEPENDENT_NINE_VERIFICATION.json`: exact endpoint degrees, live-gate
  counts, input hashes, modular checks, and finite theorem fixtures.
* `SHARED_SOURCE_SYMBOLIC_VERIFICATION.json`: exact symbolic source matches,
  every circuit hash, source ancestor counts, and degree-alignment checks.
* `CANONICAL_SOURCE_POLYNOMIALS.json`: canonical exact source polynomials in
  the five independent symbols for each positional certificate.
* `final_nine_replay.log`, `final_shared_replay.log`: final replay output.

The three undominated nine-positive-variable choices are:

* 548 operations, degree 15,502,748.
* 603 operations, degree 10,486,092.
* 655 operations, degree 10,127,484.

The equation domains are nine strictly positive or nine nonnegative integers,
with separate translated circuits. They are not unrestricted-integer claims.

## Source-bound review

For padding exponent `0<=p<W`, actual weights may include zero. The source is
`(B^p+g)^2`, not `(1+g)^2`; its formal counterpart is
`(T^p+sum z_i T^w_i)^2`. The encoded exponent for a degree-at-most-two monomial
`alpha` is `h_j-(2-|alpha|)p-alpha.w`.

With `B=lambda b^2`, `lambda>=4096M`, `b>=1`, and coefficient magnitudes
strictly below `M`, the leading coefficient 2 at `Dmax` gives unconditional
positive `Dcode`. On `g<4bB^W`,

```
B^p+g < (4b+1)B^W <= 5bB^W,
2(B^p+g)^2 Dcode < 50M b^2 B^(Kcode+1)/(B-1),
50M b^2 <= B/64.
```

This leaves ample room for `Jcode<N1=4B^(Kcode+1)`. The coefficient bound for
carry extraction remains `M(1+sum z_i)^2<=M(32b)^2<=B/4`. Each delivered
certificate has distinct encoded positions, positive leading coefficient 2,
`Kcode=Dmax+2W`, and `max h_j<Kcode`. The last strict inequality also
justifies the stated source leading coefficient in the exact-degree proof.

## Limitations

The semantic compiler/calibration and Jones ratio theorems remain inherited
mathematical dependencies. These audits are not a new end-to-end kernel proof,
do not decide consistency, and do not establish a global minimum equation.
