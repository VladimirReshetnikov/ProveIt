# Independent review of the seeded thirteen-integer construction

## Verdict and scope

**PASS.** The argument in `section.tex` establishes both soundness (no
spurious integer zeros) and completeness of `generated/signed_seeded.json`,
relative to the explicitly inherited fixed-coefficient compiler and Jones
ratio theorems. No equation change was needed. This is an independent
mathematical and executable artifact review, not a new Lean build, a proof
of consistency, or a global minimality result.

The reviewed repository pin is
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`. The canonical equation has
**13 unrestricted integer variables, exact degree 57,866,184, and 759 live
binary operations: 520 multiplications, 215 additions, 24 subtractions.**
The same-source unseeded baseline has degree 71,382,096 and 770 operations
(526 multiplications, 219 additions, 25 subtractions).

## Universal proof checks

1. **Unconditional nonzero branches.** For every integer input, `J=4A-5`
   is nonzero. If `F=0`, its definition forces `A=0`, `E=+/-1`, while
   `E` is divisible by `J=-5`, a contradiction. Thus `u=JF` is always
   nonzero. The rational polynomial `(x^3-x-1)(x^2+23)` has no rational
   root, so `Theta` never vanishes. At `Sigma=0`, the final polynomial is
   `Theta^4`, excluding this entire branch, including `a0=0`.

2. **Intersective merger.** The cubic discriminant is `-23`; at odd
   primes other than 23, either the cubic has a simple root or its
   irreducibility makes the discriminant a nonzero square and the
   quadratic has a simple root. At 23 the cubic root 3 is simple; at 2,
   `-23=1 mod 8` supplies the compatible square roots. Hensel lifting
   and CRT give roots modulo every positive modulus. Conversely, when
   `v_p(t)<v_p(u)`, the two homogenized factors have valuations
   `3v_p(t)` and `2v_p(t)`. This proves exactly the stated merger
   `exists r: Zu^5 | Theta iff Z != 0 and u | t`, for signed inputs too.

3. **Seeded stack, before positivity.** Once `Sigma != 0`, the seed,
   three guard multipliers and three auxiliary variables are nonzero.
   Every stack factor is `1 mod 4`, is not 1 or -1, and is nonzero.
   Induction gives nonzero prefixes and `|Cstar|>1` without assuming
   any guard positive. This order is essential.

4. **Rational two-root recovery.** Dividing the final equation by
   `Sigma^4` and putting `q=X/Sigma` gives
   `(q^2+Cstar-Cstar^2*a1)^2=4*Cstar*q^2`.
   The branch `q=0` would imply `Cstar*a1=1`, impossible by the previous
   strict nonunit bound. The displayed rational formulas for `r0,r1`
   then give `r0^2=Cstar`, `r1^2=a1`. Rational square roots of integers
   are integral, hence `q` is integral and `Sigma | Theta` follows.
   This handles negative radicands and cancellation; no unproved
   independence of square classes is being used.

5. **Square descent and all signs.** Each new factor is coprime to the
   entire previous product, so seed and factors are pairwise coprime.
   A square total product makes their absolute values squares. The
   factors are positive since a negative square is not `1 mod 4`;
   their product sign then forces the seed positive. Positive prefixes
   force all three guard multipliers positive, giving `s>=1`,
   `phi>=0`, and `Delta>0`. The proof correctly does *not* claim that
   the seed itself is `1 mod 4`.

6. **Bound ordering and sparse carry soundness.** `Delta>0` first gives
   `0<g<c`, `K!=0`, and `4 delta^2<K^2`. With `b>=2` and integer
   `g>=1`, the leading coefficient of the injective source code gives
   `Dcode(B)>B^5190>0`, hence `R>L^2>N^2`, independently of carries.
   Under `g<4c`, the strict bounds `g<N0`, `Jcode<B^(5557)` and
   `S,T<B^5741` hold; integrality of the first two inequalities handles
   their endpoints. Therefore `S+T<L=2bB^5741` as required. Signed
   coefficient carries stay in `{-1,0}`; at a target, the digit avoids
   `B-2` precisely when the target coefficient is zero. The reviewed
   mask argument only uses the mask equivalence within its established
   interval for `g`.

7. **Parity-tuned threshold.** With `b=2^k`, `B=2^nu` and
   `nu=kappa+2k`, the verified popcount expression is
   `5947*kappa+11864*k-20`, equal to `log2(N^2)` for
   `N=2^16012040 B^2966`, `kappa=2134940`.
   The strict three-block separation above makes central-binomial
   divisibility equivalent to the no-carry source test.

8. **Signed Jones witnesses.** The interval guard and established
   source bounds imply `C,Y,K>0`; the explicit square-gap argument
   excludes `h<=0`. Replacing `i` by its absolute value preserves the
   conditions. Replacing `j` by its absolute value would not work,
   and is not done. Instead `F | H-C` and the congruences in the proof
   make `D,F,I` positive pairwise coprime squares. A positive norm-one
   Pell unit can be advanced by a unit power equal to 1 modulo `CF`,
   making `H'>B1` while preserving `H mod CF`. This yields positive
   integral `j'` and preserves the divisibility and all square tests.
   The free proof-side ceiling `8gK^2+1` supplies the literal Jones
   margin without assuming an unavailable old ceiling estimate.

9. **Cofinal square omega and stronger interval completeness.** Choose
   `b=2^(1+2r)` cofinally, so `epsilon=2^r`. The literal canonical
   construction in `Ratio.lean`, `exists_B25core`, takes
   `omega=2^(2R+1-k)`, a positive square because `k` is odd and
   `k<2R+1`. No unsupported square restriction on `s` is made.
   The actual `ratio_core` estimate and its canonical fractional tail
   yield `|C/K-Y|<b/N^2`. Since `b,c<=N` and integer
   `g(c-g)>=1`, this proves the strict new `Delta>0` for those same
   canonical witnesses. Finally positive nonsquare guard parameters
   admit Pell solutions with even second coordinate, building all
   seeded factors as squares. The merger and an integral finalizer
   variable complete a zero of the displayed equation.

## Source and artifact boundaries

The source residuals are exactly the original package-31 source with
`x_i=n_i+1`, not the later package-45 extra transport shift. The four
actual fixed payloads, their aliases, and the two additional powers of
two are specified in `FIXED_BINDING.json`. `CODE.json` specifies the
selective weight tuple; the main checker checks all 71,808 interactions.
The source residual at the origin excludes the zero source code.

`upstream/Ratio.lean` and `upstream/NineRatio.lean` are the literal Jones
ratio references reviewed for the canonical witness and interface.
The arithmetic finalizer does not use Sun's bridge. The inherited
compiler semantics remain the explicitly cited source theorem; the
finite checks do not independently rebuild or replace that theorem.
`SOURCE_PINS.json` authenticates all 14 imported source files; it and
`FIXED_BINDING.json` are the canonical dependency manifests.

## Reproduced checks

The following completed successfully, including optimized Python runs:

```
python jones/build_jones.py
python jones/check_jones.py
python -O jones/check_jones.py
python jones/independent_seeded_audit.py
python -O jones/independent_seeded_audit.py
python root_checks/check_seeded_norm.py
python -O root_checks/check_seeded_norm.py
```

The primary report `CHECK_RESULTS.json` records 540 literal circuit
replays, 50 odd-base threshold tests, 400 norm expansions, 136,000 signed
seeded-stack cases, 4,375 nonzero-divisor cases, 4,050 merger cases, 999
intersective moduli, and 114 sparse-borrow cases. The independent generic
norm check records 190,950 cases, 42 zeros, and 1,536 guard-stack cases.

The new `independent_seeded_audit.py` imports no builder, primary checker,
circuit implementation, or upstream program. It authenticates all 14
source pins by SHA256 and Git blob ID, authenticates all four compressed
and raw payloads, independently evaluates coefficient recipes at the
actual fixed tuple, and checks every circuit node is live and correctly
ordered. Its own degree propagation and nonzero actual-tuple diagonal
coefficients prove that the circuit degree upper bound is attained.
For the seeded equation those coefficients are 95, 634, and 949917 modulo
101, 1009, and 1000003 respectively. The results are persisted in
`INDEPENDENT_AUDIT_RESULTS.json`.

These exact finite certificates establish the claimed provenance,
operation ledger, and total degree. The universal equivalence is the
mathematical proof audited above, not an extrapolation from tests.
