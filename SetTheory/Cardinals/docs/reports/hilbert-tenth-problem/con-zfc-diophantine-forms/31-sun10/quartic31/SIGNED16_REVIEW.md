# Second independent review of the sixteen-integer construction

Reviewed the new emitter `../signed16/build_signed16.py`, its data and full
literal output, the inherited signed17 proof, package30's Jones/quartic31
proof, and the repository's `Master3.lean`, `NineReduce.lean`, and
`NineRatio.lean` source constructions. This is ordinary mathematical review,
not a proof-assistant certificate.

## Logical order and cofinal base

The complete `USys_of_mem` proof uses its chosen exponent
`w=x*y+sum(zs)+1` only to obtain `w>=1`, `xy<2^w`, and `zs_i<2^w`.
All remaining constructions and estimates use those inequalities and the
fact that b=2^w. Thus the proof still applies to every larger exponent w.
The reduction in `NineReduce.reduced_of_mem` keeps that same b, and
`NineRatio.ratio_complete` has b as a fixed parameter rather than selecting
a new one. Consequently restricting w to a cofinal progression c+2r is valid.

The digit positions of the index are distinct, and every digit z+c_alpha is
strictly below 2z. Thus y<(2z)^(L+1)=kappa. A choice t=2^r gives
b=kappa*t^2=2^(c+2r), and all sufficiently large choices meet the source's
size conditions. This is the required constructive completeness argument;
cofinality of b alone would not justify it without inspection of the source.

In soundness, positivity of b must be proved after the guards. It is not an
unconditional fact when t=0.

## Nonzero merger and smaller weights

For all integer source inputs J=4A-5 is nonzero. If F=0 then A=0 and E=+/-1,
but E=iJDC^2 is divisible by 5 in that case. Hence Ddiv=JF is always nonzero.
The homogeneous polynomial Tmerge is nonzero because its dehomogenization is
`(x^3-x-1)(x^2+23)`, which has no rational roots. Therefore Smerge=0 would make
the final three-root norm equal Tmerge^8, a nonzero integer. At every final
zero, Smerge is nonzero, hence i and all six guard witnesses are nonzero.

Each guard factor Bj=1+4dj Cprev^2 zj^2 is 1 modulo 4 and dj is 2 modulo 3.
Consequently Bj is not 0, 1, or -1 once zj is nonzero. It follows that the
absolute value of the full stack is greater than one before any sign guard
has been recovered. This justifies the smaller signed weight w1=stack and
w2=stack*(P^2+K^2+2). Their absolute values satisfy the separating inequalities.
Complex square roots of negative radicands cause no difficulty: the triangle
inequality and Galois sign argument use absolute values, not positivity.

The square-stack and homogeneous divisibility proofs therefore apply without
assuming t nonzero. After recovery of all guards, g=g0+1>0 and margin>0.
If t=0 then b=0 and Gcap=32bB^(5^nu)=0, so

    margin = -8*g*K^2 <= 0,

a contradiction. Hence t is automatically nonzero. It is safe to omit t
from the nonzero product Z=i*z1*...*z6, saving one multiplication.
Only now infer b>=kappa>y and define epsilon=b-y-1>=0, before applying the
inherited signed h/i and Jones soundness lemmas. There is no circular use of
positive b in the denominator, merger, square-stack, or weight arguments.

## Degree check

Let L=5^32, treating all fixed coefficient recipes as constants. Direct
inspection of the literal formulas gives

| Expression | Degree |
|---|---:|
| R | 470 L |
| P | 1900 L + 3 |
| K | 1900 L + 4 |
| a0 | 7600 L + 14 |
| a1 | 49280 L + 68 |
| margin | 4442 L + 12 |
| guard5 | 363 |
| stack=guard6 | 4442 L + 1103 |
| Ddiv | 13750 L + 20 |
| Smerge | 68750 L + 107 |
| weight2 | 8242 L + 1111 |
| A2norm | 203264 L + 2504 |

A2norm has strictly greater degree than the competing norm terms. The final
leader is A2norm^4. Hence the degree is exactly

    813056*5^32+10016
    = 18930435180664062500000010016.

The accompanying independent auditor also propagates degree bounds and
actual-instance leading diagonal coefficients modulo 1000003 and 1000033.
Both are nonzero (121738 and 73024 respectively), independently certifying
that the claimed top degree survives after the selected coefficient tuple
is substituted.

## Literal audit

Run `python3 audit_signed16_independent.py --signed-dir PATH_TO_SIGNED16`.
It reads only data and imports neither the emitter nor its DAG utility.
For the final 121-by-8801 coefficient tuple it verifies all four decompressed
port hashes, expands the full 58,905-position coefficient baseline directly,
uses a separate divide-and-conquer geometric sum, and checks 288 named-node
values on six assignments over two primes. The assignments include t=0 and
negative base coordinates, so they exercise preguard behavior. It also
checks the eight-factor norm identity exactly in the rank-eight ring with
three formal square roots, including negative radicands, for 100 cases.

The finite diagnostics certify the transcription and degree calculations.
The cofinal-base, signed-guard, and root-separation reasoning above supplies
the universal mathematical argument for the new steps. Compiler correctness,
the chosen parent quartic's semantic interface, and K215's calibration remain
the explicitly inherited proof dependencies.
