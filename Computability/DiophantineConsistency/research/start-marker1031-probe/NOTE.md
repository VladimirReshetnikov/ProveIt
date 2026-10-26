# Marker1031: eight Start bits and one exact tile exclusion

This complete finite candidate lowers the Start marker from1048 to1031
and the cell length from4177 to4127. Its four whole integer ports total
97,046 raw bytes, saving1,173 bytes. The strengthened alignment argument
uses all eight existing nonzero Start south-copy tests and the exact
decoded tile942. No additional polynomial input, mask test or arithmetic
operation is introduced. A complete ordinary proof and independent review
remain separate requirements before promotion.

`probe.py` authenticates the unchanged one-anchor7309 verifier and, through
its model, the full radix55 page, decoder and source proof. All943 indexed
tiles and all3297 coefficient slots are retained. The coefficient values,
language and label layout are unchanged from the zero-weight Start-marker
construction; only the zero-weight marker's physical position changes.

## Complete new tuple

Put `rho=2^47`, `M=2^44`, `L=4127`, `d=193969`, `B=rho^L`, `beta=B-1`.
The physical support is

```
E={0..942,943..951,973..981,992..999,1002..1009,990,991,1031}.
```

It has980 positions and977 nonzero coefficients. Dummies990,991 and
marker1031 have coefficient zero but stay in E. The shared control is

```
Psi(x,t)=x^992*(x^10+t^17)*G_8(tx)
       +t^8*x^943*(x^30+t^17)*G_9(tx)
       +t^34*x^1031*(2-t).
```

Its complete t=1 and t=2 specializations are checked independently.
Using the unchanged selector/label coefficients c, the entire tuple is

```
DC=rho^20+rho^30+rho^1031
   +sum_e c[e]*(rho^(2042-e)+rho^(3074-e)),
K=DC+B*rho^10,
MC=beta-sum_(e in E,e!=1)rho^e-2*rho^990,
Ccore=rho^973*G_9(rho)+rho^1012*G_8(rho)+rho^1031,
padding=2^29*rho^4124-rho^4106,
MF_native=4+(M-2)*(rho^2042+rho^3074)+Ccore+padding,
MF_source=MF_native+beta.
```

Actual whole-integer checks give core population105, padding875, native
population980, MC population d-980, the two origin residues and all scalar
boxes. The complete coefficient sum remains3,829,914,518,407,087 and
every coefficient is below M.

## Full offset exclusion

The retained Start selector0 has complemented south color510. Its bits
1..8 are all one, giving odd temporal requirements at every target974..981.
The monomial1031 copies selector0 and adds a ninth odd test at1031.
Every target is below first reflection1033. The same low-carry reset and
fractional-phase argument apply before cell alignment is known.

For the remaining rho-field offset r, the1031 test gives r=0 or
`22<=r<=1031`, since every other physical position is at most1009.
The974 test excludes wrapping, hence r<=974. The complete case split is:

- For22<=r<=29, the eight source indices974-r..981-r include952,
  which is absent.
- For r=30 or31, the marker source is1001 or1000, both absent.
- For r=32, the eight source positions are942..949. Selector942 is
  forced, while position943 requires south bit0 to be one. The exact
  decoded tile942 is `(4,437,2,437)`, whose complemented south is74 and
  bit0 is zero. The earlier clean-clause decoding therefore contradicts
  this case.
- For33<=r<=974, at least two of those eight source positions are
  distinct selector indices in one cell, contradicting n<=1.

Thus only r=0 remains. The tile942 step uses the complete inherited tile
calibration, not a guessed color or a new machine convention. The native
count lemma has recovered all labels before this phase argument.

Exact enumeration finds915 support-only candidates:0,913 eliminated by
multiple selectors, and the sole calibrated exception32. The script
checks every candidate, then stores counts/hashes of long evidence.

## Every changed field and complete controller

All17 label copies and their unwanted predecessors are checked. The marker
target1031 receives only selector0; other bare/spatial predecessors1001,
1011,1021 are absent. Clause gap1032 exceeds all physical support
differences. The exact predecessors are

```
2041: Aadj,
3073: Aadj+c[0]*marker,
c[0]=34876427265.
```

The monomial1031 acting on low support ends at2040; its marker product
is2062, away from both clauses and predecessors. The final product field
4105 has only `c[0]*marker`, resetting carry. All later fields4106..4126
are zero, covering full padding4106..4123 and low29 bits at4124.

The full Boolean and extra-dummy local convolution maxima both equal
3,829,914,518,407,087, attained at2042 and3074. Spatial3, temporal
`3rho/4` and carry29 still fit below30rho. Safe-dummy maximum exponents
are4064,1000,990; each has `L-(e+1)>=3`.

The required tail first permits length4125, which is composite;4126 is
also composite and4127 is prime. The exact base-two and B orders are23
modulo47 and the prime2063 modulo4127. Their lcm47449 is coprime to d.
After five composite progression candidates, the full new controller uses
`lambda=474491=10*47449+1`, with lift quotient135285:

```
B^(lambda-1)=1+135285*lambda mod lambda^2.
```

| Modulus | B | K | B squared | H=1+BK+B squared |
| ---: | ---: | ---: | ---: | ---: |
| 47 | 37 | 28 | 6 | 9 |
| 4127 | 1600 | 1451 | 1260 | 3487 |
| 474491 | 39160 | 446034 | 425179 | 153928 |

Every K residue is verified by full dense Horner evaluation, complete
decoded tile/control expansion and reduction of the whole integer K.

| Port | Bits | Raw bytes |
| --- | ---: | ---: |
| beta | 193969 | 24247 |
| K | 194440 | 24305 |
| MC | 193969 | 24247 |
| MF_source | 193970 | 24247 |
| Total | | 97046 |

## A retained local obstruction at marker1030

Lowering the marker one further field while keeping this layout does not
support the same alignment proof. At offset31, allowed decoded tile4 has
complemented tuple `(255,507,247,511)`. The complete nine south-copy tests
973..981 have source indices942..950: selector942 is zero, followed by
eight south bits equal to one. The marker1030 test has source999, west
bit7, also one. Thus this local decoded cell reproduces every tested Start
south parity and the marker parity at a nonzero offset.

The script retains that exact compatible pattern as a negative control.
It is a counterexample to this local alignment-test exclusion, not a
claimed complete native witness or polynomial zero. It gives no general
minimality result for other layouts or proof methods.

Normal and `-O` runs reproduce `RESULTS.json` and the full coefficient
array. All failures use explicit exceptions. The current4177 proof,
verifier and candidate remain frozen.
