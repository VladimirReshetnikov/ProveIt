# Physical flag of weight zero: complete finite probes

The nonuniform layout below uses 141,226 raw bytes across its four
complete integer ports, saving 30,785 bytes (about17.9%) against the
one-anchor7309 tuple. Keeping the old low positions gives a second
finite candidate at148,275 bytes. Both retain the physical flag while
setting its coefficient in the two clause forms to zero. This folder
records finite evidence and the proof lead; the full selected ordinary
proof belongs in `../zero-weight-flag-independent/PROOF.md`.

The inherited one-anchor7309 verifier is authenticated before import by
SHA256 `9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d`.
Its model authenticates the full radix55 page, decoder and complete
ordinary proof before decoding all430 actions and943 tiles. Every new
array has all3297 slots, including its zero tail. The original language,
selector calibration and complete coefficient formula are preserved.

## 1. Why the coefficient can vanish without removing the flag

Let `rho=2^47`, `M=2^44`, and change the clause mask to `mu=M-2`.
For arbitrary Boolean selectors define `n=sum_j x_j`, and let W be
the34-bit copied-label value. The raw clause is

```
Q=sum_j(2^34-ucomp_j)*x_j+W,
Acl=n+1024*Q.
```

The flag has no term in Q. With incoming carry0..29 and `n<=943`, the
tested bits1..9 still force `n+k` to be0 or1, hence n<=1. When n=1,
k=0; tested bits10..43 require `Q=0 mod2^34`, so Q=2^34 and
W=ucomp_j. When n=0, they give W=0. Thus a clean clause recovers
occupation and every copied label, but deliberately does not recover
the flag. The occupied raw value is M+1 and the empty raw value0.

The flag stays in physical support E, the C mask and its own low-bit
test. The forced Start supplies an odd south-bit copy and an odd
selector-count output at the flag's position. These two tests recover
alignment by the same phase method, before a flag value is assumed.
After alignment, the flag test enforces `n=flag_temporal`. Full spatial
color matching then forces all cells occupied, and all flags become one.
The order of these steps is essential.

The shared control polynomial uses the factor
`t^34*(2-t)*x^A`. At t=1 it includes the physical flag; at t=2 it is
zero. The probe independently checks both specializations. Constructing
E from nonzero coefficients alone would omit the flag and be wrong.

## 2. Complete recipes for both layouts

Selectors stay at0..942. The four label groups retain their original
weights: south bits35..43, west27..34, north18..26, east10..17.

| Parameter | Original low layout | Nonuniform layout |
| --- | --- | --- |
| South positions | 983..991 | 943..951 |
| West positions | 1003..1010 | 992..999 |
| North positions | 1013..1021 | 973..981 |
| East positions | 1023..1030 | 1002..1009 |
| Dummies | 1063,1064 | 990,991 |
| Physical flag A | 2079 | 1984 |
| Bare south copy | 30 | 30 |
| Bare west copy | 62 | 20 |
| Spatial shift r | 42 | 10 |
| Unit kernel interval | 1137..2079 | 1042..1984 |
| Clause centers a,b | 3145,4212 | 2995,4007 |
| Padding start p | 5309 | 5019 |
| Complete padding zero band | 5309..5348 | 5019..5039 |
| Cell length L | 6299 | 6007 |

All physical supports have980 positions. Only977 coefficients are
nonzero: the943 selectors and34 labels. Both dummies and the flag have
coefficient zero. The whole coefficient sum is3,829,914,518,407,087,
exactly the former sum minus3M, and every coefficient is below M.

For each row's layout, put `B=rho^L`, `beta=B-1`, and

```
DC=rho^30+rho^westcopy+rho^(A-942)*G_943(rho)
   +sum_e c[e]*(rho^(a-e)+rho^(b-e)),
K=DC+B*rho^r,
MC=beta-sum_(e in E,e!=1)rho^e-2*rho^dummy,
Ccore=sum_northpositions rho^e
     +sum_(j=0)^7 rho^(west+westcopy+j)+rho^A,
padding=2^29*rho^(p+18)-rho^p,
MF_native=4+(M-2)*(rho^a+rho^b)+Ccore+padding,
MF_source=MF_native+beta.
```

For the nonuniform case the complete shared control polynomial is

```
Psi(x,t)=x^992*(x^10+t^17)*G_8(tx)
       +t^8*x^943*(x^30+t^17)*G_9(tx)
       +t^34*x^1984*(2-t).
```

The two43-bit clause masks plus17 copies, one flag test and origin test
give105 bits. The padding gives `18*47+29=875`, hence native population
980. Whole-integer checks establish `pc(MC)=47L-980`, all scalar boxes,
`MC=2 mod4`, `MF_native=4 mod8`, and the source mask's exact single shift.

## 3. Complete finite geometry

All17 copy targets and sources are enumerated, along with every unwanted
bare/spatial contribution. For the nonuniform layout the exact identities
are

```
target973+j: current943+j, j=0..8;
target1012+j: current992+j plus spatial1002+j, j=0..7;
target1984: sum_(j=0)^942 currentselector_j.
```

The Start test is974. Every other low physical index is at most1009,
so difference1010 has the unique representation `(1984,974)`. Clause
difference1012 is absent because972 is absent; difference1013 is absent
because971 is absent. Difference1011 is present exactly as `(1984,973)`.

The nonuniform first reflection is1986, strictly above the flag. Unit
products with low inputs end at2993; unit products with the flag occupy
3026..3968. Therefore lower clause2995 and predecessor2994 lie in the
gap, and upper clause4007 and predecessor4006 follow the entire unit
product. These are checks on physical support, including the zero-weight
flag, rather than merely the nonzero coefficient support.

For `Aadj=sum_(e,e+1 in E)c[e+1]*x_e`, the complete predecessors are

```
2994: Aadj,
4006: Aadj+2^18*x1984.
```

Under at most one selected tile, `Aadj<=2M-1024`; the script computes
the sharper bound32,607,504,956,417. The extra doubled low dummy has
zero adjacent weight. Both predecessors plus carry29 remain below rho.
The raw padding predecessor5018 is exactly `2^18*x1984`, and every
field5019..5039 is zero before temporal input. Aligned temporal support
cannot reach this band. This covers all18 full padding fields and the
low29 bits at5037. The last product field5991 is `c[0]*x1984`, followed
by zero fields5992..6006. Safe dummy maximum exponents are4997 locally,
1000 spatially and990 temporally, each satisfying `L-(e+1)>=3`.

For the original layout the analogous exact values are phase difference
1065, clause gap1067, first reflection2115, unit low-product maximum3143,
unit flag interval3216..4158, upper predecessor extra `2^18*x2079`,
padding predecessor `2^35*x2079`, last product6291 and safe-dummy
exponents5275,1105,1063. The script checks its complete geometry too.

The low phase-reset bound `952+3rho/4+29<rho` still holds. Complete local
convolution envelopes, allowing all Boolean physical inputs and then two
extra dummy units, are:

| Layout | Boolean maximum | Fields | Extra-dummy maximum | Field |
| --- | ---: | --- | ---: | --- |
| Original | 3829914518407087 | 3145,4212 | 3856576023158618 | 3776 |
| Nonuniform | 3829914518407087 | 2995,4007 | 3854576949571473 | 3553 |

The extra-dummy maximum is larger than the coefficient sum; it is not
silently replaced by the Boolean maximum. For both actual maxima,
adding spatial3, the temporal bound `3rho/4` and incoming29 remains
below30rho. The full ordinary proof must establish the temporal bound,
cyclic carry construction and all interpretation steps without assuming
occupation or alignment prematurely.

## 4. New whole controller and raw byte cost

The nonuniform search checks every integer5992..6007;6007 is the first
prime and passes the complete controller. Here `d=282329`, the exact
base-two and B orders are23 modulo47 and1001 modulo6007, and
`1001=7*11*13`. All three proper-order tests are performed. Their lcm
23023 is coprime to d. The first three progression candidates above d
are composite; the fourth is the prime `lambda=368369=16*23023+1`.

| Modulus | B | K | B squared | H=1+BK+B squared |
| ---: | ---: | ---: | ---: | ---: |
| 47 | 16 | 34 | 21 | 2 |
| 6007 | 5053 | 4606 | 3059 | 53 |
| 368369 | 315712 | 25722 | 46186 | 95646 |

The lift is `B^(lambda-1)=1+367868*lambda mod lambda^2`, so its
valuation is exactly one. Each K residue agrees in three complete routes:
full dense Horner evaluation, direct decoded tile/control/kernel expansion
with no flag coefficient, and the actual whole integer K.

The original layout has L6299, d296053, B-orders23 and134, spacing3082
and auxiliary prime305119. Its H values are24,5145,67287, with lift
quotient34579. Here the base-two order modulo6299 is6298, different
from the B-order134;47 divides the former. Its finite controller is
stated using the exact B-order. It is not claimed to meet an unchanged
base-two-coprimality clause from an earlier ordinary proof.

| Layout | beta bytes | K bytes | MC bytes | MF_source bytes | Total |
| --- | ---: | ---: | ---: | ---: | ---: |
| Original | 37007 | 37254 | 37007 | 37007 | 148275 |
| Nonuniform | 35292 | 35350 | 35292 | 35292 | 141226 |

Run `python3 -B probe.py` and `python3 -B -O probe.py` to reproduce
the deterministic receipts. Long geometry arrays are compared in full
in code and recorded by count and SHA256; small counterterms remain
explicit. Both complete3297-slot coefficient arrays are stored. The
receipt binds the full inherited source chain and each whole tuple.
No accepted source or previous receipt is changed by this exploration.
