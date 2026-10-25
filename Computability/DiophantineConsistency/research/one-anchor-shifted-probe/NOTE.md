# Eight-field shift: complete finite evidence and ordinary-proof lead

Both checked variants use 170,695 raw bytes across their four complete
integer ports, saving 1,316 bytes against the preserved one-anchor7309
tuple. They retain fifteen positive inputs, the uniform integer-leaf
66-operation front and degree 157 as candidate constructions. This
folder contains finite evidence and a detailed proof lead. It does not
claim a completed shifted native-interface proof or promote either tuple.

The entire source is authenticated through the frozen one-anchor7309
verifier, SHA256
`9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d`.
Its `model()` authenticates the full original radix55 page, closed decoder
and complete one-anchor ordinary proof before decoding every action and
tile. The probe retains all 3297 coefficient slots, including the zero
tail. No new machine index, changed tile or incoming coefficient array
is used.

## 1. Complete shifted layout

Keep selector positions 0..942 fixed. Move every one of the 34 label
positions and both dummies down eight fields. Replace the one weighted
anchor 2079 by 2063, retaining its weight `3M`, where `rho=2^47` and
`M=2^44`. Thus

```
E={0..942,975..983,995..1002,1005..1013,1015..1022,
   1055,1056,2063}.
```

There are 980 physical positions and 978 nonzero coefficients. The
entire coefficient multiset, sum 3,882,691,076,540,335 and maximum 3M
are preserved. With `G_n(x)=1+...+x^(n-1)`, the shared control formula is

```
Psi(x,t)=x^995*(x^20+t^17)*G_8(tx)
       +t^8*x^975*(x^30+t^17)*G_9(tx)
       +t^34*x^2063*(2t-1).
```

The probe expands `Psi(x,1)` into all 35 control positions and
`1024*Psi(x,2)` into the exact full weighted control array. All selector
coefficients keep the unchanged complete decoded-tile formula.

For both variants put `L=7253`, `d=47L=340891`, `B=rho^L`, `beta=B-1`.
Use `DR=rho^42`, bare coefficients at 30 and 62, and the selector-count
kernel `rho^1121*G_943(rho)`, occupying exactly 1121..2063. For clause
centers `(a,b)` and padding start p, the whole tuple is

```
DC=rho^30+rho^62+rho^1121*G_943(rho)
   +sum_e c[e]*(rho^(a-e)+rho^(b-e)),
K=DC+B*rho^42,
MC=beta-sum_(e in E,e!=1)rho^e-2*rho^1055,
Ccore=sum_(e=1005)^1013 rho^e
     +sum_(e=1057)^1064 rho^e+rho^2063,
padding=2^25*rho^(p+18)-rho^p,
MF_native=4+(2^46-2)*(rho^a+rho^b)+Ccore+padding,
MF_source=MF_native+beta.
```

| Variant | a | b | p | First reflection | Last product |
| --- | ---: | ---: | ---: | ---: | ---: |
| plus3 | 4129 | 5188 | 6277 | 2066 | 7251 |
| plus1 | 4127 | 5186 | 6275 | 2064 | 7249 |

Each entire DC has distinct coefficient residues below rho and lies
below B. Both masks satisfy the actual scalar boxes, origin residues
`MC=2 mod4`, `MF_native=4 mod8`, and populations
`pc(MF_native)=980`, `pc(MC)=d-980`. Padding has exactly
`18*47+25=871` bits; the remaining core has 109 bits.

## 2. All copy, phase and clause fields

Complete enumeration gives these exact non-temporal identities:

```
target1005+j: current975+j, j=0..8;
target1057+j: current995+j plus spatial1015+j, j=0..7;
target2063: sum_(j=0)^942 currentselector_j;
targets a,b: sum_e c[e]*current_e.
```

The first copy target 1005 has no unwanted bare-62 input: its potential
index 943 lies just above the selector interval. All other unwanted
bare, reflected and spatial terms are separately checked for every one
of the 17 copy fields. The preserved Start's south bit 1 moves from
984 to 976, so its tested copy moves from 1014 to 1006.

Every low support position is at most 1056. Difference
`2063-1006=1057` has the unique representation `(2063,1006)` inside E.
Because `L>2*2063`, the same ordinary difference exhausts the circular
alignment cases. The clause gap 1059 is absent because 1004 is absent;
the neighboring difference 1060 is absent because 1003 is absent.
Difference 1058 is present exactly as `(2063,1005)`.

For either variant the entire low band through 2063 precedes reflection.
The unit block has at most 943 Boolean contributions and cannot reach
the extra dummy until field 2176. Bare and spatial contributions total
at most nine. Thus `952+3rho/4+29<rho` supplies the same initial carry
reset. The shifted extra dummy's only possible odd fractional-phase46
spill is from 1055 to 1056. The Start tests at 1006 and 2063 therefore
recover fractional phase zero and then cell alignment by the unique
difference1057, provided the parent global carry and clean-clause
arguments are rewritten for this complete layout.

The full coefficient sum and maximum preserve the parent's count lemma
with one flag of weight three. The two reflected contributions cannot
hit together because 1059 is absent. Extra-dummy unit outputs end at
3118; reflected extra-dummy outputs begin at 3121 for plus3 and 3119
for plus1. The bare/spatial dummy outputs are separate earlier fields.
Hence the same conservative extra-dummy bound 6M and global carry29
argument apply to this layout. As an independent finite bound on the
local part, the script computes the entire Boolean convolution and its
extra-dummy envelope: both maxima are exactly the preserved coefficient
sum, attained only at the two clause centers. Adding a spatial digit
up to three, temporal bound `3rho/4`, and incoming29 stays below30rho.
The unbounded temporal and cyclic-carry arguments are still proof work.

## 3. Changed predecessors, padding, tails and safe bits

Let `Aadj=sum_(e,e+1 in E)c[e+1]*x_e`. For both variants the complete
upper predecessor is

```
field b-1: Aadj+2^18*x2063.
```

The lower predecessor is Aadj for plus3. For plus1 it is
`Aadj+x2063`: the unit kernel's last term meets the anchor at
`2063+2063=4126=a-1`. This extra term is explicitly retained; the unit
product ends before the clause itself. With at most one selected tile,
`Aadj<=2M-1024`, and both changed predecessors plus incoming29 remain
below rho. The script's sharper finite one-tile bound is
32,607,370,738,689. A complete ordinary proof must establish the one-tile
premise before using these reset inequalities.

At field p-1 the complete local contribution is `2^35*x2063`, and
every field in the following bands has zero local and spatial input:

```
plus3: 6277..6308;
plus1: 6275..6306.
```

These bands cover all 18 full padding fields and the low25 final bits.
The last product field is respectively7251 or7249, with sole raw term
`c[0]*x2063`; its coefficient is below M. Every subsequent field below
L is zero. The parent aligned top reset thus leads to the same strict
`F<q/rho<q/7`, while the new support gives `C<q/rho^5189`.
These are fresh bounds for the shifted words, not a reused old encoding.

For a safe dummy at physical1055, the largest local/spatial/temporal
exponents are `(6243,1097,1055)` for plus3 and `(6241,1097,1055)` for
plus1. Each satisfies `L-(e+1)>=3`, so three interior contributions sum
strictly below `q/rho^2`. A complete shifted proof must then repeat the
exact ordinary increment, rank/population and Boolean-subset arguments
with the new constants and controller. All rank-mask populations and
origin residues survive the complete whole-integer checks, and d remains
odd, preserving the required parity premise for the outer square bridge.

## 4. Entire new controller and measured constants

For plus3 the integer7252 is composite, and7253 is the first allowable
prime. For plus1,7250,7251,7252 are all composite. The exact base-two and
B orders are23 modulo47 and7252 modulo7253, with
`7252=2^2*7^2*37`. Every proper-order test is checked. The spacing is
`166796=23*7252`, coprime to d.

For both whole K values, the first eligible progression candidate above
d is the prime `lambda=500389=3*166796+1`. It satisfies
`B^(lambda-1)=1+40045*lambda mod lambda^2` and `B^2!=1 modlambda`.
The K-specific nonzero values `H=1+BK+B^2` are:

| Variant | H mod47 | H mod7253 | H mod500389 |
| --- | ---: | ---: | ---: |
| plus3 | 18 | 7145 | 92468 |
| plus1 | 44 | 2175 | 142110 |

Every modulus uses three complete K routes: dense Horner evaluation of
all3297 coefficients, direct decoded tile/control/kernel expansion, and
reduction of the actual whole integer K. Exact primality tests, proper
order tests and the nonzero lift establish the finite controller data
for each tuple independently.

| Complete port | Bits | Raw bytes |
| --- | ---: | ---: |
| beta | 340891 | 42612 |
| K | 342866 | 42859 |
| MC | 340891 | 42612 |
| MF_source | 340892 | 42612 |
| Total | | 170695 |

The variants have the same raw byte cost; K and MF_source differ.
The two-field tightening in plus1 adds an exact predecessor term but
does not cross the next prime-length threshold.

## 5. Retained failed nine-field shift

Moving the same labels/dummies down nine instead gives the first temporal
copy target1004. Its complete local inputs are

```
1004=974+30=942+62.
```

The intended label974 is accompanied by selector942. This invalidates
the unchanged temporal-copy identity. The script requires this exact
counterexample, including both inputs, as a negative control. It is an
obstruction to this uniform-shift layout and copy proof, not a general
lower bound for arbitrary layouts or equations.

Run `python3 -B probe.py` and `python3 -B -O probe.py`; both reproduce
`RESULTS.json` and `COEFFICIENTS.json`. All geometry failures raise explicit
exceptions. The receipt binds the script, full inherited source chain,
all decoded data, both whole tuples and the complete shifted coefficient
array. Promotion still requires a complete ordinary proof for a selected
variant, independent review, a coherent page/builder and all four new
ports; this exploratory folder alters none of the accepted7309 files.
