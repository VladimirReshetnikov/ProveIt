# Single Start-selector marker: 98,219-byte finite candidate

Replacing the943-term selector-count kernel by a single monomial gives
a complete finite candidate at98,219 raw bytes across its four integer
ports. This saves43,007 bytes against the zero-weight6007 tuple and
73,792 against one-anchor7309. The physical marker has coefficient zero
in the clauses and copies selector0. The full ordinary proof is being
developed separately in `../start-marker-independent/PROOF.md`; this
folder records the complete finite model and the changed proof argument.

The probe authenticates the frozen one-anchor7309 verifier
`9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d`
before import. Its model authenticates the full radix55 page, decoder
and preceding ordinary proof before decoding every action and tile.
All3297 coefficient slots are retained, including the zero tail. The
new coefficient array has the same977 nonzero values as zero-weight6007.

## 1. Complete physical support and tuple

Selectors remain0..942. The labels are south943..951, north973..981,
west992..999 and east1002..1009, with the unchanged coefficient weights.
The dummies remain990,991. The physical marker moves to1048 and retains
coefficient zero. Thus E has980 positions, and `max E=1048`. The two
dummies and marker are explicitly included even though their coefficients
vanish. The entire coefficient sum is3,829,914,518,407,087; every
coefficient is below `M=2^44`.

Put `rho=2^47`, `L=4177`, `d=196319`, `B=rho^L`, `beta=B-1`. The shared
control formula is

```
Psi(x,t)=x^992*(x^10+t^17)*G_8(tx)
       +t^8*x^943*(x^30+t^17)*G_9(tx)
       +t^34*x^1048*(2-t).
```

At t=1 it includes35 physical controls. At t=2 the marker disappears
from the weighted clause coefficient polynomial. The probe checks every
coefficient of both specializations. With `Phi(x)=sum_e c[e]*x^e`, use

```
DC=rho^20+rho^30+rho^1048
   +sum_e c[e]*(rho^(2059-e)+rho^(3108-e)),
K=DC+B*rho^10,
MC=beta-sum_(e in E,e!=1)rho^e-2*rho^990,
Ccore=rho^973*G_9(rho)+rho^1012*G_8(rho)+rho^1048,
padding=2^29*rho^4175-rho^4157,
MF_native=4+(2^44-2)*(rho^2059+rho^3108)+Ccore+padding,
MF_source=MF_native+beta.
```

All DC residues are disjoint, with first reflection1050 above all three
bare monomials. The two43-bit clause masks plus19 other tests give core
population105. Tail padding adds18 complete fields4157..4174 and29 low
bits at4175, totaling875. The actual whole integers satisfy every scalar
box, both origin residues and complementary populations980 and d-980.

## 2. The three-test alignment argument

The zero-weight count lemma is unchanged: before alignment, each cell
has at most one selected tile, and its labels are recovered. The physical
marker is not recovered by that lemma. The calibrated Start selector0
has complemented south color510, whose bits1 and8 are both one. Their
copy tests are974 and981. The new monomial contributes selector0 at1048.
Thus the forced Start gives three odd-test requirements at

```
T={974,981,1048}.
```

All three are below reflection. Four possible bare/spatial terms, each
at most three, and the temporal bound give
`12+3rho/4+29<rho`, so their incoming carries vanish before alignment.
The same fractional-phase argument applies: phases1..45 supply only
even temporal digits, and phase46 has only one possible odd dummy spill.
Hence the fractional phase is zero.

Let r be the remaining rho-digit offset modulo L. The1048 test requires
`1048-r modL` in physical E. Because1048 is its maximum, r is the ordinary
nonnegative difference1048-e. If r is nonzero, e<=1009, hence r>=39.
The974 test excludes r>974, since the wrapped index then exceeds all
physical support. Therefore every nonzero possible r satisfies

```
0<=974-r<=935,
7<=981-r<=942.
```

These are distinct selector indices in the same source cell. Both would
have to be one, contradicting the previously established one-tile lemma.
Thus r=0. This argument uses one-hot decoding before alignment; a claim
of a unique support difference would be false here.

The finite enumeration retains this distinction. There are906 offsets
compatible with physical support alone, including0. Every905 nonzero
candidate requires the two distinct same-cell selector preimages. The
first is `(r,pre974,pre981)=(39,935,942)` and the last `(974,0,7)`.
All candidates are tested in full; the receipt stores counts and hashes.

After alignment the marker mask says
`marker_(temporal predecessor of i)=selector0_i`. It does not make all
markers one. In the canonical construction it is the appropriately
shifted Start indicator, and safe dummy subsets leave it unchanged.

## 3. Every copy, predecessor and tail field

The17 unchanged label-copy identities are checked individually. The
marker target1048 has exactly the local input selector0, and unwanted
bare/spatial predecessors1018,1028,1038 are absent. The gap1049 between
the clauses exceeds max E, so both clauses cannot receive temporal input
at once. The reflected principal clauses use all977 coefficients; the
marker has coefficient zero.

The monomial1048 acting on low support ends at2057, before lower
predecessor2058. Acting on the marker gives field2096, between the
clauses and before upper predecessor3107. Let
`Aadj=sum_(e,e+1 in E)c[e+1]*x_e`. The exact predecessors are

```
2058: Aadj,
3107: Aadj+c[0]*marker,
c[0]=34876427265.
```

The upper extra term comes from the unique support difference1048,
namely `(1048,0)`. It is retained explicitly. At most one selected tile
gives `Aadj<=2M-1024`, so `3M+29<rho` resets both predecessors. The
script also checks the sharper whole finite bound, including both the
selector942-to-label943 and dummy991-to-label992 adjacencies.

The entire product ends at4156, where the sole local contribution is
`c[0]*marker`. It has no spatial or aligned temporal contribution and
resets carry because c[0]<M. All fields4157..4176 are then zero. This
proves the entire tail padding band, plus a final zero field, for either
Boolean marker value. The last raw nonzero field need not be occupied.
Every canonical word still has positive occupied clauses of value M+1.

The complete Boolean and extra-dummy local convolution maxima are both
3,829,914,518,407,087, attained only at2059 and3108. Adding spatial3,
temporal `3rho/4` and incoming29 remains below30rho. Extra-dummy bare
outputs are1000,1010,1020,2038, all distinct; reflected dummy outputs
start at2040. The full ordinary proof must supply the unbounded temporal
and cyclic-carry arguments that use these finite bounds.

Safe low-dummy increments have maximum exponents4098 locally,1000
spatially and990 temporally. Each satisfies `L-(e+1)>=3`, so their three
interior contributions sum below `q/rho^2`. The ordinary proof must
repeat the exact increment/rank and entire Boolean-subset construction
with the shifted Start marker, fresh native words and this new K.

## 4. Complete new controller and raw bytes

The first allowable length4176 is composite;4177 is prime and passes
the full controller. The exact base-two and B orders are23 modulo47
and87=3*29 modulo4177. Both proper-order tests are checked. Their lcm
is2001 and is coprime to d196319. The bounded progression search checks
13 composite candidates before selecting prime
`lambda=224113=112*2001+1>d`.

| Modulus | B | K | B squared | H=1+BK+B squared |
| ---: | ---: | ---: | ---: | ---: |
| 47 | 28 | 26 | 32 | 9 |
| 4177 | 1368 | 3388 | 128 | 2620 |
| 224113 | 189170 | 7706 | 45625 | 158694 |

The lift is `B^(lambda-1)=1+192053*lambda mod lambda^2`, proving
valuation exactly one. Every K residue is checked in three complete
routes: all3297 coefficient slots by dense Horner evaluation, the whole
decoded tile/control and three-monomial expansion, and reduction of the
actual whole integer K.

| Complete port | Bits | Raw bytes |
| --- | ---: | ---: |
| beta | 196319 | 24540 |
| K | 196790 | 24599 |
| MC | 196319 | 24540 |
| MF_source | 196320 | 24540 |
| Total | | 98219 |

The script uses explicit exceptions for every failed condition, including
all geometry and the complete offset exclusion. Run `python3 -B probe.py`
and `python3 -B -O probe.py` to reproduce both receipts. Full coefficient
arrays are retained; long geometry/offset evidence is summarized only
after exact comparisons. This exploration changes no accepted source.
