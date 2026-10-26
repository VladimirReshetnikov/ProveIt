# Integer endpoints in the Pell-congruence proposal

**Verdict:** the four reviewed integer endpoints have coherent ordinary
existence proofs with their specified whole source-34 coefficient tuple:
17 variables/degree88, 18/32, 19/28 and 20/20. The quotient compression
uses a preliminary rank fact available before either deleted quotient or
the auxiliary norm; it does not assume the later exact index p=R. The
determinant and residue restrictions have one compatible canonical witness
family. Replacing alpha by the native C coordinate makes F genuinely
monic, with every occurrence substituted. No missing nonzero scale or
parity condition was found in these new transformations.

This is an ordinary mathematical review relative to the named inherited
signed Pell/native/K215 theorems. It does not certify a new Lean endpoint,
an encoded internal-ZFC derivation, or native calibration from scratch.
Lean remains paused. Positive companions and the nine-variable majorant
are outside this review.

## Exact intake and checked literals

The incoming archive is `con_zfc_pell_congruences_2026-10-23.zip`, arrival
commit `eae4f1952b`, SHA256
`7c21ff5d05ef52c754399a6e62f37ac7622baa6e82a702d855bfb68d82fc1a4a`.
It has230 files and6,849,876 raw member bytes. The archive hash was checked
against the actual ZIP. Read-only intake was copied to a scratch tree
before any component script was run; incoming files were not changed.

| Literal under `transport/` | Integer unknowns | Squared residuals | Exact degree |
|---|---:|---:|---:|
| `degree88_17.json` | 17 | 5 | 88 |
| `degree32_18.json` | 18 | 6 | 32 |
| `degree28_19.json` | 19 | 7 | 28 |
| `degree20_20_rank_register.json` | 20 | 8 | 20 |

Every unknown ranges over all integers. Ordered abbreviations introduce no
additional witnesses. The packets define one polynomial as the sum of
their residual squares. All declared unknowns and fixed ports are live.
These packets supply no optimized live binary-operation claim; variable/
degree comparisons should not silently be extended to arithmetic cost.

The integer tuple is the complete source-34
`mixed-parity-unrounded-1064921` tuple, beta,K0,MC,MF, with already shifted
MF, plus `cone_A=2^1113` and `cone_B=2^666104`. The six decompressed
payloads total615,883 bytes. The coefficient verifier reconstructed all
six exact integers. Independent raw/compressed hash and size checks also
passed. Compact44, compact54 and source31 ports are not substituted.

## Why the quotient removal is not circular

The exact new parametrization is

```text
V=f*c*T-f²*R-c,      T in Z.
```

For nonzero integers c,f with `c|f²-1`, it parametrizes the entire
simultaneous congruence class
`V=-c (mod f)`, `V=-R (mod c)`. In one direction, write V=fo-c.
Then c divides `f(o+fR)=V+c+f²R`; since gcd(f,c)=1, it divides o+fR.
Thus T=(o+fR)/c is integral. Conversely restore

```text
o=cT-fR,
j_aux=fT-1-((f²-1)/c)R.
```

These give V=fo-c=j_aux*c-R. They are inverse maps for every sign of
c,f,R,V. The coefficient fc is nonzero, so T is unique. The stronger
expression `f²(cT-R)-c` would impose an additional subprogression; it is
not the formula used in these integer packets.

The crucial hypothesis is established at the right point. The retained
source70 signed proof, Sections4.1–4.2, uses only:

* the first and main Pell equations;
* the native rank polynomial and index identity k=R+1+hE;
* the common-sign and eta*zeta guards;
* the ordinary strong equation `(i*c²)²=Delta(f²-1)`.

It proves `|c|=psi_b(p)`, `|f|=chi_b(m)`, and p|m for b=|a+2|>=2,
before using V, either quotient, the auxiliary norm, or p=R.
The first-index bootstrap already supplies the large-coordinate condition
for its ordinary strong-rank lemma. Pell divisibility then gives
`psi_b(p)|psi_b(m)`, hence **`c²|f²-1`**. This is stronger than the CRT
hypothesis and is available early. There is no informal cancellation of
Delta in the supplied ordinary strong equation.

In the reduced packets, k is defined as R+1+hE, so that preliminary
index equation is still present identically. E=XY and c=kY+eta are either
definitions or retained residual equations. The proof may restore those
rows first and then use the same preliminary interface. It does not need
the deleted quotient rows to justify its own restoration.

## Nonzero scales and signed cases

The shared guard forces both determinant G and eta*zeta positive.
Thus eta,zeta have one nonzero common sign; k=eta+zeta is nonzero and
0<|eta|<|k|. In every packet `W=4(3w3+1)` is nonzero and `2v_scale+1`
is odd and nonzero. With q=beta(3J3+1)+1 and beta>1, q cannot vanish;
the recovered common-sign bounds also give |q|>=16. Consequently X=qW,
Y=(2v_scale+1)q³ and E=XY are nonzero. If c=kY+eta were zero, the
integer Y=-eta/k would have magnitude strictly between zero and one,
which is impossible. The ordinary strong equation, with odd i and
Delta=(a+2)²-1>0 in the preliminary bounds, then forces |f|>1.
Thus both CRT moduli and all proof-only divisions are legitimate.

Source70's preliminary classification explicitly handles negative X:
the first consecutive product becomes m(m-1), with parameter 2m-1,
rather than assuming X positive. The new determinant guard is restored
to the original two sign guards before invoking that theorem. The residue
orientation X=2 modulo three is used only after recovering
X=plus-or-minus 2^R with R odd. Positive X is not assumed to prove it.

For the17-variable packet, eta is defined as c-kY. Its original c row is
therefore an identity, and eta*zeta>0 still supplies exactly the needed
sign information. Its half-centered first root is integral in reverse:

```text
HC=t²+2t(2P-k)+k²-4,
HC(2tau_old-2P+k)=4(tau_old²-P²+Pk-1),
HC-(t-k)²=4tP-4.
```

A zero therefore makes t-k even. The inverse
`tau_old=(t+2P-k)/2` is integral without assuming k or t has a prescribed
parity. This covers the half-centered root's potentially delicate boundary.

## One canonical family satisfies both guards

The determinant implication is sound for either sign of q. With
U=cone_A*F and Wc=cone_B*C,
`G=U Wc-(q-U-Wc)²>0` gives a common nonzero sign for U,Wc,q and
`|q|>(|U|+|Wc|)/2>=|F|+|C|`. Hence alpha=q-F-C has their same sign.
The two old positive-product guards can be restored by independent Pos
representations.

Completeness cannot choose unrelated witnesses for determinant and residue
orientation. Here the retained source71 proof explicitly covers the same
source-34 rank-tuned canonical family. Its C blocks have leading digit1
at radix exponent3296, all lower support at most2195. The F leading
digit is c0=105534389824824194647382298625 at exponent8791.
Rank tuning changes the permitted lower dummy at1063; it leaves those
leading digits unchanged. The bound on all convolution coefficients
explicitly allows every such dummy change, so no new leading carry appears.

The exact scale exponents and c0 bounds yield, on this very family,

```text
q/2 <= cone_A*F < 4q/5,
q/2 <= cone_B*C < 3q/5,
```

and therefore G>0. Its d,t,R are odd, so J_old=1 modulo three and
`w_scale_old=2^(R-t-2)=1 (mod 3)`. Thus both affine residue lifts
`J_old=3J3+1`, `w_scale_old=3w3+1` exist on the same family.
No additional rank tuning or incompatible cofinal restriction is introduced.

Finally the reused nearest-square guard is an existence equivalence:
`x,y>0` iff some s has `xy-(s²-x-y+1)²>0`. It may merge G>0 and
eta*zeta>0 after the canonical core witnesses are fixed. Its private
variables occur in no other row, so this choice creates no feedback into
the rank controller or the CRT witness.

## Monic transport and the20-variable lift

Replacing alpha by an independent integer C, with alpha=q-F-C, is an
integral affine bijection. The actual shifted transport becomes

```text
(K0+W)C-F-z(q-1)=0.
```

Its coefficient of F is -1 even if K0+W vanishes. Thus eliminating F by
`F=(K0+W)C-z(q-1)` needs no positivity, divisibility, nonzero multiplier,
or Pell hypothesis. The rank polynomial simplifies exactly to
`[q(q-F)-C](q²-1)+(MC+q MF)J`. All occurrences, including the determinant
and the rank, are substituted; F is not left as a free coordinate in any
target packet. The independent transport checker compares the whole
ordered definition graph and all retained rows against the exact parent.

The20-variable endpoint retains E and adds R_register with a monic row
R_register-R_native=0. Forgetting those two uniquely determined registers
gives the18-variable zero set, with the same root and guard coordinates.
Conversely their polynomial values restore every row. R may be arbitrary
off the zero set; its defining row is imposed before interpreting it as the
native rank. There is no new semantic assumption hidden in that register.

## Degree evidence and reproduction

The reviewed exact degrees are supported both by the delivered degree
audits and an independent AST interpreter over a univariate finite-field
polynomial ring with actual fixed ports. It checks all four complete
definition graphs, liveness, upper bounds and nonzero leading
specializations. The20-variable uniform coefficient is independently64
at `r^4 c^8 y_gap² f^4 R_register²`; only the auxiliary row can contribute
that monomial. The leading shared-guard forms give the17/88 and18/32
degrees, while the19/28 degree is supplied by its centered auxiliary row.

The scoped scratch replay ran coefficient verification, integer rebuild,
independent integer audit, transport rebuild and independent transport
audit, once normally and once under `-O`. All ten stages passed; all
integer and transport literal JSONs rebuilt byte-identically, and transport
parent copies matched the audited integer packets exactly. These are
Python-only checks; no Lean, TeX, positive companion or nine-variable
component was run in this review.

[PROPOSAL_REVIEW_PELL_CONGRUENCES_INTEGER.json](PROPOSAL_REVIEW_PELL_CONGRUENCES_INTEGER.json)
and its optimized companion preserve archive/source/tuple pins, literal
hashes, dimensions, degree data and all scoped replay records. The new
independent interpreter is
[review_pell_congruences_integer.py](tools/review_pell_congruences_integer.py).
The finite congruence controls supplement the universal proof above;
bounded examples are not used as a proof of the early-rank theorem.

The complete fixed tuple remains linked to refutation by the inherited
ordinary native/compiler/K215 theorem. This review verifies that the new
coordinate reductions meet its stated interfaces; it neither reproves that
global calibration nor turns an external equivalence into a derivation
inside the encoded ZFC calculus.
