# Joint exponent parity and the full radix-125 order in the canonical three-adic family

For the precise canonical ansatz `q=2^d*3^k`, `R=2*3^e-3`, the repunit
and packed-index divisor force **k even and e odd** for every odd d>=3.
Thus the offset e-3k must be odd. Separately, a new exact order certificate
for the entire modulus `2^125-1` extends the previously proved exclusion
from authentic exponents d=5^n, 2<=n<=16, to **2<=n<=34**.

Neither conclusion is an exclusion for all powers of5. In particular the
proof leaves odd offsets at n>=35 open and does not decide direct-X83
soundness, arbitrary canonical scales, or wrapped positive zeros.
No paid source is modified. The parity argument was derived during this
follow-up; root observed that the same character also gives k even.

## 1. Inherited interface

Let d,k,e be positive integers, and put

    B=2^d, q=B*3^k, R=2*3^e-3.

Assume the exact repunit and packed-index necessary conditions

    J=(q-1)/(B-1) is a positive integer, J divides R.       (1)

For the range exclusion also assume the inherited numerical window

    (2q-1)(q^2-1)<R<q^3(q-1).                             (2)

These are necessary at an authentic direct-X83 positive zero with this
q,R ansatz: every term of its literal packed index

    R=(qU-Z)(q^2-1)+(MC+q*MF_source)J

is divisible by J. The unchanged bootstrap supplies (2). They need no
interpretation of native masks for the following arithmetic arguments.
The previous varying-offset theorem proves from (1)--(2)

    3^k<=3B^3(B-1)<3*2^(4d),
    11k<11+28d,                                         (3)

where the second inequality uses 2^11<3^7. The full source recipes have
d=5^n with n>=2; the parity theorem below only needs odd d>=3.

## 2. A uniform Jacobi-character obstruction

Suppose d is odd and d>=3. Since B=0 modulo8 and B=2 modulo3, the
repunit identity `(B-1)J=B*3^k-1` gives

    J=1 modulo8, J=2 modulo3, hence J=17 modulo24.        (4)

In particular J is odd, coprime to6, and greater than1 (indeed J>3^k).
The Jacobi symbol is therefore defined with this positive odd denominator.
No primality or squarefreeness of J is assumed. The supplementary law
for2 gives `(2/J)=1`. Quadratic reciprocity, using J=1 modulo4, gives

    (3/J)=(J/3)=(2/3)=-1.                              (5)

Apply the multiplicative character to `2^d*3^k=1 modulo J`, which
follows from q=1 modulo J. Equations (4)--(5) give `(-1)^k=1`, proving
**k even**. This conclusion used only the repunit in (1).

Since J is coprime to3, its divisibility of R can be cancelled by3:

    2*3^(e-1)=1 modulo J.

The same character gives `(-1)^(e-1)=1`, proving **e odd**. Consequently

    c=e-3k is odd.                                     (6)

Under the additional lower bound (2), the inherited argument also gives
c>=1. Thus the admissible offsets in that interface are positive odd
integers, not merely arbitrary positive integers.

**Remark 1 (an exact additional reason the old even-offset progression
fails).** The earlier radix-compatible scalar progression takes
c=2^(3d+1), k a multiple of lcm(ord_(B-1)(3),c), and e=3k+c. Its k and
c are even, hence e is even, contradicting (6) if J divides R. This
refutes completion of that progression to a literal packed index without
using its marker positivity argument or a large-k inequality. Its proved
canonical scale and repunit properties remain valid; those were never a
complete source-zero theorem. The previous fixed-offset and marker
obstructions are retained unchanged.

## 3. One exact full-modulus order certificate

Set

    M=2^125-1=42535295865117307932921825928971026431,
    O=2576525686996852656333000
     =2^3*3^2*5^3*41^2*107*10223*184711*842887.           (7)

The exact order of3 modulo M is O. The certificate uses `3^O=1 modulo M`
and the following residues, each different from1:

| Prime ell | 3^(O/ell) modulo M |
| ---: | ---: |
| 2 | 30956704208697257411056507980356130152 |
| 3 | 15658468161339686373973998107111488354 |
| 5 | 10664710849360348179995350704375424989 |
| 41 | 8264232980333680078538289627652816672 |
| 107 | 10006089262660319110576718966247817960 |
| 10223 | 21042106684190814350812957586723129037 |
| 184711 | 16393777223232271084185805725897864898 |
| 842887 | 5542338464860825349674650997828247544 |

The eight factors displayed in (7) are prime; finite trial division
through floor(sqrt(ell)) verifies this, with largest endpoint918.
Multiplication verifies the complete factorization of O. If the order
were a proper divisor of O, it would divide O/ell for one of these prime
factors, contrary to its listed residue. This proves exactness without
assuming M prime. The modular powers are checked by a fresh handwritten
square-and-multiply loop and compared with the language's scalar pow.

The search leading to (7) examined the unused exact cofactor
`4710883168879506001` of the same Mersenne modulus used in the preceding
work. The final certificate above is directly on the whole M; it does
not rely on that cofactor's primality, on its separate order, or on any
external factorization result. No new larger Mersenne exponent is used.

## 4. Transfer to every multiple of125 and the covered range

Whenever125 divides d, M divides B-1. The repunit in (1) gives
`3^k=1 modulo B-1`, hence `3^k=1 modulo M`. Therefore O divides k.
By (3), no candidate can exist when

    11O>=11+28d,
    d<=floor((11O-11)/28)=1012206519891620686416535.      (8)

For d=5^34=582076609134674072265625 the exact positive margin is

    11O-(11+28d)=12043637501194505196225489.

All 3<=n<=34 therefore satisfy (8). The preceding proof's d=25
certificate ord_(2^25-1)(3)=450 excludes n=2. Together these prove
no authentic positive zero of the stated ansatz for **2<=n<=34**.
This includes, but does not change, the previously frozen2<=n<=16 result.
The fixed modulus is now used through its entire order rather than the
partial order supplied by two of its factors.

**Remark 2 (the enlarged finite certificate is still not an all-n proof).**
At d=5^35=2910383045673370361328125, take k=O. It satisfies the exact
order requirement and k even, and it passes even the sharper inherited
size test, since

    2k=5153051373993705312666000
       <8731149137020111083984375=3d,
    3^k<2^(2k)<2^(3d)<3B^3(B-1).

This is a concrete counterexample to upgrading the partial order and
size tests into an all-n exclusion. It is not claimed to satisfy the
full repunit modulo2^d-1 or to admit any e, packed index, or source zero.
Adding the parity requirement e odd is a further necessary test, not a
proof that such an e exists.

**Open question 1 (credited continuation of root's uniform route).** Can
the full repunit and J|R, with k even, e odd and window (2), exclude the
remaining odd offsets for every authentic d=5^n, n>=35? A uniform lower
bound on ord_(2^(5^n)-1)(3) strong enough for (3) would suffice, but none
is proved here. The fixed factors' valuations do not automatically grow
when n grows: for example LTE gives v31(2^(5^n)-1)=1 for all n>=1.
The new finite certificate alone cannot replace this missing argument.

## 5. Evidence, attribution and limits

The companion fresh helper performs only scalar modular arithmetic,
small prime trial division, endpoint comparisons, and byte/span bindings.
It checks one full-modulus order, its eight proper-prime tests, and the
explicit n=35 partial-test boundary. The Jacobi theorem is proved above;
no finite parity sample is substituted for that proof. The helper hash is
`2be94c50335e2d149672355b0e9525d81293fb4285328c95c37ce9e657cd2f27`.

Dependencies read in full, inertly, are the committed
`direct_X_three_adic_order_range_pascal.md` (SHA256
`d57209396a8baffd74782c6c8380f41be5bbcbbd360438b3819182f01a37a948`),
`direct_X_varying_three_adic_offset_bound_pascal.md`
(`926f648494c4bac101901f4dd1552402f94a44c39efb80ee4df3c30466254394`),
`direct_X_fixed_offset_repunit_divisor_root.md`
(`8e54b2963256a1a239e91a495f22c6c43c26d439c287f724b0e2679f96827717`),
and `direct_X_authentic_outer_root.md`
(`35d5d5080a615583779f31b1985768045455ab6cbbfc394dac4b93cc2713a617`).
The receipt authenticates their full bytes and exact read spans. Their
ancestral native proofs and source arrays are not newly re-certified.

No supplied, archived, predecessor or frozen program is executed or
imported. No source array is evaluated, compiler instance constructed,
or huge canonical X,Y/native witness materialized. There is no repository
or Git mutation and no new universality or operation-count claim. Receipt
and final replay status are supplied separately to avoid a hash cycle.
