# Independent pooled-power and bootstrap review

25 October 2026. Internal AI-assisted ordinary mathematical review, not external
peer review or a new proof-assistant verification. All paths below are relative
to the workspace. No old-round or upstream source was edited.

## Findings

1. The existing two-coordinate fixed-base pooling lemma transfers correctly to
   the strict factorial-free integer source. Its exact affine coordinate shifts,
   all 14 old congruences, retained Pell rows, deletions, survivors, and full SOS
   expansion were independently checked for the 224- and 225-variable stages.
2. The source's literal square frame, after undoing retained row combinations,
   bounds every actual power base, output, and index by its square. Thus no
   frame strengthening is needed for integer pooling.
3. The subsequent beta replacement `y=F*(2w+1)` has an acyclic sign-recovery
   argument even though it no longer makes `y` positive immediately.
4. Standard pooled K,L are automatically nonnegative whenever the base n and
   modulus T are positive. However, the natural source uses consecutive Pell
   coordinates instead of existing X and AY wires; its proposed three-wire
   pooling variant is the appropriate degree-two encoding.
5. A direct common-modulus merger of the adjacent bases is obstructed by an
   exact small resultant. This is a limitation of that particular approach,
   not a lower bound or global optimality claim.

## 1. Fixed-base algebra and natural signs

Let `Z_i=A*Y_i`, `D_i=m_i-X_i+Z_i`,
`H=sum Y_i*(m_i-X_i)`, `S=sum(D_i^2-Y_i^2)`, and
`T=2*A*n-n^2-1`. The rows are

    K - 2H - (2A-n)L = 0,
    S - nK + L = 0.

Writing `e_i=D_i-nY_i`, direct expansion gives

    sum e_i^2 = S-2nH-T*sum Y_i^2
              = T*(L-sum Y_i^2).

The congruence, inverse clearing for negative indices, and squared-atom estimate
in upstream `158-pooled-powers/proofs/POOLED_POWERS.md` therefore apply unchanged.
No individual Pell error `e_i` is claimed small; only the ordinary cleared
power errors are bounded.

For completeness, exact individual congruences give `T|e_i`, so the constructed
L is integral. If `n>0` and `T>0`, the identities

    L = sum Y_i^2 + (sum e_i^2)/T,
    nK = sum D_i^2 + (sum e_i^2)/T

show both L and K are nonnegative. K is integral from its defining first row.
Consequently the standard block itself has no natural-sign obstruction.
These are proof identities; they introduce no divisions into the polynomial.

## 2. Independent literal integer audit

`check_frame.py` imports no producer module. For the dense strict235 source it
reconstructs the pure square frame as the literal row combination

    frame_row + domain_guard.3 + 2*mul.40_defining_row.

For sparse strict236 the combination is `frame_row+mul.40_defining_row`.
In both cases the result is exactly

    W = 2 + sum of 34 actual affine atom squares.

The atoms include t, F, F+t, x, actual y+1, all nine actual representatives,
the actual anchor index, both q and q+1, B, BH, N, and all retained requested
outputs. It verifies all 17 base/index/output triples. The actual representative
`a` is stored `crt.encoded.a-1`; actual `y+1` is stored `y`;
`q=4*radix.odd_square_root_half+1`. The two special principal-pair offsets
are separately authenticated by `check_pool_transplant.py`.

Because `t>=16`, `W>=258`. Thus each relevant squared atom is below W and the
existing `|A|>W^W` suffices for the same fixed-base estimate (11 and 3 terms).
The audit rejects a one-unit mutation of the frame constant.

`check_pool_transplant.py` independently reconstructs every changed row from
literal source polynomials. It checks the shared affine expression for T_q,
each removed quotient congruence, every retained AY gate and norm, the formal
aggregate identity before imposing AY=Z, the variable/row deletion manifests,
all retained output rows, all variables, all collected quartic coefficients,
and all printed metrics. Both branches pass normally and with Python `-O`.

    strict235 -> pooled224: 224 variables, 161 rows,
                           19301 monomials, height 7968.
    strict236 -> pooled225: 225 variables, 162 rows,
                           11736 monomials, height 7968.

The reports in POOL224.json and POOL225.json, not the prose census above, are
the authoritative literal metric record if subsequent stages are added.

## 3. Acyclic bootstrap with an affine odd beta multiplier

Use semantic, not stored, names. Retain

    t=16+h^2,  F=t^t,  q=4z+1,
    y=F*(2w+1),
    B*h_B=C+F+1,  N=B^x,  q=(BH)^x,
    H=2+C+sum of the eight other representatives,
    x=F+1+(y+1)u_0,
    x=1+(1+(t+1)y)u_t.

The initial frame and signed-orientation proof precede all these arithmetic
sign conclusions and are unchanged. The first singleton power has positive
base t and gives F=t^t>1. The beta factor is odd and nonzero, so y is a nonzero
integer multiple of F, though it may not yet be assumed positive.

1. Since q is one modulo four, q is nonzero and q+1 is two modulo four.
   Hence `|q+1|>=2` independently of y or x. Apply the eleven-member pool at
   q+1 first. It makes every representative index nonnegative and supplies
   every exact numerator power. Hence H>=2.
2. The index row has positive right side C+F+1, so B is nonzero and
   `|BH|>=2`. Its retained singleton power gives x>=0 and q=(BH)^x.
3. If x=0, the last endpoint says `1+(t+1)y` divides -1. Therefore this
   integer equals 1 or -1. The first possibility gives y=0, contrary to
   the nonzero odd multiplier. The second gives `(t+1)y=-2`, impossible
   for an integer y and t>=16. Thus x>=1 and `|q|>=2`.
4. Apply the three-member pool at q. Its requested indices are t, y+1, x.
   In particular y+1>=0, so y>=-1. Since y is a nonzero multiple of F>1,
   the only possibility is y>=F>0. This is the missing sign step; no
   claim about the sign of a unit-base exponent was used.
5. If u_0<=-1, the first endpoint gives x<=F-y<=0, a contradiction.
   Thus u_0>=0 and x>=F+1>1. The last endpoint now has positive modulus,
   so u_t>=1 and x>=(t+1)y+2>=(t+1)F+2.

Every size and signed-digit estimate of the strict factorial-free source now
has its original hypotheses. They recover positive B and then positive q.
The existing zero-accumulator propagation excludes the boundary y=F after
local CRT decoding; therefore y>F and the initial remainder really is F+1.
No claim that `y>=F` alone makes F+1 a valid bounded remainder is needed.

### Completeness

Choose the strict cofinal horizon with even h, so t is even and
`v_2(F)=t*v_2(t)>v_2(t!)`. If O is the odd part of t!, choose an arbitrarily
large positive odd multiple v of O and put `y=Fv`, `w=(v-1)/2`.
Then t! divides y, y is even, and it exceeds every finite pending product.
All beta moduli are odd and pairwise coprime. Their CRT code x can be made even,
positive and arbitrarily large, as before. No former square condition on y is
used elsewhere; the replaced private multiplier square was its only use.
The remaining representative parities, B odd, H odd, q an odd square, frame,
Pell witnesses, exact powers, and pooled K,L witnesses can be selected in their
unchanged order. This establishes the ordinary existence equivalence.

## 4. Consecutive-coordinate natural variant

The natural source instead has canonical consecutive ordinates `(Y_i,Z_i)`
with `X_i=A*Y_i-Z_i`. Define `D_i=m_i+Z_i`, `T=2An-n^2-1`. There need not be a
materialized X_i or A*Y_i, so silently substituting these products into the old
H would make a cubic row.

Introduce three natural coordinates U,K,M and use

    U = sum Y_i^2,
    K = 2*sum Y_i*D_i + (2A-n)M - nU,
    sum D_i^2 + M - nK = 0.

All three rows are quadratic. Eliminating them gives

    sum(D_i-nY_i)^2 = T*M.

Thus, with canonical indices and a sufficiently large T, the same small-error
method recovers every exact power. Conversely exact individual congruences
make `M=sum e_i^2/T=T*sum(e_i/T)^2` a natural integer when T>0; U is natural,
and `nK=sum D_i^2+M` shows K>=0. Integrality is supplied by the defining K row.
This proves the abstract natural block under its stated canonical-pair interface. The actual natural source has an initially ambiguous abscissa after deleting one incidence; `NATURAL_REVIEW.md` Sections 4–6 supply its required inverse-clearing and additive-frame repair. It does not turn the eleven separate
modular-digit requests into exact-power requests with existing affine outputs.

### Stronger lower frame

For a natural source with only linear atom bounds below W, squared errors can
require a larger frame than W^W. The coefficient-only replacement of the lower
ordinate `W*Z` by `2W*Z`, with Z positive, is sound. For every integer W>=1,
the recurrence

    U_0=0, U_1=1, U_(j+1)=2(W+1)U_j-U_(j-1)

immediately gives `U_j(W+1)=j (mod 2W)`, since `2(W+1)=2 (mod 2W)`.
Thus a positive lower ordinate divisible by 2W has canonical index at least
2W. Its abscissa is at least `(W+1)^(2W)`. For W>=2 this exceeds
`4W^(2W)`: Bernoulli's inequality gives `(1+1/W)^W>2` for integer W>1.
No parity split is needed. Completeness can simply choose a canonical lower
index that is a positive multiple of 2W.

This proves the frame lemma itself. The producer must still authenticate the
literal lower ordinate equation and positivity of its factor Z, and preserve
all common-root congruences when choosing the later principal A. These are
separate construction checks, not consequences of the recurrence alone.

## 5. Why naive adjacent-base sharing fails

For `T_n=2An-n^2-1`, direct elimination of A gives

    (q+1)T_q-qT_(q+1)=q^2+q-1.

Hence `gcd(T_q,T_(q+1))` divides the nonzero, framed quantity q^2+q-1. A proposed
common-modulus pooling proof cannot simply replace both huge T's by that gcd;
it loses the enormous modulus that forces ordinary squared errors to vanish.
This does not rule out more elaborate product-modulus constructions, nor does
it prove that two coordinates per existing block are minimal.

## Scope

All unmodified signed Pell classification, semantic anchor, CRT compiler,
finite syntax and C222/ZF/ZFC calibration statements remain explicit inherited
dependencies. This review establishes the new ordinary arguments and exact
finite algebra listed above. It neither proves consistency nor claims a newly
kernel-checked end-to-end theorem or global variable minimality.
