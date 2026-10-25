# Normalize the sign of the private common Pell helper

This separate ordinary theorem replaces two helper sign predicates by one
affine predicate in the exact principal Round15 body. No source, projection,
engine run or numerical improvement is materialized. The body equations stay
the same, but the inverse witness map may change five private body coordinates.
It is not a fixed-whole-body guard deletion.

Write V=v251,d=v252,e=v510,H=v254,P=v511 and Bpart=v255. All coordinates
are integers. Keep the complete522-coordinate/446-row body and all original
guards except guard27(d>=0) and guard30(V-1>=0). Replace those two guards by

    Bpart-4>=0,

represented by one fresh Legendre graph. Its actual comparison base is
Bc=Bpart+1, so the new predicate says Bc>=5. No sign of F,A,U or any primary
Pell pair is needed in the normalization proof.

## Exact affine involution

Define R on the entire integer body space by

    V'=-V, d'=-d-2, e'=-e-2, H'=-H, P'=-P,

and fix every other coordinate. Applying R twice is the identity. The complete
source occurrence lists for these five coordinates are:

| Coordinate | Name | All body row occurrences |
| --- | --- | --- |
|251|shared_index.V|205,206,207,434|
|252|shared_index.q4minus1|207|
|510|shared_index.Vquotient_minus1|433|
|254|mul.452|205,206|
|511|mul.727|433,434|

The five affected residuals are exactly

    r205=H-A*V,
    r206=U²+V²-H²-1,
    r207=Bpart-4V(d+1),
    r433=P-v509(e+1),
    r434=V-P.

Direct substitution gives r205(Rx)=-r205(x), r433(Rx)=-r433(x),
r434(Rx)=-r434(x), and r206(Rx)=r206(x), r207(Rx)=r207(x).
Every other body residual contains none of these five coordinates and is
unchanged. Thus EACH of all446 residuals is preserved up to a fixed sign on
ALL integer assignments. Consequently the complete body sum of squares is
exactly invariant under R, not merely on its zero set. This is an algebraic
identity and has no Pell or power-theorem dependency.

Every remaining old guard expression avoids the changed coordinates. Only
the two omitted expressions mention them: guard27 is d, and guard30 is V-1.
Their auxiliary triples are603..605 at row473 and612..614 at row476. All
old triples are pairwise disjoint and occur only in their own guard graphs.
Every retained graph and its witnesses can therefore remain unchanged under R.
The new expression Bpart-4 is also fixed by R.

## Normalize a zero and restore the old guards

Suppose a body zero satisfies all retained guards and Bpart>=4. Row207 gives

    V(d+1)=Bpart/4>0.

There is no division in the emitted equation; this is an ordinary consequence
of its exact integer equality. In particular V is nonzero and d+1 has its sign.

If V>0, keep the body tuple. Integrality gives V>=1 and d+1>=1, hence d>=0.
If V<0, use R. Then V'=-V>=1 and d'+1=-(d+1)>0; integrality gives d'>=0.
All body rows remain zero and all retained guards keep the same values and
witnesses. The old e need not have a sign premise: its reflection is exactly
what keeps row433 valid with v509 fixed. The old product and every primary
ordinate remain fixed.

Choose fresh Legendre witnesses for d_normalized>=0 and V_normalized-1>=0.
The two private old triples then restore the old guard rows without changing
any other equation. This yields a zero of the exact old guarded system.

Conversely, an old guarded zero has V>=1 and d>=0. Row207 implies Bpart>=4,
so Bpart-4 is a nonnegative integer and has a Legendre representation
a²+b²+c(c+1). Keep the whole body and retained witnesses, discard the two old
private triples, and choose this new triple. This is a zero of the proposed
guard policy. The elementary Legendre/parity lemma is the only existence
theorem added to the polynomial row identities.

These maps preserve every body coordinate outside{251,252,254,510,511}.
In particular every arithmetic base/exponent/output, the frame W,A,Zminus1,
the common U, comparison base and its quotient, every primary/comparison pair,
and every native semantic port are fixed. The actual complete frame/power
inventory contains none of the five changed coordinates. The set of body
zeros projected to that fixed complement is exactly the same for the old and
proposed guard policies. No whole-body bijection, unique guard witnesses or
polynomial choice of Legendre witnesses is asserted. Sign normalization is
piecewise identity/R and can identify reflected tuples.

## F-only and joint ordinary compositions

The same reflection proof holds if F's guard is also omitted, or if both F
and A guards are omitted, because those targets and all their predicates are
fixed by R. First normalize V,d and restore their two old guards. Only THEN
apply the separately sealed F-only theorem when A's guard is retained, or the
separately sealed JOINT(F,A) theorem when both guards are absent. Supply their
fresh triples afterward if composing all the way to the original source.
The F-only theorem is never invoked with its A premise missing. No claim is
made about reflection indices in an already compacted or projected chart;
any materialization needs its own complete coordinate and guard maps.

## Finite scope and remaining work

CERTIFICATE.json pins the actual rows, occurrences, all old guards, the affine
involution, fixed coordinate/semantic interfaces and witness schedule. The
standalone stdlib checker will collect every reflected body row and the whole
sum of squares, check every graph/private occurrence and exercise actual
altered-artifact controls. Its executable must receive full root review BEFORE
its first execution. No incoming executable, optimizer or engine is invoked.

A later guarded-source layout and any projection/translation must be emitted
and independently checked separately, with complete inverse/free-coordinate
accounting and every quartic coefficient. No operation, variable, degree,
height or optimum claim follows from this ordinary replacement alone. The new
cap prototype retains its initial helper guards; transferring this reflection
to that different kernel is a separate future proof. Canonical files, common
reports, frozen parents and Lean are unchanged.
