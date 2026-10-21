# Independent audit: union of all six membership orientations

Date: 2026-10-20.

## Verdict and scope

**PASS as an ordinary, unbounded syntactic consistency proof.** The reviewed
argument proves in ZFC that the exact native calculus remains consistent when
all six indicated membership-valued rho8 families are present simultaneously,
with truth, MP, GEN, every retained native row, and the whole support-bearing
seed-K bundle. Its treatment of cross-orientation detachment is essential and
correct. No false constructor equality, omitted generator branch, or gap from
the zero alias was found.

This is an independent mathematical audit, not a new Lean/Rocq build. No
received executable, proof checker, search program, or target machine was run.
The original proof uses no Heyting representation or completeness theorem.
This review makes no machine-state bound or machine-runtime claim.

The reviewed proof is:

`research218_round2_rho8/MIXED_ORIENTATION_UNION_OBSTRUCTION.md`

SHA-256: `17c9d774b65cf538b2cbef6b4f99cfbbd99649cec178c4a824952c22388ba4a0`.

The following sections spell out the abbreviated inherited branches rather
than simply accepting the prior fixed-orientation review.

## 1. Literal native binding and constructor facts

I inspected the local native source as inert text:

- `research218_companion/evidence/logic/KCode230.v`;
- `research218_companion/evidence/logic/Codes230.v`;
- `latest219_baseline/k225-formal/rocq224/src/Codes222.v`;
- `latest219_baseline/k225-formal/rocq224/src/Thm222.v`.

The constructors are literally

    P(x,y) = tri(x+y)+y,
    I(x,y) = 4P(x,y),
    R(x,y) = 4P(x,y)+1,
    Q_i x  = 4P(i,x)+2,
    E(i,j) = 4P(i,j)+3.

Consequently each constructor is injective in both fields, their residues
are disjoint, I(x,y) >= x,y, and R(x,y) > x,y. Also Q is positive,
I(x,y)=0 iff x=y=0, and R(x,y)=1 iff x=y=0. These conclusions follow from
the displayed pairing definition, not an assumed free formula algebra.

The retained rows expand to

    r1(i,j)   = I(Q_i I(E(i,j),1),1),
    r2(i,x,y) = I(Q_i I(x,y), I(Q_i x,Q_i y)),
    r3(a,b,c) = I(E(a,b), I(R(c,a),R(c,b))),
    r4(i,j,x) = I(Q_i Q_j x,Q_j Q_i x),
    r5(a,b,c) = I(E(c,a), I(R(c,b),R(a,b))),
    r6(i,x)   = I(I(Q_i I(Q_i x,1),1),x),
    G(a,b,u)  = I(E(u,a),I(E(u,b),Q_{R(a,b)} E(a,b))).

This agrees with the invariant's native rows. In particular, rho6's two
negations have not been omitted or collapsed.

Write V(a,b,c)=I(R(a,b),Q_c R(a,b)). The native source defines nks222(a,b,c)
with outermost constructor Q_c, and defines

    bundle222(a,b,c) = I(I(V(a,b,c),nks222(a,b,c)),1).

The actual calculus admits this only when c differs from a and b. For this
review choose the stronger invariant containing every

    B(a,b,c;k,z) = I(I(V(a,b,c),Q_k z),1),

with arbitrary parameters and no gate. Every actual full bundle is an
instance: choose k=c and z equal to the entire literal body of nks222.
The body, including its support content, is neither dropped nor projected.
Allowing additional bodies and disabled parameter triples is a harmless
overapproximation for consistency.

## 2. Explicit invariant and all generator categories

For each of the six builders U(a,b,c), put

    H_U(a,b,c) = I(I(I(c,U(a,b,c)),a),I(I(a,c),I(b,c))).

The four builders R(a,b), R(b,a), R(a,c), R(c,a) are called V-type here; each
has U(a,b,c)>a. The remaining two are

    W_0(b,c)=R(b,c),   W_1(b,c)=R(c,b).

Both have W_t(b,c)>c and W_t(b,c)=1 iff b=c=0. Define

    p_t(b,c) = I(c,W_t(b,c)),
    J_t(b,c) = I(I(p_t(b,c),c),I(b,c)),
    A_tu(b,c,d) = W_u(d,p_t(b,c)),
    h_tu(b,c,d) = I(I(A_tu(b,c,d),c),I(b,c)),
    D_tu(b,c,d) = I(I(h_tu(b,c,d),p_t(b,c)),I(d,p_t(b,c))).

Let S have finite witnesses with generators r1--r6, G, all strengthened B,
all six H families, both J families, all four D families, all identities
I(x,x), GEN, and quantified monotonicity

    S(I(x,y)) implies S(I(Q_i x,Q_i y)).

MP is not a generator. No claim that the added identities, J, D, or
monotonicity are actual theorems is needed.

The following categories exhaust every possible last witness constructor:

1. Identity.
2. r1, r2, r4, and monotonicity: immediate antecedent has Q tag.
3. r3, r5, G: immediate antecedent has E tag.
4. r6: immediate antecedent is I(Q_i I(Q_i x,1),1).
5. B: immediate antecedent is I(V,Q_k z), consequent is 1.
6. H: immediate antecedent is I(I(z,U(x,y,z)),x).
7. J: immediate antecedent is I(p_t(y,z),z).
8. D: immediate antecedent is I(h_tu(y,z,e),p_t(y,z)).
9. GEN: the whole output has Q tag.

Every output has residue 0 or 2. Thus no R- or E-headed number is in S.
A Q-headed output must end in GEN, so S(Q_i x) implies S(x).

## 3. The three inherited forbidden shapes really remain forbidden

First consider I(E(i,j),1). GEN has the wrong outer tag. Identity would
equate E with 1; monotonicity and r1/r2/r4 have Q antecedents; r6/B/H/J/D
have I antecedents; and the possible E-antecedent rows r3/r5/G have I
consequents, not 1. This exhausts the generators.

Next consider X(i,x)=I(Q_i I(Q_i x,1),1). Identity would equate Q with 1.
Monotonicity has Q consequent; r2 has I consequent and r4 has Q consequent.
Rows r3/r5/G have E antecedents, and r6/B/H/J/D have I antecedents.
GEN has the wrong outer tag. The only remaining case r1 would require
E(i,j)=Q_i x after repeated injectivity, impossible by residues.

Finally consider I(V(a,b,c),Q_k z). Identity would equate I with Q.
Monotonicity and r1/r2/r4 have Q antecedents; r3/r5/G have E antecedents;
GEN has the wrong outer tag. H/J/D have I consequents and B has consequent
1, all different from Q_k z. An r6 instance could have Q_k z as its free
consequent, but matching its antecedent with V requires its Q-headed first
inner field to equal R(a,b). This is impossible. Thus every strengthened
bundle antecedent, not merely the original fixed body, is excluded.

None of these inversions invokes MP closure.

## 4. Every H-major/minor interaction

Fix an H_U(a,b,c) major, write v=U(a,b,c), and suppose its required minor
I(I(c,v),a) belongs to S. Categories 2, 3 and 9 above fail immediately by
antecedent or outer tags. A B minor equates Q_k z with membership code v;
a D minor equates its I-headed p_t with v. These are impossible for all six
orientations.

### 4.1 V-type major: v>a

- Identity forces a=I(c,v)>=v>a.
- An arbitrary H minor, whatever its orientation, forces its first
  parameter x=v and a=I(I(x,z),I(y,z))>=x=v>a.
- A J_t(y,z) minor forces z=v and a=I(y,z)>=z=v>a.
- An r6 minor forces v=1 and c=Q_i I(Q_i a,1). For R(a,b) or R(b,a), v=1
  forces a=b=0 and the major's output is the admitted identity
  I(I(0,c),I(0,c)). For R(a,c) or R(c,a), v=1 forces c=0, contradicting
  the positive Q value just obtained.

Thus all four V-type major families are closed under detachment even after
adding every other orientation and every mixed auxiliary.

### 4.2 W_u major

Here v=W_u(b,c)>c and the required minor is I(p_u(b,c),a).

- Identity gives a=p_u(b,c), and the output is exactly J_u(b,c).
- A J_t(y,z) minor gives c=p_t(y,z), z=W_u(b,c), hence
  c>=z=W_u(b,c)>c.
- An r6 minor gives W_u(b,c)=1, hence c=0, together with
  c=Q_i I(Q_i a,1)>0.
- The B and D cases are the tag collisions already recorded.

It remains to inspect every H minor. Injectivity always gives

    c=I(z,U_minor(x,y,z)),
    x=W_u(b,c)>c,
    a=I(I(x,z),I(y,z)).

If its builder is V-type, then U_minor(x,y,z)>x, so

    c>=U_minor(x,y,z)>x>c.

If its builder is W_t, then c=p_t(y,z), x=W_u(b,p_t(y,z)), and
a=h_tu(y,z,b). The major's consequent is therefore exactly

    I(I(h_tu(y,z,b),p_t(y,z)),I(b,p_t(y,z))) = D_tu(y,z,b).

The index order is correct: t is the minor's orientation and u is the
major's orientation. This checks all 36 H/H orientation pairs, including
the genuine mixed W_0/W_1 and W_1/W_0 detachments. No cross-orientation
case was silently inherited from a single-builder argument.

## 5. Every J major is inert

Fix t,b,c and write w=W_t(b,c), p=I(c,w). A J_t(b,c) major requires I(p,c).
Again the Q/E-antecedent and GEN categories fail by tags. The remaining
cases are exhaustive:

- Identity forces p=c, contrary to p>=w>c.
- r6 forces w=1, hence c=0, and simultaneously c=Q_i I(Q_i c,1)>0.
- B forces its Q core to equal w.
- Any H minor forces x=w and c=I(I(x,z),I(y,z))>=w>c. Its orientation
  is irrelevant.
- Any J_u minor forces z=w and c=I(y,z)>=w>c.
- Any D_uv minor forces its I-headed p_u to equal w.

Thus no J major has an S minor, for either t.

## 6. Every mixed D major is inert

Fix t,u,b,c,d. Write w=W_t(b,c), p=I(c,w), and
h=I(I(A_tu(b,c,d),c),I(b,c)). A D_tu major requires I(h,p).
The Q/E-antecedent and GEN categories fail by tags. All remaining cases:

- Identity gives h=p; their right fields force I(b,c)=w.
- r6 gives h=I(Q_i I(Q_i p,1),1), so 1=I(b,c).
- B would give p=1.
- Any H minor has consequent I(I(x,z),I(y,z)); equality with p forces
  I(y,z)=w.
- Any J_v(y,z) minor has consequent I(y,z)=p, forcing y=c,z=w. Its
  antecedent I(p_v(y,z),z)=h then forces z=I(b,c), hence w=I(b,c).
- Any D_vr(y,z,e) minor has consequent I(e,p_v(y,z))=p, forcing
  p_v(y,z)=w.

Every case is an I/R residue collision. None uses t=u or any hidden
relationship between the two builders. The four mixed D families are all
inert as majors.

## 7. MP, GEN, truth, and the zero alias

Prove MP closure by induction on a finite witness of S(I(x,y)), retaining
an arbitrary S(x) witness as an additional parameter. This is well founded
even when numerical codes coincide: the induction measure is witness
structure, not code size.

- Identity returns the supplied minor.
- A GEN witness cannot conclude an I-headed major.
- For monotonicity, injectivity identifies x=Q_i r and y=Q_i s.
  Strip Q from the minor, apply the induction hypothesis to the strictly
  smaller premise witness S(I(r,s)), and rebuild Q by GEN.
- r1 needs Q_i I(E(i,j),1). Strip Q and apply the first forbidden shape.
- r2 needs Q_i I(r,s). Strip Q and use the admitted monotonicity generator.
- r3/r5/G require an E-headed minor, absent from S.
- r4 strips two Q prefixes and rebuilds them in the exchanged order.
- r6 and B require the second and third forbidden shapes, respectively.
- H has only the identity, J, or mixed-D outputs proved above.
- J and D cannot fire.

This is not a circular assumption of MP closure. Every actual derivation
now embeds in S by induction on its derivation: all actual axioms are
admitted, truth 0 is I(0,0), GEN is a generator, and MP is the proved closure.

The special code 0 causes no missing branch. The proof never treats 0 as a
fresh disjoint atom: it has I residue, and constructor injectivity applies
to I(0,0) exactly as to other I codes. All p_t satisfy p_t>=W_t>c>=0,
so p_t is strictly positive. An H consequent can itself be zero, but it
still has residue 0 and remains covered by the identity/generator argument.
No exclusion uses a false claim that every I-headed code is positive.

Finally, every S generator has residue 0 or 2. Code F=1 has residue 1,
so it is not in S and has no actual derivation.

## 8. Calibration consequence and exact remaining obligations

The finite witness construction and its inductions are directly
arithmetizable in ZFC. Therefore ZFC proves consistency of the full union
calculus, and likewise of every subunion of these six orientation schemes.
If ZFC is consistent, it cannot also prove that this consistency implies
Con(ZFC), by the usual second-incompleteness consequence. This rules out
these exact modifications as a ZFC-provable consistency calibration.

There is no remaining ordinary mathematical obligation identified within
that stated theorem. Separate obligations, not supplied by this result, are:

1. A machine-checked formalization, if one is wanted; prior Lean checking
   of a single fixed orientation does not certify this union extension.
2. An exact machine/calculus correspondence before drawing conclusions
   about any concrete transition table.
3. Any claim about extra K/S axioms, implication-headed fourth builders,
   raw pairing builders, dominated-U families, or other changed calculi.

The result does not show that a <=217-state construction is impossible.

## Source hashes and provenance

The prior local review and pinned upstream ordinary proofs were also read:

    c0c3dbdf578f5370746f24278fa1c2c23b6cc9801d8dab6c91418ab1457d546d
    research218_round2_rho8/UPSTREAM_FIXED_ORIENTATION_CLOSURE_REVIEW.md

    1700dd54f5abe35a4ef9a8f052c403842abfa92e9b8f90b7888ad8bac977dc9d
    latest218_baseline/k219-fourth-parameter/diagonal-invariant/invariant.md

    5fca0235bdf77dc3c1767dcfa15e00d45c66ea7b7686a9801d3d26c94061807c
    latest218_baseline/k219-fourth-parameter/six-orientations/evidence/rbc-invariant.md

Their upstream attribution is commit
`7c3bca89c19b3a33eab255cb8b6ff2a31bc50fcc`; this audit used the local inert
copies and did not refetch or compile that commit.

Native files actually inspected have hashes:

    2a5fd8a170dedfd732347e0da969230cfc9321d3d8f71729711f5cf3b12f045e
    research218_companion/evidence/logic/KCode230.v

    ab41044fd2feb34cf595c6ea2d174c768c2c6cde14204d03dbee77c37d8f618e
    research218_companion/evidence/logic/Codes230.v

    b929fb1fbf42194d21ae25e1e2f7ebf87dbf364e180702667213c867e67a1bed
    latest219_baseline/k225-formal/rocq224/src/Codes222.v

    991e4895fd9a37b17801f3555499051338e7ad01d265e0053257f9d33f185708
    latest219_baseline/k225-formal/rocq224/src/Thm222.v
