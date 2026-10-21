# Independent review: correlated R(b,c)/I(b,c) union

Date: 2026-10-20.

## Verdict

**PASS as an ordinary, unbounded syntactic consistency proof.** The correlated
four-D-family invariant closes under MP after admitting exactly the exceptional
code4. All H/D, D/H, D/D, truth-zero, retained-row, and quantified-monotonicity
branches check out. The full native seed is included. The fixed seven-node
proof of code4 was independently recalculated and passes.

This is a distinct proof from the earlier all-membership invariant. In
particular, that invariant excludes code4, whereas the present calculus
really derives it. No result from that earlier invariant was assumed here.

Reviewed artifacts:

- `research217_mixed_tag_basis/MIXED_R_I_OBSTRUCTION.md`
  SHA-256 `c4186c5ce28910a4595b0a18b483134c0b80e83e522fbf709e4e5d160e9da1f3`.
- `research217_mixed_tag_basis/FIXED_CODE4_RECEIPT.json`
  SHA-256 `3ac2dd91696c044d5a9bb12380e14f32c41ac45afa3f27881c12f24d55305e15`.

No received checker, executable, proof search, or target machine was run.
This is not a proof-assistant certification, source-size bound, runtime
result, or physical-state lower bound.

## Native binding and zero arithmetic

The rows and full seed agree with the native source audited in the earlier
reviews in this directory. The actual nks222 core is Q_c-headed; placing
its complete body in the arbitrary z of the strengthened bundle includes
the entire support-bearing seed, without projection. Omitting gate
restrictions only enlarges the auxiliary invariant.

The relevant native inequalities are stronger than mere component
domination: I(x,y)>=4x and I(x,y)>=4y. Thus a natural number equal to an
I term containing itself as a field must be zero, and injectivity then
forces the other fields to zero. The source uses these inequalities
correctly. It does not treat raw0 as a distinct atom: I(0,0)=0 throughout.

No independent identity schema is present in the actual native rules or
the auxiliary class. A generator that happens to evaluate to an identity
is still covered through that generator's case.

## H majors: exhaustive possibilities

Use the source's notation u_e(y,z)=I(y,z)+e, and D abbreviations

    w=u_e(y,z), c=I(z,w), x=u_d(b,c),
    a=I(I(x,z),I(y,z)).

An H_t(A,B,C) major requires I(I(C,u_t(B,C)),A).

- Truth0 forces A=C=0 and u_t(B,0)=0, hence t=B=0; output0.
- GEN has the wrong outer tag. Monotonicity and r1/r2/r4 have Q
  antecedents, r3/r5/G have E antecedents, and code4 has R antecedent.
- Bundle would identify a Q core with u_t, whose tag is 0 or1.
- r6 forces C=C_i(A)>0 and u_t(B,C)=1. Tag0 cannot match; tag1 forces
  B=C=0. Thus no rho6-trigger family survives.
- An H minor gives exactly the admitted correlated D family.
- A D minor forces C=a, u_t(B,a)=c, A=I(b,c). Because c is I-headed,
  t=0; injectivity gives B=z and a=u_e(y,z). Since a is I-headed, e=0.
  Now a=I(y,z)=I(I(x,z),I(y,z)), forcing a=x=y=z=0. Then c=0 and
  x=u_d(b,0)=0 force d=b=0. The major's conclusion is0.

These are all last-generator cases. In particular the H/D exclusion
depends on exact correlations, not merely the tags of its fields.

## D majors: truth, retained rows, and H minors

A D major requires I(a,c).

Truth0 requires a=c=0. Expanding c and a forces e=d=b=y=z=0, so the
conclusion I(b,c) is0. There is no missed nonzero conclusion from the zero
alias. GEN and all Q/E/R-antecedent generators fail by tags. Bundle has
consequent1, not I-headed c. r6 forces X_j(c)=a, hence 1=I(y,z), impossible.

For an H_t(A,B,C) minor, exact field matching gives

    C=x, u_t(B,C)=z, A=I(y,z),
    I(A,C)=z, I(B,C)=w.

Therefore z=I(I(y,z),x). The native factor-four bound forces z=y=x=0.
Then x=u_d(b,c)=0 forces d=b=c=0, and c=I(0,u_e(0,0))=0 forces e=0.
Thus D/H detachment also has only output0. This derivation checks the
source's field equations rather than inheriting a fixed-orientation argument.

## Independent D/D audit

Let the D major have unprimed parameters and the D minor primed ones.
Matching the minor with I(a,c) yields

    a=I(a',c'), c=I(b',c'),
    a'=I(x,z), c'=I(y,z), b'=z, c'=u_e(y,z).

Hence e=0. Expanding the primed terms gives

    x=I(x',z'), z=I(y',z'), z'=y, z=u_e'(y',z').

Hence e'=0. Since x is I-headed and x=u_d(b,c), d=0. Comparing
I(b,c)=I(x',y) gives b=x' and c=y. Thus

    y=I(z,I(y,z)).

The factor-four bound gives y=0, and injectivity then gives z=0.
Successively z'=y'=b'=c'=0, while

    x'=u_d'(0,0)=d', b=d', c=0.

There is no further restriction on d'. The output is exactly I(d',0),
namely0 for d'=0 and4 for d'=1. Thus admitting code4 is necessary, and
the four correlated D families suffice: no additional mixed family is
left unexamined.

## Old forbidden shapes and MP closure

The old forbidden shapes I(E(i,j),1), X_i(a), and
I(V(a,b,c),Q_k z) remain excluded. H/D have I-headed immediate fields;
code4 has an R-headed antecedent, so none supplies these shapes. Truth
cannot match the positive targets. The retained possibilities reduce to
the familiar E/Q collision for r1 versus X and Q/R collision for r6 versus
the bundle antecedent; all other cases fail directly by tags. These are
last-generator inversions, independent of MP closure.

The MP proof is a well-founded induction on the major's finite S witness.
Truth as major forces both its fields0. Code4 as major would need F as
minor, excluded by the root-tag invariant. GEN cannot be an I-headed
major. Monotonicity strips Q from the minor, uses the induction hypothesis
on its smaller premise witness, and rebuilds Q. Retained rows use the
three forbidden shapes or Q stripping/rebuilding. H and D use the
exhaustive analyses above. Numerical aliasing does not compromise this
witness-size induction.

Actual finite derivations consequently embed in S, whose outputs all have
residue0 or2. F=1 is absent. This proves the stated ZFC-provable consistency
result, including the full retained seed and rules.

## Fixed certificate: independent arithmetic verification

I did not read or execute the supplied check_fixed_code4.py. I freshly
implemented only native P, I, H_0/H_1, and the fourfold Z iteration using
exact integer arithmetic. All seven reported decimal codes matched, and
all three MP equations held:

    node2 = I(node1,node3),
    node5 = I(node4,node6),
    node6 = I(node3,4).

The verified Z chain is 4,40,3280,21523360. The first two MPs respectively
derive D_(0,1)(0,0,0) and D_(0,0)(1,0,0); the final MP is precisely the
exceptional D/D case above. There was no enumeration or formula search.

Independent receipt:
`research217_theory_review/MIXED_R_I_CODE4_INDEPENDENT_RECEIPT.json`.

## Further supported corollary and limits

Every S generator other than code4 either has no outer I or has an
immediate antecedent of tag0,2,or3. Therefore every actual theorem I(v,x)
whose v is membership-headed must be exactly4. This strengthens the
source's final bootstrap observation: I(F,F) is absent, and every
K(F,b)=I(F,I(b,F)) is absent because I(b,F) cannot be0. It does not exclude
the actual theorem I(F,0), nor claim that all identities are absent.

No remaining ordinary proof obligation was found in the stated theorem.
Other mixed builders, changed correlations, extra identity/K schemas,
source compilation, enumeration fairness, and concrete blank machines
remain outside this review. The consistency obstruction alone is not a
physical-state lower bound.
