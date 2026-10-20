# Seed-request K with absorbed equality: source-theory proof

## Claim and proof boundary

The new source composes two independently calibrated reductions from the three
223-state packets at ProveIt commit
`6ab3e41e4dcddfbd7f843bdf4be48ae5c7ba2430`:

1. The seed-request K source from `K223_Construction_2026-10-20 (3).zip`.
2. The merged Euclidean equality/helper row G from
   `K223_Construction_2026-10-20 (2).zip` and the identical core in
   `K223_Construction_And_Research_2026-10-20.zip`.

Let S be the exact native numerical calculus searched by the seed 223 machine,
and SG the exact calculus emitted by `sites222.json`. For every natural formula
code n, an effective transformation of finite derivations establishes

    S proves n  if and only if  SG proves n.

Consequently SG has the same refutation predicate at the literal code 1. The
inherited ordinary mathematical calibration of S therefore yields

    ZFC proves (Con(SG) <-> Con(ZFC)).

Together with the separate enumerator, exact startup and unbounded binary
runtime certificates for the new table, this gives the intended machine
nonhalting equivalence in ZFC. The source proof alone does not prove that a
particular transition table implements the source. No new Rocq/Lean endpoint,
proof in PA, absolute consistency, or unconditional nonhalting is asserted.

The contribution is the measured composition and its exact implementation.
The seed theory itself and its lower/upper consistency translations already
occur in Elliot Glazer's K230 development; the G logical theorem already occurs
in the incoming G223 packet. Neither theorem is presented as newly discovered.

## Literal formula constructors

Write

    P(a,b) = (a+b)(a+b+1)/2 + b,
    I(a,b) = 4 P(a,b),
    R(a,b) = 4 P(a,b)+1,
    Q(a,b) = 4 P(a,b)+2,
    E(a,b) = 4 P(a,b)+3,
    F = 1,
    N(A) = I(A,F),
    Ex_i A = N(Q(i,N(A))).

These are arithmetic constructors on natural codes. Formula algebra is used
at the level of the retained numerical calculus, before any interpretation as
ordinary syntax. In particular F is the designated relative-falsity code 1;
it is not silently treated as a syntactically closed ordinary formula.

Let d_ab=E(a,b), Q_i A=Q(i,A), and kappa(a,b)=R(a,b). The old logical row and
helper are

    rho7(a,b,c) = d_ca -> (d_cb -> d_ab),
    H_eq(a,b) = d_ab -> Q_kappa(a,b) d_ab.

The new row is

    G(a,b,c) = d_ca -> (d_cb -> Q_kappa(a,b) d_ab).

Every numerical triple is covered by G in the same logical-row position as
rho7. The seven other logical rows and the rules MP and theorem GEN remain.
The separate H_eq constructor is removed from the gated theory bundle.

## Uniform interderivation of G and the two old obligations

The following proof is independent of the set-theoretic root. The unchanged
rho8/rho6 bridge supplies classical propositional reasoning. Quantified
monotonicity follows by theorem GEN and rho2. The rho1 instance
Ex_i d_ii yields seriality

    Q_i A -> Ex_i A.

One derivation first generalizes the tautology A -> (d_ii -> A), then uses rho2
and its existential consequence to combine Q_i A with Ex_i d_ii. Thus seriality
does not assume reflexivity, rho7, H_eq, or G. Applying seriality to Q_i A and
then rho6(i,A) yields

    Q_i Q_i A -> Ex_i Q_i A -> A.                         (1)

All uses of GEN here are on derivations with no open hypotheses. Such a theorem
may have free named labels; 'closed derivation' does not mean its formula has no
free labels.

For a fixed x put e=d_xx and z=kappa(x,x). G(x,x,z) and propositional contraction
give

    d_zx -> Q_z e.

Existential monotonicity and rho1(z,x) give Ex_z Q_z e; rho6(z,e) therefore gives
e. Reflexivity is recovered without an old helper or old equality-row premise.
Now G(a,b,a), together with the recovered d_aa, gives exactly H_eq(a,b).

Generalize this recovered H_eq theorem at i=kappa(a,b) and distribute by rho2:

    Q_i d_ab -> Q_i Q_i d_ab.

Compose with (1). This proves Q_i d_ab -> d_ab. Appending that consequence to G
recovers the literal old rho7(a,b,c). Conversely, old rho7 followed by H_eq gives
G by propositional composition. There is no translation of the equality atom
in this interderivation.

The argument is uniform in arbitrary natural a,b,c, including all coincidences.
It never uses freshness of kappa as a premise. The off-diagonal freshness of
R(a,b) is an inherited condition needed for the ordinary equality interpretation,
not an unproved side condition in this syntactic interderivation.

## The exact seed bundles and their gate

For the actual coupled matrix/private code c define

    S = Q_c (R(c,a) -> R(c,b)),
    W = Q_b (c -> N(Q_b(c -> N(R(b,c))))),
    U = Q_a (S -> W),
    H = Q_b (R(b,c) -> N(Q_a(c -> N(U)))),
    C_minus = Q_c (H -> N(W)),
    V_R = R(a,b) -> Q_c R(a,b).

Here C_minus is the negation of the seed core after the recorded classical
fusion. The literal seed bundle used by the prior 223 source is

    B_old = N(I(V_R, I(H_eq, C_minus))).

The literal new bundle is

    B_new = N(I(V_R, C_minus)).

Thus B_old is the fused encoding of And(V_R,And(H_eq,seed_core)), and B_new is
the fused encoding of And(V_R,seed_core). It is important to use this order:
the previous G223 package used an output-root core in a different conjunction
order. Its displayed bundle certificate is not reused by assuming those native
codes are equal.

The new certificate checks the exact three propositional schema roots

    B_old -> B_new,
    B_old -> H_eq,
    B_new -> (H_eq -> B_old).

The gate is unchanged: if c=a or c=b the emitter returns code 0; otherwise it
returns the bundle. For each pair (a,b), choose t=max(a,b)+1. The old bundle at
(a,b,t) passes the gate and hence supplies H_eq(a,b) by its projection. This
allows the old theory to derive every G(a,b,c), for arbitrary c including c=a
or c=b. Conversely G yields H_eq(a,b) for all pairs, so every old successful
bundle is recovered from its corresponding new successful bundle. Disabled
bundle cases remain the identical truth code 0.

Replacing the changed axiom leaves by these fixed finite proofs, preserving
MP and theorem GEN, and inducting on finite derivations proves the claimed
S/SG deductive equivalence on literal natural codes. The fresh gate choice and
proof substitutions are explicit effective operations; they are formalizable
in ZFC. No new model-existence assertion is being substituted for that proof
translation.

## What is inherited from the seed calibration

The ordinary seed theory uses a binary relation R and genuine equality. With
arbitrary finite parameter tuples, write

    Sub(p,u) = forall z (R(z,p) -> R(z,u)),
    W_phi(p,C) = (exists y phi(y,p)) ->
                 exists y (phi(y,p) and R(y,C)),
    H_phi(C) = forall u (R(u,C) ->
                  ((exists p phi(u,p)) and
                   forall p (Sub(p,u) -> W_phi(p,C)))).

Its schema is forall a exists C (W_phi(a,C) and H_phi(C)), with the chosen
conjunction order immaterial in ordinary logic. Its upper reduction from the
output-root theory uses a case split on existence of a phi-output: a witness
supplies the required root; absent a witness, the root request is vacuous. Its
lower reduction supplies K0's seed request at p=a and every hereditary request
via H_phi. These are the `output_root_to_seed` and `seeded_core_to_kp0` routes
in the pinned K230 development, followed by K0's ZFC refutation translation.

The exact native seed adapter already handles the points that ordinary formula
similarity alone would miss:

- The matrix code and private binder are the same actual number c.
- `D_private_fresh` proves c is not free in D(c); at c=0 the decoder is a closed
  tautology with a possible bound occurrence of 0, and at c=1 it is R(0,0).
- At a!=b, the named-to-two-role abstraction uses c!=a,b and private freshness.
- At a=b, the quantifiers shadow the same active role. H simplifies to a
  member-guarded conjunction of existence of a unary witness and W(C).
  An empty C handles the no-witness case; a singleton witness handles the
  other case. The correct split is existence of a witness, not its value at
  the old environment.
- For the lower proof, primitive equality is translated into membership
  indiscernibility before choosing the private code. If psi is the translated
  matrix, choose pp=not not psi and c=enc(pp), with positive distinct active
  names 1 and 3. Then c>3 and every introduced name in pp lies below c.

These obligations are inherited by returning to the exact seed native theory
S. They are not reproved merely by the new G certificate, and the new G code
does not alter them. The standalone source checker reruns the relevant exact
constructor side-condition checks on both its emitted bundle and G row.

## Exact source evidence and state accounting interface

`check_seed_g_source.py` reconstructs `sites222.json` from the pinned seed source:

1. Replace the old equality row's final portion so its consequent becomes
   Q_R(a,b) E(a,b). The complete row grows from 300 to 409 primitive instructions.
2. Delete the 300-instruction H_eq emitter and the additional 27-instruction
   implication constructor from the seed bundle. Its macro word shrinks from
   77 to 65 entries, and its primitive word from 2240 to 1913 instructions.
3. Apply the inherited closed right rotation at address `1110100100111000`.
   This changes no guarded source control edge and lowers the maximum zero run
   from seven to six.

The whole source has 4962+109-327=4744 primitive occurrences, 208 distinct
subtrees including 23 distinct leaves, maximum depth 36, and maximum zero run
six. Its SHA-256 is
`cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e`.

The checker independently compares its entire primitive word with a direct
macro source. It validates nine all-register macro bisimulations against the
pinned Dag230 programs and ProgLib230 contracts, checks symbolic expression
identity for all natural inputs, and compares both complete guarded control
flow resolvers over all 6167 cases. The local emitter comparisons have 1240
seed and 1176 new paired decrement/return boundaries. These are finite
induction certificates, not runs at sampled register values.

`logic/check_seed_g_logic.py` adds the exact seed-bundle tautologies to the G
proofs. It validates 33 closed roots in 298 proof nodes and 272 distinct
formulas. One label assignment is schematic (a,b,c and a symbolic kappa
builder), so all instances are obtained by a homomorphic substitution of
natural labels and evaluation of kappa. Five numerical cases are additional
regressions. The checker rejects any forward proof that assumes OLD_H or
OLD_RHO7 and any reverse proof that assumes G. It exports, reloads, and checks
the proof DAG again.

The table builder and complete new runtime certificates must determine the
actual working-state count; a source DAG count is not a machine-state count.
The two old G decoder helpers can remain required as microcode even after
their original source subtrees disappear. That distinction is retained in the
separate 222-state construction evidence.

## Primary inherited references

The pinned upstream is Elliot Glazer's `elliotglazer/k230-rocq`, commit
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`, especially `KPSeed.v`, `KPrimeCore.v`,
`KQuotZFTransfer.v`, `KQuotZFC.v`, `KDecoder230.v`, `KDecodeFresh.v`,
`KDecodeAbstract.v`, `KDecodeDegenerate.v`, `Dag230.v`, `ProgLib230.v`,
`CD230.v`, and `Comp_Prop230.v`.

The retained K224 source `portable/theory/k_equality_helper_extension.md`
explains the restricted helper's calibration. The seed packet's
`portable/theory/native_seed_request_audit.md` and `report/theory223.tex` give
the native seed interpretation. The G packet's `report/theory.tex` and
`portable/theory/merged_euclidean_helper_certificate.py` give the root-independent
G interderivation. The source checker pins the exact local dependency bytes;
the enclosing package should retain the upstream archives and notices needed
to audit the inherited end-to-end calibration.
