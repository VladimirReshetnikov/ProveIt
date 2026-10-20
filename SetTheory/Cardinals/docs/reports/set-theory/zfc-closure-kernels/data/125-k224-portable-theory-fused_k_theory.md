# Eliminating eight redundant negations from K230's numerical axiom bundle

## Proven result

The following is a syntactic optimization of the existing K230 calculus. It
does not require a new set-theoretic interpretation, an equality quotient, an
alpha-conversion argument, or a freshness premise beyond the unchanged native
gate. Its eventual machine-state effect must be measured separately.

Write I(A,B) for the literal numerical implication constructor, Q_x(A) for
the literal universal-quantifier constructor, and F=1. Define

    N(A) = I(A,F),
    A & B = N(I(A,N(B))),
    E_x(A) = N(Q_x(N(A))).

The complete retained logical rows prove explosion F -> A, double-negation
introduction and elimination, implication congruence, and quantifier
congruence. Consequently every occurrence of N(N(A)) in a formula-constructor
expression can be replaced by A, with finite derivations of both directions.
This assertion is uniform in arbitrary natural-number formula codes A. It
does not presume that A has any particular decoded syntax.

## Four cancellation sites

For arbitrary codes A,B and any variable label x,

    E_x(A & B)
       = N(Q_x(N(N(I(A,N(B))))))
      <-> N(Q_x(I(A,N(B)))).

The equality is literal constructor expansion; the biconditional is a
derivable logical equivalence. It removes two calls of N. K230's core has
three such sites:

1. the outer container witness;
2. the existential support input;
3. the selected witness for a subset request.

There is a fourth site in the final bundle:

    A & (B & C)
       = N(I(A,N(N(I(B,N(C))))))
      <-> N(I(A,I(B,N(C)))).

Thus the complete axiom-bundle expression removes **eight** N constructors.
All eight logical rows, both vacuity implications, the freshness gate, the
number of pushed axiom slots, and the proof search protocol can remain the
same.

## Exact replacement formula

Let m be the opaque matrix code, k the private binder label, a the input
label, and b the output label. Let R=M(b,k), and let

    S = Q_k(I(M(k,a),M(k,b))).

Define, bottom-up,

    W = Q_b(I(m, N(Q_b(I(m,N(R)))))),
    U = Q_a(I(S,W)),
    H = Q_b(I(R, N(Q_a(I(m,N(U)))))),
    Kf(a,b,k,m) = N(Q_k(I(I(m,R),N(H)))).

The fused vacuity bundle is

    V_R = I(M(a,b), Q_k(M(a,b))),
    V_E = I(Eq(a,b), Q_k(Eq(a,b))),
    Bf(a,b,k,m) = N(I(Kf(a,b,k,m),I(V_R,N(V_E)))).

As in the existing source, specialize k=m=c. Return 0 when c=a or c=b;
otherwise return Bf(a,b,c,c). No old source code may simply be renamed to
the fused code: this is an explicit changed axiom family, with a finite
derivation translation between the two families.

## Numerical derivation argument

Let L be any numerical deductive relation closed under modus ponens and
GEN and containing K230's retained logical rows rho1,...,rho8. In fact this
argument only needs the K/S/Peirce consequences of rho8, rho2, and rho6.

1. Explosion is derivable from rho6(0,A). The latter is
   E_0(Q_0(A)) -> A. From F and K one gets E_0(Q_0(A)), because
   E_0(Q_0(A)) is itself an implication into F. Discharge F.
2. Classical propositional logic then gives N(N(A)) -> A and A -> N(N(A)).
   The upstream proof already exports `thm_F` and `thm_DNE` for every nat A.
3. If L proves A -> B, GEN gives Q_x(I(A,B)); rho2 then gives
   Q_x(A) -> Q_x(B). Apply in both directions for quantifier congruence.
4. Classical propositional logic gives congruence under both arguments of
   I, and hence under N. Induct on a formula-constructor context.
5. Apply steps 2--4 at the four sites above. Both old-bundle -> new-bundle
   and new-bundle -> old-bundle are theorems of the retained logical core,
   for every a,b,c, even when labels coincide or m is a low code.

The existing native gate is kept exactly. At enabled triples, replace an
old bundle axiom by the new bundle axiom followed by the uniform implication
back to the old one. At disabled triples both emit 0. The other axioms and
MP/GEN are unchanged. Structural induction on a finite derivation gives
primitive recursive proof transformations in both directions. Therefore,
for every conclusion n, not merely for n=1,

    thm_old(n) <-> thm_fused(n).

In particular the old and new enumerators halt on the same inconsistency
predicate once the new source is bound to the unchanged enumeration protocol.
The old K230-to-ZFC calibration can be reused through this explicit proof
translation. None of these derivations uses the new set-theory bundle to
justify its own equivalence, so there is no circular completeness argument.

The final fused bundle remains a literal implication into F, hence its
numeric code is divisible by 4 and cannot equal F=1. Its outer implication
has positive right argument, so it is not code 0 either.

## Provenance and limits

Primary source is Elliot Glazer's `k230-rocq` at commit
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`:

- `coq/settheory/KCode230.v`: literal I/N/and/ex constructors and complete
  K230/vacuity/gated bundle.
- `coq/logic/Codes230.v`: retained rho1--rho8.
- `coq/logic/Comp_Prop230.v`: `thm_F`, `thm_DNE`, deduction theorem and
  propositional logic inside the numerical calculus.
- `coq/logic/CD230.v`: derivations of K, S and Peirce from rho8.
- `coq/logic/Thm230.v`: the exact finite numerical proof relation.
- `coq/settheory/KUpperConsistency.v`: finite-refutation consistency
  reduction to StandardZFC.

The released proof is an external axiom-free Rocq theorem. A report may give
the ordinary ZFC formalizability of the finite syntactic translations, but
must not describe a new kernel-checked theorem for the changed machine
unless that theorem is actually compiled and checked. The optimization is
classical double-negation elimination, not a new logical principle. Its
possibly new contribution is applying it to the literal K axiom emitter and
demonstrating a smaller complete binary machine.

For the main machine's restricted equality helper, the independently
regenerated `rel_helper_fusion_certificate.json` uses a separate schematic
helper binder kappa. `bind_rel_fusion_certificate.py` instantiates it with
the actual Rel(a,b) code and matches the exact emitted canonical formula.
The helper's consistency calibration is proved separately in
`k_equality_helper_extension.md`; it is not a propositional equivalence
with full primitive equality vacuity.

Conditional seeding and deleting global support are not used by the main
machine. `conditional_k_calibration.md` gives the completed conditional
calibration, while `k_schema_obstructions.md` gives the support-deletion
countermodel. These are separate research results.
