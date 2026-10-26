# Independent audit: fixed-role seed calculus

## Audited claim

Let C* have truth 0, modus ponens, generalization, rho1--rho6, growG,
rho8, guarded membership vacuity RV(a,b,k) for k != a,b, and the
one-parameter schema Seed(c)=N(nks(0,1,c+2)). Then, relative to the
identified inherited ordinary first-order and seed-to-ZF constructions,
ZFC proves C*(1) iff ZFC has a finite syntactic refutation.

The audit inspected the actual local copies of KCode222.lean,
KEqCodes222.lean, KEind222.lean, KSeed222.lean,
KSeedInterface222.lean, KSeedDirect222.lean, KEndpoint.lean,
KLowerQHyp.lean, KQ1Model.lean, and the shell source. It did not compile
a new Lean development or replay all transitive dependencies.

## Direction from the new calculus

The old bundle is N(I(RV,nks)), propositionally RV AND N(nks).
The old classical basis derives both projections. Consequently every
guarded RV axiom is an old theorem, and every new Seed(c) follows from
the old bundle with roles 0,1 and k=c+2; its two guards hold because
k>=2. All other axioms and rules are unchanged. Induction on a finite
C* proof therefore gives an old C222 proof with the same conclusion.
The inherited KEndpoint upper implication and ConstructibleChoice
translation then give a ZFC refutation from C*(1).

## The completeness interface really needs only RV

KEind222.c222_of_thmK has one direct use of a projected bundle:
the vacRel branch invokes vrel_of_bundle. This is supplied immediately
by the new guarded RV axiom. Its helper and rho7 branches use
helper222 and rho7_222, whose proofs in KEqCodes222 use only retained
rho1, rho2, rho3, rho5, rho6, growG, generalization, and the classical
basis. The basis in KCode222 is derived from rho8 and rho6, without
using any seed bundle. The interpretation thm_th is independent of
C222 and remains unchanged. Thus the proof of c222_complete ports
word-for-word as an ordinary induction to C* once these named lemmas
are reinterpreted. One must state this generalized lemma rather than
apply the old Lean theorem to a different derivability predicate.

## Only roles 0 and 1 are used in full-seed recovery

For each named formula psi, the retained direct proof takes
m=not not psi and k=enc(th(m)). It proves k>1 and that k is absent
from the free support of m. The new schema contains N(nks(0,1,k)):
choose its natural parameter c=k-2. Guarded RV(0,1,k) also holds.
The classical conjunction introduction derives
N(I(RV(0,1,k),nks(0,1,k))), exactly the one bundle needed by
KSeedDirect222.seed_direct. No arbitrary-role seed instance is used
in that proof. Consequently an irreflexive model of the named
derivable theory has FullSeed. The retained FormSeed and tagged
quotient argument then proves that such a model permits no ZF
refutation. With generalized completeness, a ZF refutation implies
C*(1). Compose the established ZF/ZFC refutation equivalence.

This direction is an ordinary semantic proof of a syntactic
existence statement. It is not an explicit termwise translation
of every arbitrary old bundle to a new proof, and should not be
described as such. First-order completeness and the retained
seed-to-ZF argument are formalizable in ZFC, so this suffices for
the requested internal ZFC equivalence; it does not prove Con(ZFC).

## Shell recoding and the +2 parameter

The constructor-preserving bijection f fixes codes 0 and 1, and
therefore maps the set of natural codes >=2 onto itself. It need
not satisfy f(c+2)=f(c)+2. To transport a seed with k=c+2, use
the new shell parameter f(k)-2, which is a natural number. The
inverse uses g(k)-2. The correct schema is "all codes k>=2";
the polynomial presentation k=c+2 enumerates that set. Negation,+nks, and the fixed roles are transported through constructor
identities. Disequalities for RV are preserved. There is no
requirement that code size or ordering above 1 be preserved.

## Exact boundaries and remaining obligations

1. The final arithmetic local-rule polynomial must use the new Seed
   and guarded RV as separate alternatives; the old guarded bundle
   cannot merely be relabeled as the new seed.
2. The parent arithmetic bootstrap must be rechecked against the
   actual new code DAG and its parameter/range bounds. Finite code
   identity checking does not establish those unbounded bounds.
3. Keep the exact shell constructor identities, truth/falsity codes,
   and inherited logical interfaces in the theorem statement.
4. Claim an ordinary proof with explicitly inherited dependencies,
   not a newly compiled end-to-end Lean or Rocq theorem.

No mathematical obstruction was found in this restricted-role
seed substitution. Its meaningful novelty is reducing the axiom
schema before arithmetization, while preserving the full model
construction required for consistency strength.
