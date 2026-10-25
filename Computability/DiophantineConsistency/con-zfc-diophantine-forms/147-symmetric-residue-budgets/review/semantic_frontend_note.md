# A separate semantic direction: optimize the proof calculus for arithmetic

This note is a mathematically motivated follow-up, not a newly materialized Diophantine endpoint or a claim of worldwide priority. It identifies a safe source redesign and an important failed shortcut.

## A genuine obstruction to a tempting simplification

One cannot simply replace the condition c != a,b on the entire C222 bundle by c>max(a,b), or by the polynomial substitution c=a+b+d+1. ProveIt Source 142 gives a full model of that weakened whole-bundle calculus in ZFC. The atomic membership-vacuity conjunct is part of the logical completeness machinery; thinning it changes the theory. The result is recorded at:

- `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-187.md`, section "Source 142: what the theory results permit", commit e0c98c629bf10d30b695884f6b1d2ab361bdf513.

This is why a guard-erasure substitution without a new calibration proof would be invalid.

## A safe split at the semantic source

Write the original bundle as B(a,b,c)=not(V(a,b,c) -> K(a,b,c)), where V is membership vacuity and K=nks is the negated seed core. Retain all logical rows, modus ponens, generalization and truth. Replace the bundle axiom by two families:

1. V(a,b,c) for every c != a,b, with the full original freshness range.
2. not K(0,1,d+2) for d in N.

Each new axiom is derivable in C222: project the two conjuncts of the relevant old bundle, using its classical propositional basis. Thus a refutation in the split calculus implies one in C222.

For the reverse consistency implication, the existing full-seed proof already uses only public roles 0 and 1. For an arbitrary named relation psi, it uses m=not not psi, k=enc(th(m)), and proves k>1 and that k is fresh for m. Hence the needed seed instance occurs in the new family with d=k-2. Full atomic vacuity, retained without restriction, supports exactly the same equality-interpretation completeness proof. The separated V(0,1,k) and not K(0,1,k) reconstruct the old named bundle by propositional logic. The remainder of the existing lower model construction is unchanged.

The source-facing proof interfaces are:

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEqCodes222.lean`: its helper and equality-transport proofs use only G, rho1, rho2, rho6, MP, GEN and propositional logic; the final `vrel_of_bundle` is exactly the separately retained full vacuity family.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEind222.lean`, particularly `c222_of_thmK` and `c222_complete` (the bundle is used in the logical transport only to obtain full `vrel_of_bundle`).
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedDirect222.lean`, theorem `seed_direct` (only roles 0 and 1, k>1, fresh k).
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedInterface222.lean`, `enc_bundleNF` and the definition of `FullSeed`.

This is an ordinary modular calibration argument. It has not been implemented as a new Lean source file in this turn. The core-only cofinal principle is already anticipated by Source 142 and should be credited to it.

## A side-condition-free three-parameter axiom presentation

For arithmetic compilation, a guarded family can be a poor trade even if it is efficient in a small machine. Every triple (a,b,c) of naturals with c!=a,b lies in one of the following five polynomial charts, with u,v,w in N:

| Chart | a | b | c |
|---|---|---|---|
| c below both | u+v+1 | u+w+1 | u |
| a<=b<c | u | u+v | u+v+w+1 |
| b<=a<c | u+v | u | u+v+w+1 |
| a<c<b | u | u+v+w+2 | u+v+1 |
| b<c<a | u+v+w+2 | u | u+v+1 |

All generated triples are fresh, and the case distinction on the relative positions proves exhaustive coverage. There is no extra disequality witness. Therefore the five polynomial values V(a,b,c) in these charts replace the guarded vacuity family exactly.

The only original four-parameter logical row is Lukasiewicz's implicational axiom. Replace it by K(a,b), S(a,b,c), and Peirce(a,b). These use at most three parameters and generate exactly the same classical implicational logic under modus ponens. Conversely each is derivable from the original Lukasiewicz basis, as in the supplied source. The other seven logical axiom families already have at most three parameters.

Consequently the split calculus has 16 unguarded polynomial axiom maps N^3 -> N: seven retained logical families, three classical implicational families, five vacuity charts and one fixed-role seed family. Together with truth, modus ponens and generalization this gives 19 local branches. All numbers are ordinary natural code values and no undecidable choice of coefficients is involved.

This offers a precise engineering question: does deleting one CRT witness column outweigh the additional shallow axiom branches after complete polynomial compilation? A local branch count is not a final variable or operation count. No improvement is claimed without rebuilding the actual CRT/Pell equation, authenticating its literal source and proving the bounds and maps needed by that compiler.

## Further research question

Optimize a complete numerical proof calculus for total Diophantine cost (schema arity, bounded-witness columns, nonlinearity and degree), rather than for Turing-machine state count. The inherited small-machine calculus and the arithmetic-optimal calculus need not be the same. The safe fixed-role split provides a calibrated starting point; the whole-bundle countermodel identifies a restriction that must not be silently made.
