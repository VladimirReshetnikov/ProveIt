# Proof and implementation interfaces

## Target

Fix ordinary classical first-order ZFC with its precise recursive axiom
presentation and a primitive-recursive finite-proof predicate. The requested
contract is:

    ZFC proves: not Halt_blank(M) iff Con(ZFC).

Equivalently, ZFC proves that M halts iff a finite ZFC refutation exists.
A PA proof of the same equivalence is an optional strengthening, not the
user's present minimum requirement.

## Proven mathematical results in this report

1. For any logically reflexive seed, pure subset-bounded range-pure seeded
   closure and the corresponding mixed-bound schema are deductively
   equivalent, even without Extensionality.
2. Extensionality plus either the point or subset pure kernel is deductively
   equivalent to ZF without Foundation and Choice, with full Separation and
   functional Replacement.
3. EC plus equality-free pure subset closure has effective refutation
   translations to and from the extensional subset theory. The ordinary
   Foundation/Choice/presentation bridges yield ZFC equiconsistency.
4. The specified theorem-only Hilbert record system has a finite accepted
   refutation iff the equality-free theory has a refutation; the specified
   fair search halts exactly in that case.

These are ordinary mathematical arguments. The report does not distribute
serialized first-order derivations for these theorems or their proof templates.

## Noncircular bootstrap

- Constant relations plus reflexive seeding and range purity give exact
  subset-bounded constant classes, in particular singletons.
- A singleton input outputs its member; a nonsingleton input outputs its
  subsets. The exclusive cases have separate subset bounds.
- Positive closure yields a transitive H with a subset H. It need not put
  a in H. No Extensionality, Separation, Union, or Foundation is needed here.
- A transitive superset of b turns every output in b OR subset b into a
  subset of H. Bounds are used pointwise; no simultaneous choice is made.

The singleton/subset switch is inherited from the pinned source manuscript.
Its use at this earlier bootstrap stage and the resulting bound-absorption
are the additions relative to that manuscript.

## Reference certificate contracts

Executing syntax contains membership, implication, universal quantification,
and primitive bottom. Logical equality and measurement holes are rejected.
Every record generates a conclusion; there is no admission rule. Theory
axioms are universally closed, so theorem-only generalization is sound.
Modus ponens uses strict earlier-line references and alpha-equivalence.

Matrix free variables 0 and 1 are input/output slots. Other free variables
are universally closed parameters. Wrapper binders are fresh above all
matrix names. Substitution is capture-avoiding. Bound slots are not renamed
as free slots. The generator emits the boundedness implication as syntax;
it does not evaluate the semantic antecedent.

The final target is the primitive bottom node. It is not self-membership.
The benchmark's self-membership alias requires IR and collision/freshness
arguments; it must not be copied into an IR-free checker without replacement.

## Remaining formal artifacts

- First-order derivation constructors for the fixed bootstrap and each
  translated axiom instance; uniform correctness over arbitrary formula codes.
- An audited ordinary-ZFC proof predicate and its foundation-free/Choice bridge.
- Verified parser, axiom generator, checker, and complete enumeration.
- Register/TM compiler, tape/register invariants, exact blank initialization.
- Certified optimizer passes and a literal table with digest and state count.
- An explicit endpoint derivation in the requested metatheory, not merely a
  theorem under unexamined proof-assistant axioms.

New formal work should follow the repository's direction to use Lean.
There is no Lean file in this delivery. No missing compiler bundle is claimed
recovered, and no historical Coq build is claimed rerun.

## Negative claims not warranted

- 79 formula nodes do not imply fewer than 254 TM states.
- No strong-bisimulation merges do not imply global minimality.
- All graph states reachable do not imply blank-tape reachability.
- Passing finite tests does not prove the full infinite schema or evaluator.
- No refutation in a finite interval does not establish consistency.
- Bare consistency does not imply Sigma-1 soundness, so it alone does not
  justify every two-sided independence assertion for a consistency machine.
