# A smaller implication proof and a stronger abstract theorem

## Exact result

The current primary K215 proof contains 117 numbered helper schemas in
DomRho8.lean at commit aa66d0a33f1f8237a348899eb8095b045a502832.
The delivered rewrite retains 84 of these schemas. Thirteen changed bodies
are ordinary schematic instances of modus ponens; dependency pruning removes
33 helpers. The final proof of unrestricted rho8 needs 82 of the numbered
helpers; the other two retain the existing public distribution theorem.

The important improvement goes beyond proof text compression. The bootstrap
now works for an arbitrary implication operation on an arbitrary carrier,
using a reflexive relation closed under insertion into either operand.
It needs neither a distinguished truth code nor the numerical identity
I(0,0)=0. No decoder, injectivity, order antisymmetry, bottom element, global
inhabitedness, or separate transitivity premise is assumed.

The independently checked generic theorem imports Init only. Its three
public results rho8_all, composition and distribution have empty axiom
reports. The numeric adapter preserves all original public declarations,
including DomImp, le_l, le_r, sub, wim00, and the original three theorem
names and types. It additionally exports rho8_all_of_restricted without
DomImp.truth. The existing KCodeDom equivalence and explicit typed clients
have been compiled against the adapter.

This is a local theorem and calibration-module check. It is not a fresh
rebuild of the complete K215 machine-to-ZFC endpoint, an internal PA proof,
a new machine table, or a state-minimality theorem.

## Abstract statement

Let A be any type, I : A x A -> A any binary operation, and R a relation
such that:

* R(x,x) for every x;
* R(u,x) implies R(u,I(x,y));
* R(u,y) implies R(u,I(x,y)).

Let T be a predicate on A closed under modus ponens:
T(I(x,y)) and T(x) imply T(y). Write

    rho(a,b,c,u) = I(I(I(c,u),a), I(I(a,c),I(b,c))).

Assume T(rho(a,b,c,u)) whenever R(u,a). Then T(rho(a,b,c,u))
for every a,b,c,u, with no dominance restriction.

The proof first allows an arbitrary proven element tau. The auxiliary seed
is then eliminated by choosing tau = rho(a,a,a,a); this belongs to T by
reflexivity. The target's first argument a supplies the witness, so no
Nonempty A instance is required. The empty-carrier case is vacuous.

A corollary takes A to be binary implication trees and R to be syntactic
subterm. The calculus consisting solely of modus ponens and rho instances
with u a subterm of a derives exactly the same formulas as unrestricted
rho plus modus ponens. SubtermImplication.lean states this as
provable_iff_full. It includes no truth axiom.

The theorem also applies to raw, noninjectively represented codes: Language
imposes no decoding or uniqueness condition on I. This matches the user's
permitted freedom to use codes that do not have a conventional formula
interpretation. It does not by itself supply a complete replacement ZFC
calibration or a cheaper emitter.

## Why the final deduction argument disappears

Use x=>y for I(x,y). The retained derived schemas include:

    B: (x=>y) => ((y=>z) => (x=>z))
    C: (x=>(y=>z)) => (y=>(x=>z))
    K: x => (y=>x)
    P: ((x=>y)=>x) => x.

B gives composition of proved implications. B and C together give the
following derived rule for every fixed z:

    T(x=>y) implies T((z=>x)=>(z=>y)).

Put f=(c=>u)=>a, g=a=>c and p=(c=>u)=>c.
B gives f=>(g=>p), while P gives p=>c. Lift the latter under g and
compose to obtain f=>(g=>c). K gives c=>(b=>c); lift that under g and
compose once more to obtain f=>(g=>(b=>c)), exactly rho(a,b,c,u).

This direct proof removes the auxiliary Proof inductive family,
proof_sound, discharge_aux, and discharge. General distribution is no
longer a dependency of rho8_all. It remains exported for API compatibility.

## Representative new schematic shortcuts

The delivered JSON and generator record every actual substitution. Three
particularly useful ones, in the original helper names, are:

    cd75 := MP(b52, cd92)
    cd103 := MP(cd104, cd69)
    b60 := MP(b22, b18).

These formulas are not merely used under their old dependency order: the
generator topologically reorders the proof after the replacements. For
example, cd92 does not depend on cd75, so placing it earlier introduces no
cycle. Every target retains its exact original statement. The symbolic
auditor verifies the full instantiated major formula is
I(instantiated minor, exact target), then the kernel checks the resulting
Lean proof.

The b10 shortcut uses b4 and b1. Combined with the other rewrites it
eliminates b5 through b9, including the old bottom-only rho8 instance.
Two remaining redundant derivations of T(0), at b39 and cd47, are replaced
by the auxiliary seed proof. All numerical zero-normalization wrappers can
then be removed before abstracting the carrier.

## Measured artifacts

The original numeric file is 30,114 bytes and 517 lines.
The final generic core is 19,752 bytes and 388 lines; the compatibility
adapter is 2,526 bytes and 70 lines. Combined: 22,278 bytes and 458 lines,
a 26.02% reduction in source bytes. The numbered helper reduction is
117 to 84 (28.21%). These figures include comments and the newly exposed
generic interfaces, so they are source-size measurements, not proof-object
or end-to-end build-time measurements.

The curated packet omits the intermediate numeric-only rewrites. The final
integration consists of DominatedImplication.lean plus DomRho8.adapter.lean
copied to DomRho8.lean in the repository module directory.

## Reproduction and provenance

In the curated packet, enter generation/ and run:

    python3 regenerate.py --check
    python3 regenerate.py --out /fresh/output
    python3 search_shortcuts.py

The first command verifies the pinned original hash, rederives all
thirteen substitutions, checks acyclic dependencies, and reproduces both
final Lean files byte for byte. The second writes repository-layout source
files without touching the original. The third replays the finite
one-step discovery search over the existing schemas; no optimality claim
is made.

shortcuts.json stores only the selected pairs, source hash, commit, and
roots. templates/ contains the generic interfaces, direct final argument
and adapter. Python output is untrusted proof data; the Lean and Rocq
kernels remain the verification boundary.

Original proof ancestry is Source 149 / CD230, as credited by the original
DomRho8 source. This contribution consists of the selected schematic
shortcuts, dependency pruning, abstract-carrier theorem, removal of the
seed premise, direct B/C/K/P finish, and subterm instance. The inherited
mathematics and original authorship are not claimed as new.

## Further checked strengthening: four finite schemas

A separate extension replaces the structural-subterm restriction by exactly
four explicit rho8 families: a=u, a=I(x,u), a=I(I(u,x),y), and
a=I(I(I(x,u),y),z). These correspond to paths empty, R, LL, and LLR from
the first argument to the fourth. FourShapeImplication.lean is checked with
empty axiom reports and does not assume the four-shape relation is closed
under arbitrary contexts. The seed is again derived from an allowed row.

KCodeFourShape.lean preserves every other C222 rule, including truth and
both bundle guards, and proves CFour n iff C222 n for every natural-number
code. The numerical equivalence and its consistency corollary also have
empty axiom reports. Only the propositional interface is free of arithmetic
side conditions. The new formalism is not a compiled TM or a state-saving
claim. A future emitter can test whether constructing the four fixed
contexts is smaller than the original numerical guard, but larger emitted
terms and extra parameters may offset any saving.

FOUR_SHAPES.md provides the exact schema table and scope. The deterministic
specialize_four.py script reproduces the independently checked source;
four-shapes.json inventories every guard occurrence. This extension is
separate from the compatibility patch, whose generic core remains unchanged.

## Which 215-state alternative is easiest to certify?

CM215 remains the strongest choice for a short additional correctness proof
relative to the existing primary K215 endpoint. Its source, calculus,
scheduler, and startup frame are unchanged; an invariant and two local
three-step blocks transfer halting equivalence. The six changed transition
rows do not require rebuilding its logical foundation.

This conclusion is already in the recent proposal packets. In particular,
k215-simplification-2/formal_cm215/CM215Core.lean has a compiled exact dense
equivalence to KDense215.machine215. Its CM215ZFCAdapter.lean is a short
composition with the existing endpoint but was explicitly left uncompiled
with the full ZFC closure in that packet. A stale headline saying no
alternative has a complete compiled endpoint must not be read as saying no
compiled exact-machine transfer exists.

Context-return machines need matched multi-step blocks and extra entry
facts. Rebalanced sources need new source/decoder coverage. Zero-credit or
GC-ZC machines offer appealing source-level schedulers but require new
compiler, guard-safety and startup bindings. Their lower local counts do
not establish a shorter complete formal proof than CM215's transfer.

No 214-state construction follows from this implication result alone.
Removing the truth premise from the implication bootstrap does not
authorize deleting the numerical calculus's truth rule or changing the
machine's initial register frame. Those interfaces must be justified
separately.

Pinned references:
https://github.com/VladimirReshetnikov/ProveIt/blob/aa66d0a33f1f8237a348899eb8095b045a502832/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DomRho8.lean
https://github.com/VladimirReshetnikov/ProveIt/blob/aa66d0a33f1f8237a348899eb8095b045a502832/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/formal_cm215/README.md
https://github.com/VladimirReshetnikov/ProveIt/blob/aa66d0a33f1f8237a348899eb8095b045a502832/Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/README.md
