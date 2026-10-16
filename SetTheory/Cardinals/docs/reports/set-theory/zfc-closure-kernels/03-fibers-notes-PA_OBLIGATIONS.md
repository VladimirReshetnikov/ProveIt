# From the paper theorem to a literal PA-certified machine

## Fixed target

Use ordinary classical first-order ZFC with a fixed effective axiom
presentation and a chosen proof predicate. The eventual theorem must be:

    PA proves (exists t: Halt(M,t)) iff (exists p: Prf_ZFC(p,bottom)).

The machine model in the article is a deterministic one-tape, two-symbol,
blank-tape machine, with a two-way infinite tape and L/R moves. State counts
exclude the specified halt state/convention. The final artifact must state
its literal transition table, initial state, halt convention, and hash.

## Required proof interfaces

### A. Object syntax and source axiom constructor

Freeze the syntax, variable encoding, parameter conventions, logical proof
calculus, bottom formula, and primitive-recursive proof predicate. Give an
axiom certificate format for EFH containing the arbitrary matrix, its input
and output variables, parameters, and the required fresh variables.

Prove in PA that the constructor is total and produces exactly permitted
instances. Check substitutions and renamings under binders. Bound variables
in inserted matrices must not capture external variables; conversely the
seed must not accidentally become a free matrix argument.

The Python AST in this package is a reference syntax/measurement utility,
not this proof predicate or a proof-producing implementation.

### B. Local proof templates

For the equality-bearing source, implement the paper's derivations in this
order:

1. False fiber gives Empty Set and transitive containment.
2. Transitive containment makes a constant exact fiber yield Separation.
3. Exact singleton fibers plus transitivity yield Pairing.
4. Transitive containment plus Separation gives Union; the subset matrix
   gives Power Set directly.
5. Guarded functional matrices give Replacement; the successor matrix gives
   Infinity.
6. Conversely, define each unique exact fiber, collect these by functional
   Replacement, and perform the two omega-recursions defining the hull.

These steps must be uniform in matrix codes, not merely individually
provable for each externally named formula. Prove correctness of the local
templates by structural induction, yielding primitive-recursive proof
translations both ways between EFH and the specified ZF-without-Foundation
presentation.

Do not replace functional Replacement by full Collection after deleting
Foundation without supplying a separate argument.

### C. Equality-free interpretation

Replace equality by equality of membership profiles. From EC prove
reflexivity, symmetry, transitivity, membership congruence in both
arguments, and formula invariance. Translate every equality axiom and
inference rule. The translated Extensionality instance is a logical
identity and every translated EFH instance is an allowed equality-free
instance.

In the reverse direction, derive EC from ordinary Extensionality and copy
the equality-free EFH instances. This route does not need the prior
nonextensional bisimulation construction. It does not justify deleting EC.

### D. Foundation and Choice

Implement the standard class relativizations: first the well-founded
cumulative hierarchy, then the constructible hierarchy. For every source
axiom code, produce a proof of its relativization in the preceding theory.
This includes uniform Separation/Replacement templates. Use ranks of
unique outputs to bound interpreted Replacement images.

These are syntactic transformations of finite proofs. Do not assume a set
model of all of ZFC, an inaccessible cardinal, a global truth predicate,
or a reflection principle stronger than what the source proves.

Compose A–D to obtain primitive-recursive f and g and PA proofs of:

    Prf_source(p,bottom) -> Prf_ZFC(f(p),bottom)
    Prf_ZFC(q,bottom)    -> Prf_source(g(q),bottom).

### E. Enumeration and backend

Give a complete enumeration of all finite certificates. Prove that each
candidate is either rejected after a finite computation or accepted
exactly when it is a valid refutation. Prove that every valid finite
certificate is eventually visited. Malformed inputs must not create
nontermination that blocks the enumerator, or trigger accidental halts.

Then prove the simulation chain from the enumerator to the literal table,
including blank-tape initialization, all variable-freshness conditions,
stack invariants, decoder coverage, arithmetic overflows in finite
representations, and the halt test. The proof transformation f/g is not
executed by the machine.

## What has and has not been supplied

The article supplies mathematical proofs for the new local equivalences
and explains why they give PA-verifiable proof translations. It invokes
the standard effective Foundation/Choice reductions at the paper level.
This package does not implement A–E as formal proof-producing software,
does not emit a PA proof object, and does not supply a new TM table.

A theorem checked by Coq/Lean in its native metatheory is useful evidence,
but is not by itself an export of the equivalence to PA. For the upstream
254-state project, additionally audit the actual definition of its ZF/ZFC
endpoint and the arithmetic principles used by its verification.
