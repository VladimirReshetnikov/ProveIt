NEWEST-PARAMETER INTRODUCTION: EXECUTABLE CANDIDATE
================================================

The mathematical correctness and completeness proof is a separate artifact.
These files implement the proposed three-family calculus, provide matched
controls, and reproduce finite implementation evidence. They do not claim
proof-assistant verification.

Selected standalone module: checker.py.
Exact 1925-byte normalized copy: checker_normalized.py.
Primitive-recursive bounded-certificate variant: checker_fuel.py.

The unbounded input is exactly [goal, proof]. The bounded input is
[goal, proof, fuel] with a nonnegative integer fuel. Acceptance is exactly
exit status zero and ACCEPT followed by a newline. Exceptions reject.

TERMS AND FORMULAS
------------------
Zero is integer 0. Negative integers are free numerical parameters.
Positive integers are de Bruijn indices; the nearest binder has index 1.
The only compound term is [counter, seed, body], a counter-aware,
successor-seeded recursor. The body binds state at index 1 and counter at
index 2. Its equations are

  R(0,a;i,u.h) = S(a),
  R(S(c),a;i,u.h) = h[c/i,R(c,a;i,u.h)/u].

Successor S(a) is [0,a,0]. Supplied term/formula fields are computation
normal forms, except for the auxiliary template of discharge (see below).
Formulas are [s,t] for equality and [B] for D(x,y).B. D binds y at index 1
and x at index 2. The ordinary reading is

  exists x (B(x,0) -> forall y B(x,y)).

The same traversal validates sorts, handles scopes, substitutes without
capture, and normalizes computations. When successor recursion unfolds,
the outer counter is substituted first, protecting the inner state slot;
then the state is substituted. This order is essential for open terms.

CONTEXT AND RULE PACKETS
------------------------
The context is a list of clauses (antecedent, unary body). Empty antecedent
means unconditional. The fixed initial context is [([], [1,1])], universal
reflexivity. At context length n the available parameters are -1,...,1-n;
the next fresh parameter is b=-n. Each context extension allocates one name.

1. ['u', j, t, p]
Use clause j at t. Its conclusion is the normalized body instance.
When the antecedent is nonempty, p proves it. For an unconditional clause
p is deliberately unused; null is the conventional payload.

2. ['i', p]
The goal is D(x,y).B. The witness is fixed to the newest existing parameter
1-n, or equivalently zero when n=1. There is no witness input. Let
C(y)=nf(B(1-n,y)). If C(0) is literally r=r, add the unconditional assumption
C(b); otherwise add C(0). In that local context p proves C(S(b)).

3. ['e', B, F, s, t, major, eq, branch]
major proves D(x,y).B in the outer context. At fresh b, append the clause
[nf(B(b,0)); y.nf(B(b,y))]. In this context eq proves s=t and branch proves
nf(F[s]). The exported outer goal must be nf(F[t]), so b cannot escape.
F has a distinguished free bound slot, at index 1 outside its own binders.

TEMPLATE COMPLETION
-------------------
The auxiliary template F need not itself be canonical or scope-complete.
Its structure is traversed and its children are sort-checked before erasure.
Both instantiated normalized formulas are checked: one is the branch goal
and the other is the exported goal. Extra free parameters or dangling bound
indices are therefore allowed only if computation erases them in both
instances. Replacing all such extra parameters by zero and normalizing gives
an ordinary well-scoped template with the same two instances. The separate
written proof supplies this completion lemma. control_template_validation.py
uses the extra template-validation traversal for the stricter interface.

The equality proof is checked before either template instance is formed.
All active formulas and equality endpoints retain complete sort/scope checks.
In particular, malformed term arities and Boolean values are rejected even
inside erased template bodies.

CONTROLS AND EVIDENCE
--------------------
control_explicit_witness.py differs only by supplying and checking a witness
in the introduction packet ['i', witness, p]. The finite-fuel control adds
the identical budget mechanism. verify.py translates every new certificate
to this matched control by inserting the known newest parameter. It also
completes templates and replays the certificates with the stricter template
validator. These executable translations are untrusted proof producers.

audit_multisub.py is the independent simultaneous-substitution implementation
used for comparison. audit.py additionally implements a named-variable
normalizer and independent numerical interpretation. Its constructors include
Name(1) and Name(2) proofs with no supplied existential witness, general
equality transport through successor and through D, and a used induction
hypothesis. The template-completion boundary has explicit positive fixtures.

Run:
  python3 verify.py
  python3 measure.py
  python3 checker.py < examples/name_one_without_witness.json

verify.py executes normal and optimized Python CLI checks, adversarial
rejections, exact and one-short fuel boundaries, malformed-budget rejections,
capture controls and oracle comparisons. Concrete Python resource limits
can reject sufficiently large finite certificates. The bounded checker charges
each normalization traversal and proof-checking entry; every recursive cycle
passes through a charged entry. It defines a primitive-recursive bounded
certificate relation without adding a normalizer-totality axiom to the theory.

PROVENANCE
----------
Pinned repository: VladimirReshetnikov/ProveIt,
commit 11814771b7490dfbea0ed5fcf0f5b23586334764.
reference/explicit_name.py is the unchanged checker_explicit.py from
docs/incoming/ipra_clause_discharge_2026-11-11.zip under ConciseIPRA.
reference/inferred_opening.py is the unchanged code/checker.py from
docs/incoming/ipra_inferred_witness_2026-11-11.zip under ConciseIPRA.
Their inherited MIT No Attribution license is included. The traversal and
clause machinery are adapted from those sources and uniform_binding.

The compact 508-byte, 256-token, and 276-AST repository profiles remain
smaller. The positive source-size comparison is with the transparent,
fully checked clause modules and the matched explicit-witness control.
