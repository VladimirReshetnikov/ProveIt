# Proposed Lean integration — not an implemented formalization

Repository snapshot: 725d2ebb6909fe11a13a92354c0f47367a3cbbf5.
The package does not contain new Lean proof files or a successful Lean build
receipt. The following are proposed module boundaries and theorem obligations.

## 1. Word semantics

Define binary words as finite Boolean lists; define a nonempty cyclic list of
appendants and a phase-indexed partial step. Empty input has no successor.
Define exact finite execution without post-halting padding.

Prove radix value of concatenation and injectivity at a fixed length. Preserve
written zero symbols through a length/scale coordinate. Never identify the
empty word with a nonempty word whose radix value is zero.

## 2. First-failure product

Define formal resource histories over integers, including their continuation
after an illegal event. For fixed natural consumptions and productions, prove:

- legality implies every falling-factorial factor is positive;
- the first disabled event still has a nonnegative marking;
- a forbidden consumption contributes a specific zero factor;
- the full product is positive exactly for legal schedules, zero otherwise.

Natural subtraction is inappropriate for the formal history. Keep all casts
explicit until resource nonnegativity has actually been established.

## 3. FIFO reconstruction

Prove the semantic theorem independently of radix arithmetic: global per-queue
word identities plus prefix resource legality reconstruct the actual queues.
The inductive invariant is that each queue is the suffix of its already
produced prefix after removing all earlier consumed symbols.

Generalize to several queues with simultaneous read-before-write events.
Any control-table validity premise should be separate from availability.

## 4. Polynomial syntax and evaluation

For T >= 1 use an index type of size T+1 for the stream polynomial, assigning
its last coordinate to the slack. Define the residuals as integer
MvPolynomials and prove their evaluation identities. Named prefix products
are expressions, not additional variables.

Establish separate endpoints for:

1. a polynomial zero implies an exact execution;
2. an exact execution provides a canonical zero;
3. all zeros for fixed parameters are equal;
4. degree and variable-count bounds.

For the quartic compiler, use an index type of size 3*T-2. Its critical
invariant is valid radix scale from the initial code. Show that an empty
source forces the impossible equation 2*s_next = 1. No general predicate
for being a power of two is needed in the residual system.

## 5. Table interpolation

For a B-symbol alphabet, formalize K=(B-1)! clearing of the Lagrange basis.
Use integer Horner evaluation for the scaled interpolants. Prove the weighted
prefix-product formula for K^T times the content residual and the explicit
cleared guard. Do not insert rational constants into an integer-polynomial
reifier and merely assume that final denominator cancellation occurs.

## 6. Arithmetic DAG reflection

The Python JSON is untrusted input. A future Lean checker should verify that
node references point backward, reify the permitted operations, and prove
that deterministic DAG evaluation equals evaluation of the reified polynomial.
Only then connect exported circuits to the semantic compiler definitions.

Checking a numerical witness is not the same as verifying compiler soundness,
completeness, or uniqueness. Preserve these distinct trust boundaries.

## 7. Existing repository interfaces

The inspected MRDP guide documents Diophantine.mrdp, mrdp_iff, and the finite
polynomial and general trace interfaces. The bounded queue compiler does not
need MRDP. MRDP becomes relevant when proving a fixed-arity representation
of unbounded halting, but its interface alone does not preserve witness
uniqueness. Do not label that last step finite-fold or single-fold without
a separate fiber-control proof.
