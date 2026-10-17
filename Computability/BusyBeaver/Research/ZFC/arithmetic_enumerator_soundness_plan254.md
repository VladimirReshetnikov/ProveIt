# Plan for internal scheduler soundness

Status: the [proof-constructor equations](arithmetic_proof_constructors254.md)
are checked. The [stack-tail bound](arithmetic_stack_tail254.md) and
[bounded stack-certificate predicates and operations](arithmetic_stack_certificate254.md)
are now checked too. Runtime preservation and time induction remain
implementation work.

The reverse implication must start from a certified state. Arbitrary dirty
registers can contain falsity in cache and halt on NIP without any accepted
proof. The literal initial state has top, cache and stack zero; proof code 1
certifies their truth entries. Pointer, next candidate and accumulator need
no logical certification.

Replacing the native `C254(x)` predicate with `exists p, value(p)=x+1`
would make its unbounded stream invariant Π2. Instead, carry one bound on
all proof witnesses already present:

```text
ProvB(B, x) := exists p <= B, value(p) = x+1

StackB(B, z) := 1 <= B and
  forall k <= z, ProvB(B, first(tailIter(k, z)))

WorkingB(B, w) := ProvB(B, top(w)) and ProvB(B, cache(w))
                 and StackB(B, stack(w)).
```

`tailIter` will be the represented iteration of Cantor's second projection.
Its total Δ1 graph and the validator's total Δ1 graph make `ProvB`, `StackB`
and `WorkingB` Δ1. The changing bound stays existential, so
`exists B, WorkingB(B,w)` is Σ1. This bound is carried from the initial state
and explicitly enlarged at each command; no selection of all stack proof
witnesses or Collection principle is required.

The tail proof needs strict decrease at every nonzero stack code and zero
absorption. A pointwise Σ1 induction should give
`tailIter(k,z)=0 or tailIter(k,z)+k <= z`, hence zero after `z` iterations.
Indices beyond the bounded stream certificate therefore read truth, certified
by proof code 1. This yields an unbounded consequence for local push/pop
lemmas without putting an unbounded universal inside time induction.

MP constructs one new proof witness on success and uses truth on failure.
DROP and a continuing NIP reuse existing witnesses. AX adds eight logical
axiom proofs, a GEN proof for the old cache and a gated bundle proof for the
new top; its fixed pushes also preserve the old top. An enlarged bound such
as the old bound plus the finitely many new codes plus one covers every
witness. A halting NIP has cache 1, whose witness is an accepted falsity proof.

For a fixed certified initial state, the proposed time invariant is

```text
(run(time,start)=0 and exists p, value(p)=2)
or
(run(time,start) != 0 and exists B, WorkingB(B,working(run(time,start)))).
```

This is Σ1. Preservation and initial certification would show that every
internal halting time supplies an accepted internal falsity proof. A fixed
sentence and arithmetic completeness can then give the PA reverse implication,
complementing the checked [forward theorem](arithmetic_enumerator_refutation254.md).
Internal binary simulation and C254/ZFC proof transformations remain further
obligations.
