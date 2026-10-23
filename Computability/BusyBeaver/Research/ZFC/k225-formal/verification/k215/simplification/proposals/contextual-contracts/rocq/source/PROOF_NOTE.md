# Mathematical proof and integration contract

Write `R ~ S` for `forall i, R i = S i`. It is an equivalence relation. The
register update operation preserves it whenever the assigned values agree.
Consequently increment at register `r` preserves it.

For arbitrary registers `a,b`, two increments commute *pointwise*:

```text
inc_b(inc_a(R)) ~ inc_a(inc_b(R)).
```

If `a=b`, the expressions are identical. If `a<>b`, evaluate at an arbitrary
register `i`. At `i=a` both sides give `R(a)+1`; at `i=b` both give `R(b)+1`;
elsewhere both give `R(i)`. This uses decidable equality of natural numbers,
not function extensionality.

A pure two-increment node can only terminate normally, with output given by
the two corresponding updates. Inverting the actual RM execution derivation
proves that statement; nonnormal exit constructors have impossible increment
premises. This proves `swap_increment_node` for any pair of register indices,
including equal ones.

The generic transport assumes, for each node, either equal ordered child
edges or a whole-node semantic contract preserving exits and relating the
output register files. Induct on an execution derivation. At a primitive rule,
use pointwise equality to preserve the inspected register value and update.
At an unchanged node, transport its child derivations in order, passing the
related intermediate register files to the next induction hypothesis. In the
loop-restart constructor there are three premises: car, cdr, and restarted
node; transport all three. At a substituted node apply its entire local
contract. Thus every finite source derivation is matched by a target
derivation with the same exit and related output registers.

Induct once more on root iteration. A halt iteration transports its root
derivation; a normal iteration transports the root derivation and applies
the iteration induction hypothesis at the related output files. Using the
same argument in both directions establishes halting equivalence from every
initial register function.

For the concrete programs, the finite distinction `n=188`, `n=190`, or neither
discharges the transport premise. The two exceptional nodes use the generic
increment theorem. Every other node has definitionally the old body. There
are no unverified finite-search premises in the new semantic result.

## Exact boundary to the larger source proof

This result only uses structured `run` and `iter_halts`, from the actual
`K230.RM` definitions. It does not import `RMEquiv` or conclude a new
`rm_halts p215` theorem. The complete certificate-free route must add a
kernel-checked source/CFG normalization theorem or another equally sound
bridge. The current production source theorem and its normalized certificate
remain the correctness fallback throughout that integration.
