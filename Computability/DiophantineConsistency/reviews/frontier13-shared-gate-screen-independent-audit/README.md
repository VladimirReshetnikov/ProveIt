# Independent review of the shared-intermediate screen

The independent review actually exited 0 in session 72861; receipt SHA-256 is
`879bd295491b0a1c98bc704c21b9f9af5c78cc9d8df1ebf72ce0223774b6a16b`.
The original screen also exited 0 in session 16950. An isolated copy of the
process wrapper exited 0, reproduced its exact saved receipt, and refused a
second overwrite. The independent reviewer and wrapper reject optimized Python.

The family chooses two distinct target rows in order. Both remain binary
`+`, `−` or `×` gates and must use one common value: either an available node
or a literal, or the result of one new binary gate built solely from nodes and
literals available before the first target. The other operand of each target
may be any node available before that target or a literal 0–4; the shared
value may be used twice. Both subtraction orders are included. The second
operand may depend on the first target: exact preservation of the first target
preserves its later dependents. All other original rows and the output remain
unchanged. Improvement means fewer live operations, or equal operations with
fewer multiplications, after dead-row pruning.

Reduction at each sample is a ring homomorphism, so every universal integer
polynomial identity must match all three sampled signatures. A mismatch is
therefore a sound rejection; a match by itself is not an identity. For each
other operand, addition and subtraction determine a candidate shared signature.
Multiplication does so by componentwise inversion only for unit components;
the scanner fails closed for a zero component or a noninvertible nonzero
component. Literal zero cannot multiply to a target whose **entire signature**
is not the all-zero tuple, and `t−t` cannot match it either. This is not a
claim that every component of every target is nonzero. Both `t+t` and `t*t`
are explicitly searched. An available alias is not lost by the intersection
with new-gate signatures: `alias+0` is always among those signatures, and all
nodes with that signature are retained as separate alias choices.

The independent reviewer directly enumerated all concrete shared programs on
three toy graphs without using inverse lookup or signature intersections. Its
full sampled-program and improvement sets agreed with the scanner, including
the existing-alias and repeated-temporary positive controls. Separate controls
show that an all-zero target, a nonunit divisor and a partly zero earlier
signature stop the screen. Exact sparse integer-polynomial arithmetic also
independently verifies both reported G-linearization identities. Independent
whole-DAG liveness checks retain all 13 inputs and four ports in each form.

For the 87- and 86-operation source graphs respectively, the original screens
reproduced 1,208 and 1,626 sampled programs, each with exactly the two known
G-linearization forms. Both keep the original total operations and save one
multiplication. After that linearization, the screens reproduced 1,270 and
1,688 sampled programs and found no further improvement within this family.
The two retained forms are exact identities, not conclusions from sampling.

The search excludes zero-cost target aliases, replacements not using the same
shared value at both targets, more than one new shared gate, changes to other
rows or downstream compensation, constants outside 0–4, and alternative witness
encodings. It does not rule out fixed-port-only identities or merely equivalent
zero sets. It is not a global minimality proof, a Lean theorem, or a new smaller
consistency equation.
