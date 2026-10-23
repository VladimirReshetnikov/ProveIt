# Numeric computation tables for the actual formula renaming operation

`Lean/DiophantineConsistency/AnnotatedRename.lean` checks finite numeric tables
for the repository's exact `SetTheory.rename`. Mode zero represents
`rename Nat.succ`, and mode one with parameter `k` represents
`rename (inst k)`. A nonzero mode has the same instantiation semantics. The
local checker does not recursively parse a formula code.

Every row has six natural fields: constructor tag, binder depth, two arguments,
input code and output code. Membership/equality rows use their arguments as
variable indices. Binary rows use them as backward child-row indices; unary
rows use the first as a backward index and require the unused second field to
be zero. Bottom rows require both unused arguments to be zero. Constructor
codes use the exact frozen `AnnotatedProofCode` formula representation.

The public local conditions are named `atomicEquations`, `bottomEquations`,
`binaryEquations` and `unaryEquations`. They assert literal numeric constructor
equations and the required child depths. Binary children must have the same
depth as their parent; a quantified child must have depth one greater.
`binaryAt` and `unaryAt` additionally validate the backward references. These
finite arithmetic conditions are the intended future interface for an internal
model-omega proof; they make no assumption that a nonstandard code can be
decoded to an external Lean formula.

The lifted variable map fixes indices below the recorded binder depth. At or
above that depth, shifting adds one. Instantiation maps the index equal to the
depth to `k+depth`, and decrements larger indices. Its `index_up` theorem proves
that entering a binder implements the actual de Bruijn `up` operation.

Soundness reconstructs an actual formula at each accepted row and identifies
its input and output codes with that formula and its existing Lean renaming.
Completeness constructs finite accepted fragments by induction on the
original formula syntax, with explicit backward offsets. This is an
existence proof in `Prop`, without choice or Prop-to-Type elimination; it does
not select a compiler from a computability assertion.

`AnnotatedRenameCode.lean` adds explicit six-coordinate nested-pair numeric
codes for rows. Tables use the
workspace successor-pair list format. A total fuel-bounded numeric parser
checks the table spine, and its roundtrip proof supplies sufficient fuel from
the table length or from its numeric code. It does not decode the recursively
nested input/output formula codes. `checkCode` then applies the finite local
validator. The exact endpoints are:

```lean
exists_shift_code_iff (f : Form) (output : Nat) :
  (∃ code, checkCode 0 0 0 (formCode f) output code = true) ↔
    output = formCode (rename Nat.succ f)

exists_inst_code_iff (k : Nat) (f : Form) (output : Nat) :
  (∃ code, checkCode 1 k 0 (formCode f) output code = true) ↔
    output = formCode (rename (inst k) f)
```

The generalized theorem `exists_code_iff` also records an arbitrary starting
binder depth. The checks include invalid child depth, missing/forward
references, unused arguments, unknown tags, binder boundaries, table order and
numeric truncation.

`AnnotatedRenameArithmetic.lean` is a separate local arithmetic stage. It
supplies literal scalar primitive-recursive program data for the lifted
variable map, exact numeric unary/binary/variable constructors, and the full
`atomicEquations` predicate. The atomic program takes `(mode,(k,rowCode))` and
returns one exactly when those equations hold; tag-domain validation remains
a separate condition of `Row.valid`. The literal program-tree sizes are
proved in Lean:

| Local program | Nodes | Certified optimized nodes |
| --- | ---: | ---: |
| Lifted variable-index map | 177 | 161 |
| Unary constructor | 19 | — |
| Binary constructor | 33 | — |
| Variable constructor | 49 | — |
| Atomic-row equations | 1,215 | 1,151 |

These are instruction-node counts, not polynomial variable counts. Runtime
controls execute the supplied index and atomic-validation programs as well as
the complete numeric table parser on valid and malformed small certificates.
These programs do not establish that the whole table validator or the original
sealed-ZFC checker has been compiled. Bounds, sealing, actual schema expansion,
contextwise transformations, whole proof-line validation and the internal
coded-form/omega interpretation remain open obligations.
