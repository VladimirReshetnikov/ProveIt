# A supplied whole-table primitive-recursive renaming validator

The direct sealed-ZFC route now has an actual supplied scalar PR program for
the entire numeric renaming-table checker, rather than only local operations.
It is the program data `AnnotatedRenameScanPR.P.program`. Its checked pointwise
specification is the frozen `AnnotatedRename.checkCode` for arbitrary natural
input codes, not merely for prevalidated tables.

The new source modules separate four obligations:

- `AnnotatedRenameLocal.lean` defines the numeric atomic, bottom, binary and
  unary conditions and proves exact agreement with `Row.valid`, including
  missing child references, depths, unused fields and unknown tags.
- `AnnotatedRenameLocalPR.lean` supplies literal `ScalarPRCode.Realizes` data
  for all those conditions. Four-field blocks are compared by one equality of
  nested pairs, with an ordinary pairing-injectivity proof identifying the
  component equations. The tag dispatch shares the binary and unary bodies.
- `AnnotatedRenameScan.lean` gives a numeric state machine and proves its
  agreement with the frozen table checker for every natural table code.
- `AnnotatedRenameScanPR.lean` supplies the actual primitive recursion,
  terminal checker, parameter packing, pointwise checker theorem and program
  size proofs. No program is selected from a computability proposition.

A scan state contains the remaining successor-pair list code and the accepted
history code. A valid row is consumed and pushed into history. An invalid row
resets to the absorbing rejecting state zero. A completed state retains its
history. Terminal acceptance checks that the remaining code is zero, history
is nonempty, and the latest row has the exact requested depth/input/output.
Short prefixes therefore cannot be accepted as completed tables.

The external proof uses only the table-spine parser. Every natural code has a
canonical finite list of six-natural rows; no recursive input/output formula
parser is involved. The table induction and the already checked local
conditions establish the exact scan simulation. The canonical scan fuel is
the numeric table code, which bounds the number of rows.

The supplied unary program's input packs six coordinates: mode, instantiation
parameter, root depth, input formula code, output formula code and table code.
`program_input` proves equality to the frozen checker; `exists_program_iff`
proves that acceptance for some numeric table is equivalent to the actual
original formula renaming. The constructor theorem establishes the supplied
program's primitive recursiveness, and `value_primrec` transports its checked
specification. No new axiom, choice-based program extraction or formula
membership oracle is used.

The exact instruction-node counts are proved for the actual program data:

| Supplied program | Nodes | Certified optimized nodes |
| --- | ---: | ---: |
| Complete local-row validator | 3,119 | 2,931 |
| Numeric scan transition | 3,223 | — |
| Parameterized scanner | 3,271 | — |
| Terminal checker | 297 | — |
| Entire numeric validator | 3,605 | 3,329 |

These are counts of scalar PR syntax constructors. They are not witness
counts, polynomial scalar-operation counts, or size claims for a closed
consistency equation. The scanner occurs once in the fixed argument block
supplied to the terminal checker.

The PR syntax uses deliberately elementary unary recursions for zero tests
and arithmetic. Its canonical fuel can also vastly exceed the actual table
length. Efficient execution on large encoded certificates is not claimed, and
full PR execution on nonempty large table codes is deliberately excluded from
regressions. The checks execute bounded source scans on valid, short, bad
reference and bad-depth examples, reduce the all-zero supplied-program input,
and verify semantic endpoints, metadata and standard-axiom audits.

This completes an external arithmetic representation of one syntax operation.
It does not compile sealed-ZFC refutation certificates as a whole.
[Bound and sealing certificates](ANNOTATED_BOUND_SEAL.md) are now checked;
[actual schema expansion](ANNOTATED_SCHEMAS.md) is checked too. Contextwise
operations and the proof-line validator remain open. Nor does the external natural-number simulation prove
correctness on nonstandard internal-omega elements. That requires a separate
internal verification of the named finite local equations, coded-form
invariants and arithmetic programs. No decoding of a nonstandard model code
to an external Lean formula is assumed.
