# Current Rocq source audit and next integration boundary

Pin: `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.
All measurements below concern committed source bytes, not a fresh full
correctness build. Root paths are relative to
`Computability/BusyBeaver/Research/ZFC/k225-formal/`.

## Changes already present in source

The current `rocq/rocq-extension/coq/215/` differs from the historical
237-module full-build descriptions. Its directory has 43 top-level `.v`
files, 400,271 bytes and 8,026 lines; this is a directory census, not its
transitive endpoint closure.

| Source in `rocq/rocq-extension/coq/215/` | Bytes | Lines | Current role |
| --- | ---: | ---: | --- |
| `Source215.v` | 832 | 14 | One normalized forward certificate; mirror theorem supplies the converse |
| `NormalizedBisim.v` | 8,739 | 210 | Checker with pointers compared modulo trailing zeroes |
| `NormalizedCert215.v` | 109,125 | 1,447 | The 1,426-entry normalized certificate |
| `DomRho8.v` | 1,009 | 23 | Adapter into the shared implication core |
| `DominatedCore.v` | 13,083 | 269 | Shared implication proof; generated header included |
| `L1_CompPerm.v` | 14,584 | 331 | Contains `compile_direct` from `thm222` |
| `SeedPerm.v` | 2,673 | 59 | Uses `compile_direct` in `seedPerm_complete` |
| `ProgLibPerm.v` | 37,951 | 780 | Candidate-specific macro contracts remain |
| `Sim230.v` | 12,037 | 220 | Candidate-specific runtime invariant remains |

The `DominatedCore` template in `rocq224/src/` has different header bytes;
its size must not be mixed with the generated-file measurement above.
`ThmDom.v` is absent from the current generated 215 directory. Therefore
normalized source correspondence, the shared dominated-implication core,
and direct compiler fusion must not be proposed as new unimplemented
changes. Historical endpoint receipts remain tied to their own source
bytes; the current directory alone does not establish an additional fresh
end-to-end check.

## Existing proposals to reuse

The proposal collection already contains normalized and balanced source
certificates; affine drain contraction; shared numerical/unrestricted
implication; shared macro supports; a common AX word; scheduler rank;
semantic decoder contracts; decoder-prefix factoring; and local table
transport in Lean. This contribution adds the exact Rocq locality adapter
and a small generic replay theorem, rather than claiming discovery of
those ideas.

## Concrete remaining duplication

`census_runtime.py` removes only leading comments/whitespace and renames
`K<number>F` namespaces. It leaves constants, program names, logic and proof
bodies intact. For candidates 215, 217, 218, 221, 225, 226, 227, and 229,
each of the following has one identical normalized body:

- `Runtime230Core.v`
- `Tape230Blocks.v`
- `Tape230Carry.v`
- `Interpreter230Sites.v`

The 32 physical files total 333,868 bytes. The four 215 files total
42,108 bytes/938 lines. These are the selected fork corpus totals; no
subtraction is claimed as an achieved saving. Each namespace binds to
its own `TM230`, `Zip`, and boot definitions, and shared source ownership
must preserve these semantic parameters. The existing generator already
owns the fork logic; simply deleting generated files would not be a proof.

## Recommended interface split

Use stable tape/segment syntax, a table parameter, and explicit register
oracle contracts. Put the universally quantified symbolic execution theorem
in one module. Candidate-specific files supply the literal table, row
facts, oracle lemmas, boot facts, and exact source coverage. The supplied
`Runtime215Locality` component handles exact finite symbolic replay; it
is a first step toward this split, not a substitute for it.

For table modifications, use baseline footprint inclusion and row equality
to reuse unaffected site computations. Recompute or prove semantic contracts
for the affected sites. Retain all 6,176 guarded outcomes; a small number of
runtime templates is not a proof that every concrete guard is covered.
Positive progress must remain explicit because zero-step stuttering can
invalidate the backwards halting argument.

## Acceptance order

1. Preserve the current literal table and exact endpoint theorem names.
2. Compile the new locality files and their definitional bindings (done here
   under Coq 8.18; repeat on production Rocq 9.1 before adoption).
3. Introduce the smallest shared runtime interface; preserve existing public
   names by aliases so callers do not all change at once.
4. Instantiate support certificates and target physical oracle contracts.
5. Rebuild affected descendants, both exact sparse/dense endpoints, their
   assumption reports and recursive production kernel audit.
6. Measure source bytes, selected dependency closure and checking time
   separately. The new helper must be counted when reporting net savings.
