# CM215: a short, checked transport proof from K215

**Result:** a new standalone Lean proof that the repository's exact K215 and
existing conditional-marker machine CM215 halt equivalently, from control 0
on every whole binary tape and at every head position. The proof also checks
215 working states for each table and exactly six changed transition rows.

CM215 is an existing 215-state alternative, not a new 214-state construction.
The contribution here is the short formal proof route: reuse the proved
parent endpoint through a local machine transformation.

The repository snapshot is
`b6c7087477e51c017003bd729e712c8969733223`.

## Exact theorem and status

The final facade `lean/CM215Certificate.lean` contains:

```lean
CM215Certificate.all_tape_halts_iff (h : Int) (t : Tape) :
  PositiveStuttering.Halts (step parentTable) ⟨0, h, t⟩ ↔
  PositiveStuttering.Halts (step markerTable) ⟨0, h, t⟩
```

It also contains the specialized `blank_halts_iff`, the two working-state
counts, and `exactly_six_changed_rows`.

| Evidence layer | Current status |
|---|---|
| Generic positive-stuttering transport theorem | Kernel-checked; axiom-free |
| Universal marker-invariant and whole-tape simulation | Kernel-checked |
| Exact K215/CM215 finite table certificate | Kernel-checked |
| Arbitrary-tape and blank-tape equihalting facade | Kernel-checked; axioms `propext`, `Quot.sound` |
| 215-state counts and six-row difference | Kernel-checked |
| Independent five-bit-window certificate | Python PASS; 6,840 admissible cases |
| Native-to-repository label correspondence | Python PASS; all 430 rows |
| New integrated ProveIt ZFC-refutation endpoint for CM215 | Tape/run representation adapter remains |

All **24 Lean modules** passed serial compilation using Lean 4.32.0,
commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
The exact logs, source hashes, return codes, and endpoint axiom reports are
in `lean/kernel_receipt.json` and `lean/logs/`. The retained maximum child
resident set was 612,680 KiB. These are measurements of this build, not a
comparison benchmark against the complete parent development.

No `sorryAx`, custom axiom, or `native_decide` appears in the checked
endpoint. Finite chunks use Lean's `decide +kernel`.

## The proof in one page

For an old configuration `(q,h,t)`, keep three local facts:

- at state 52, the cell to the left is one;
- at state 176, the current cell is one or the cell to the left is zero;
- at state 156, the cell to the right is one.

The last fact turns the original two-step predecessor argument into a
one-step inductive invariant. It holds initially at state 0 on every tape.

Map logical state 176 to physical state 52 and leave every other state, the
head, and the whole tape unchanged. Ordinary transitions transfer in one
step. Old zero branches at states 52 and176 transfer in three steps:

```text
old logical52:  52 --0L--> 176 --1R--> 129 --0R--> 154
old logical176: 52 --0L--> 176 --0R--> 185 --0R--> 168
```

Both blocks preserve the two inspected cells and end one position right.
The target blocks have positive length and no intermediate halt.
The generic deterministic positive-stuttering theorem transfers halting
in both directions even though the state map is noninjective.

The formal proof quantifies every tape `Int → Bool`. It does not assume
finite support or a blank exterior. It starts in control 0, not an arbitrary
internal control.

## Portable reproduction

The independent checkers and generator require Python 3's standard library.
The serial kernel-build driver uses Python's POSIX `resource` module; use
Linux, macOS, or WSL with Lean 4.32.0. Run from this `cm215/` directory.

### Independent local and numbering checks

```sh
python3 check_cm215_local.py --out cm215_local_receipt.json
python3 check_repository_labels.py --out repository_labels_receipt.json
```

The first script binds exact inputs by SHA-256, checks all six row changes,
the dense-state bijection, and all 6,880 control/window combinations.
Exactly 6,840 satisfy the invariant; all preserve it and admit the correct
one/three-step simulation. It reads no upstream executable code.

The second script parses the pinned repository table as literal text and
checks every renamed parent row. It does not execute or modify Lean source,
and it does not establish a tape-representation theorem.

### Regenerate the exact table certificate

```sh
python3 generate_certificate.py --inputs inputs --out lean --chunk-size 16
```

`generate_certificate.py` and `table_data.py` reconstruct the literal
table module, nineteen bounded check modules, and final facade from the
pinned native tables. Generation is untrusted; the Lean kernel validates
the emitted propositions. The three reusable proof modules are retained
under `lean/`.

### Compile the complete standalone bridge

```sh
python3 build_lean.py --lean /absolute/path/to/lean --source lean
```

The driver compiles one module at a time, with a default 768 MiB Lean memory
limit and 180-second timeout per module, rejects errors and `sorryAx`,
and writes fresh per-module logs plus `lean/kernel_receipt.json`.
The Lean executable is not included in this archive.

For direct inspection of the result, the final source is
`lean/CM215Certificate.lean`; the complete literal tables are in
`lean/CM215Tables.lean`.

## Exact tables and numbering

| Presentation | Working labels | Start | Dispatcher | Halt |
|---|---|---:|---:|---:|
| K215 native input | Sparse; includes 301 and 302 | 0 | 84 | 254 |
| CM215 native input | Same working-label set | 0 | 84 | 254 |
| CM215 dense input | 0–214 | 0 | 83 | 215 |
| Repository K215 `KTable215.lean` | K230 labels | 0 | 84 | 230 |

The only nonidentity native-to-repository translations are:

```text
301 -> 102
302 -> 120
254 -> 230
```

Both state positions and transition targets must be translated.
The read-only label audit verifies all 430 rows after this translation.
The repository list explicitly contains 226 entries (controls 0–225),
with eleven explicit disabled entries. Controls 226–229 are additional
implicit unused labels below terminal 230; the receipt lists all of them.
State 230 has no outgoing transition. Direction `true` means right in
both encodings.

Native parent SHA-256:

```text
9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2
```

Native CM215 SHA-256:

```text
e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252
```

Dense CM215 SHA-256:

```text
1f4f084f7293e2b042d5746039f793ff72ed429083b504970c939a5515e666cf
```

## Remaining repository integration

The new proof uses an integer-indexed functional tape and the standalone
`PositiveStuttering.Steps/Halts` relation. The repository's sparse lane
uses `KZip.Conf`, whose two finite lists are trimmed after every step,
and `KZip.run/Halts`. Its final `KEndpoint215` uses the dense
`BlankHalts machine215` proposition.

The remaining adapter should:

1. apply the documented native-to-K230 label translation;
2. relate finite-support functional tapes to the trimmed list zipper,
   preserving the scanned symbol, writes, and left/right moves;
3. identify the successful-step and halting relations;
4. compose with the existing dense bridge and checked parent endpoint.

Only the finite-support part is needed for the blank start; the new CM
transport theorem itself already covers all tapes. The adapter is not
implemented here, and the parent's complete semantic dependency closure
was not rebuilt in this packet. Consequently this package claims the
checked exact-table **equihalting** theorem, rather than a newly integrated
`KEndpointCM215.blank_halts_iff_zfc_refutation`.

The established mathematical calibration of K215 plus this local transport
does give the ordinary mathematical Con(ZFC) equivalence for CM215. The
explicit integration boundary concerns the final proof-assistant theorem
in the repository's types.

## File map and attribution

- `inputs/`: exact native/dense machine bytes, dense mapping, and upstream notices.
- `reference/KTable215.lean`: pinned literal repository table for the numbering audit.
- `check_cm215_local.py`: independent universal-local finite check.
- `check_repository_labels.py`: read-only row-translation audit.
- `generate_certificate.py`, `table_data.py`: deterministic certificate generation.
- `build_lean.py`: serial complete kernel check.
- `lean/`: all 24 source modules, generation receipt, kernel receipt, and build logs.
- `cm215_local_receipt.json`, `repository_labels_receipt.json`: Python audit results.

The existing CM215 table and original conditional-marker theorem retain
their ProveIt attribution. This packet adds the history-free invariant
presentation, independent finite checker, generic positive-stuttering
lemma, formal whole-tape transport proof, and literal table instantiation.
Upstream license and notice files are retained under `inputs/`.
