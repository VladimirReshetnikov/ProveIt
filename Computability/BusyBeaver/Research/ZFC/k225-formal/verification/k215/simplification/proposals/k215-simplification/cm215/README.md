# CM215: a small, compiled relative correctness proof

This packet proves that the existing CM215 alternative is equihalting with the
exact published K215 machine. It is pinned to ProveIt revision
`b6c7087477e51c017003bd729e712c8969733223`.

**Result:** all new modules compile in Lean 4.32.0, with no warnings or proof
holes. The reported axioms are only `propext` and `Quot.sound`. The clean build
record is `verification/result.json`; the complete logs are beside it. The
additional proof consists of 363 lines including comments, excluding the 462
lines of generated literal table data and the unchanged 808-line Core module.

This is a new formal relative proof of an existing 215-state machine. It does
not introduce a new machine or claim a 214-state construction. It uses the
previously established K215-to-ZFC calibration as an explicit input when that
calibration is desired.

## Rebuild

Use Lean 4.32.0. The default command needs only the Lean distribution and the
files in this packet; it regenerates the exact table data, checks the native
byte hashes, and compiles all standalone modules in a fresh temporary folder:

```sh
python3 verify.py --lean /path/to/lean --output /new/cm215-check
```

The final repository attachment additionally requires the pinned ProveIt
checkout with `BusyBeaver.ZFC.KDense215` already compiled. Its `.olean` must be
under `Computability/BusyBeaver/Lean/.lake/build/lib/lean`. Then run:

```sh
python3 verify.py --lean /path/to/lean --repo /path/to/ProveIt --output /new/cm215-repo-check
```

The output directory must not already exist. Neither command needs network
access or changes the packet's source files. The retained verification record
used the second command and checked the actual repository-table attachment.

## Main theorems

- `PositiveStuttering.equihalting`: generic positive-stuttering transfer, with
  no upper bound on the number of target steps needed per source step.
- `CM215.halts_iff`: the exact K215 and CM215 tables halt equivalently on every
  initial tape and at every initial head position, starting in state 0.
- `CM215.core_blank_halts_iff`: the same result on the repository's real
  `Machine 215` and finite-support tape representation.
- `CM215.repo_blank_halts_iff`: exact table attachment to
  `KDense215.machine215`, checking all 430 original transition rows in Lean.
- `CM215.inherit_calibration`: any halting characterization of that published
  K215 transfers to CM215, with the characterization supplied as a hypothesis.

When the existing full endpoint is in scope, the final application is:

```lean
CM215.inherit_calibration _
  SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation
```

The new relative theorem and the actual-table bridge are freshly compiled.
Rebuilding the entire inherited K215-to-ZFC closure is a separate claim and is
not required for verifying these new modules.

Read `proof_notes.md` for the precise invariant, why CM215 is a good target
for a short *additional* proof, and comparisons with the other alternatives.
Read `PROVENANCE.md` and `upstream/` for inherited source attribution and terms.
