# Independent audit of the K226 source and dense-machine endpoints

## Conclusion and scope

An independent read-only review found **no logical defect or additional
hypothesis** in the K226 source bisimulation and dense-machine endpoints.
The review examined the definitions, statements, and proof relations in
`rocq226/OffsetBisim230.v`, `Source226.v`, `Dense226.v`, `Correct226.v`, and
`CorrectDense226.v`, together with their relevant source, runtime, bootstrap,
and upstream dependencies. It did not infer correctness merely from a
successful compilation log.

The separate standard-library-only script
`independent_source_dense_audit.py` independently parses the Rocq literal
data, compares them with the selected artifacts, and emits
`independent_source_dense_receipt.json`. It imports no generator or
construction checker. The receipt pins every reviewed principal Rocq module
by SHA-256. The script does not replace the Rocq kernel check or claim to be
a parser for arbitrary Rocq programs; it deliberately accepts only the
literal declaration forms used in this selected development.

## 1. Register offset: correct sign and tested-register guard

`OffsetBisim230.v` defines the relation

\[
R_1(i)=R_2(i)+\delta(z,i),\qquad
\delta(z,i)=\begin{cases}z,&i=5,\\0,&i\ne5.\end{cases}
\]

The actual register files remain natural-valued. The signed integer is a
relation between those files, rather than an extension of the machine's
register domain.

For two straight-line segments, `counts_ok` checks

\[
\delta(z,i)+\#_i(l_1)=\#_i(l_2)+\delta(z',i).
\]

This is exactly the equation required after adding the respective
increment counts to related input registers. `counts_ok_sound` checks all
mentioned registers and includes register 5 explicitly in
`5 :: l1 ++ l2`. That explicit inclusion also validates offset changes when
neither segment increments register 5. For every other unmentioned
register, both counts and both offsets are zero.

At a decrement checkpoint, `oentry_ok` requires equal register numbers and
`delta z r = 0`. Thus `related_at` obtains equality of the actual tested
register values. On the positive branch both registers are updated to the
same predecessor value; `related_update` proves that the relation survives.
On the zero branch the files are unchanged. No equality of test outcomes
is assumed when the tested register has a nonzero offset.

`omirror` exchanges the two program counters and negates the offset.
`Source226.v` computes and proves the backward certificate check
independently. The reverse implication is therefore not inferred from an
unchecked symmetry property of the certificate generator.

## 2. Soundness, progress, and initial relation

The source theorem is

```coq
forall R,
  rm_halts p226 ([], R) <-> rm_halts p230 ([], R).
```

It has no safe-seed, reachable-state, H-loop, or zero-register premise. The
initial checked branch starts at both empty program counters with offset
zero, so every natural-valued register file satisfies the initial relation.

The generic proof uses well-founded induction on the number of steps of a
halting run. At a decrement checkpoint it consumes one step before the
recursive call. Successful `seg` computations have proved finite runs
through increments and control transfers; they cannot hide an infinite
run between checkpoints. The inherited `seg_hn` and `seg_run` lemmas
establish the exact increment effects of these segments.

The two halt leaves terminate the simulation directly. Nonhalting is
obtained from the proved halting equivalence. There is no zero-progress
cycle being treated as a finite matched execution.

The selected certificate contains 2,376 checkpoint pairs and 4,750 checked
branches. Eight entries carry offset `+1` in register 5, and all eight test
register 6. The other 2,368 entries have equal register files. The longest
straight-line segment has five instructions. These finite facts are
certificate diagnostics; the theorem follows from the proved generic
checker and its closed forward/backward checks.

## 3. Independent exact source and table bindings

The independent script verifies the selected artifact hashes before
comparison:

| Artifact | SHA-256 |
|---|---|
| Dense K226 table | `b58279b8b2e2cf029dd94e084d47cd6097772d7bce2a62653767895123d29599` |
| Table with original K230 labels | `6f5a35c58961c77baf595ab743a185f4df6815aaaceb89a5b1494521b96f1d6c` |
| Selected K226 source | `47f5cfac0ec765c6f84f9d29973d4c9b3d79f12482a2cd1268d582e85c814bd3` |

It then checks:

- All **452 transition rows** parsed from `Table226.v` equal the dense
  machine artifact, including read symbol, write symbol, direction, and
  target state.
- All **452 surviving transition rows** parsed from sparse `Table230.v`
  equal the artifact with original K230 labels. The four disabled states
  are exactly 65, 79, 140, and 175.
- The actual `p226` record uses the parsed `p226_tab`, root 187, and 188
  decision nodes. Every node reference points backwards. Expanding the
  table produces exactly the selected **5,121 paths, opcodes, and
  arguments**, in their complete order.
- Dense-to-sparse renumbering derived independently from the deleted-state
  set makes every transition commute, including the two halt cases.

These checks concern literal bindings. A digest written in a Rocq comment
alone would not establish them; the script parses and compares the data.

## 4. Dense state type, transition identity, and blank configuration

`Ctx226.Q = bnat 226` contains the values 0 through 226 inclusive. The
literal table has 226 working rows, numbered 0 through 225; value 226 is
the separate halt state. `dense_targets_ok` bounds every target, and
`dense_terminal` proves that the halt state has no transition.

The `expand` definition skips exactly the four removed sparse labels:

| Dense value | Sparse value |
|---:|---:|
| 0 | 0 |
| 65 | 66 |
| 78 | 80 |
| 138 | 141 |
| 172 | 176 |
| 226, halt | 230, halt |

`transition_commutes` checks all 227 bounded states and both symbols. The
proof covers the terminal state as well as every working state. In
particular, a surviving dense transition cannot map to a disabled sparse
state. Its conclusion preserves the written symbol and direction and
maps the target state through `decode_state`.

`decode_initial` is a definitional equality of the actual BusyCoq blank
configurations. `c0` consists of state 0, current symbol `false`, and two
infinite `false` streams. `decode_conf` changes only the control state and
leaves the complete tape and head convention unchanged.

The forward halting implication maps each literal step and the terminal
configuration. The reverse implication maintains a sparse configuration
as the image of a reachable dense configuration. A dense transition gives
a positive sparse transition, and `progress_halts` extracts a dense halt
from a finite sparse halting run. This proof does not rely on an assumed
inverse state map or an excluded-middle principle.

## 5. Exact end-to-end theorem and discharged hypotheses

`Correct226.v` composes the following established statements:

1. The sparse literal machine halts from its actual blank configuration
   exactly when `p226` halts from `([], R0)`.
2. `p226_p230` relates that register file to the original K230 source.
3. The pinned original program theorem relates `p230` at `R0` to the
   enumerator seed actually produced by the blank bootstrap.
4. The pinned seed and calculus theorems equate this halting with a
   derivation of contradiction from `StandardZFC`.

The runtime fork proves its 409,835-step blank bootstrap anew. Its
register-file constants and dispatcher configuration are used by
`inv_boot`; the endpoint does not substitute an assumed all-zero logical
seed. The abstract box hypotheses in the generic interpreter lemmas are
instantiated by the concrete proved register-block lemmas before
`Sim230Main.tm230_rm` is used.

`CorrectDense226.v` combines this result with the dense/sparse equivalence:

```coq
Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
```

The nonhalting/consistency corollary is the negation equivalence of that
statement. There is no assumed consistency or inconsistency premise and
no additional source-invariant parameter in either final theorem.

The final recorded `Print Assumptions` results are “Closed under the
global context,” in agreement with the direct inspection. The written
audit is not a replacement for the companion build and kernel-check
receipts. As with the rest of the development, ordinary proof-assistant
kernel and foundational interpretation trust remains external to this
literal-binding script.

## 6. Nonblocking documentation defects in the reviewed files

Two comments in the reviewed `Dense226.v` are stale:

1. The header says “0..228 work, 226 halts.” The correct working range is
   **0..225**, with separate halt value 226.
2. The transition-identity comment says “all 230 states.” The actual proof
   checks **227 bounded states: 226 working states plus halt**.

The definitions and proof enumeration are correct. These comments do not
weaken any theorem. The reviewed module's digest is retained in the
binding receipt; any later wording correction should be described as a
documentation change. This audit did not modify the reviewed modules.

## Reproduce the binding comparison

Supply the Rocq module directory and the three selected artifact paths:

```sh
python3 independent_source_dense_audit.py \
  --rocq PATH/TO/rocq226 \
  --dense-table PATH/TO/k226.tm \
  --sparse-table PATH/TO/table_k230labels.tm \
  --sites PATH/TO/sites.json \
  --out independent_source_dense_receipt.json
```

The script raises an error on any mismatch and writes the receipt only
after every comparison succeeds. Its checks do not depend on Python
assertions and remain active under optimized Python execution.

## Delivery note

The two stale comments identified during the scratch-source review are corrected
in the portable proof sources. The adjacent receipt was freshly regenerated
against those delivered sources and the exact public machine. The separate
Rocq source-correspondence receipt preserves the original checked comments and
verifies identical noncomment proof text.
