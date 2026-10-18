# Closed 244-state ZF/ZFC consistency equivalence in Lean

[BinaryCompensated244.lean](../../Lean/BusyBeaver/ZFC/BinaryCompensated244.lean)
proves, for the exact [compensated 244-state machine](candidate-compensated244/README.md),
that blank-tape halting is equivalent to a ZF refutation and to a ZFC
refutation. Consequently nonhalting is equivalent to the corresponding
consistency statements. These are **closed external Lean theorems**.
The proof inside PA remains open; no unconditional nonhalting or absolute
consistency theorem is asserted.

The machine has **244 working states**, including initialization, and one
separate halt target. It starts in state 0, at head 0, on the empty binary tape.
The single tape is infinite in both directions and every action moves left
or right. The exact canonical table has 488 actions and SHA
`2ea5521fa7d0fc24b4f3dc07d497b10de2532147225820033d9c96f247444187`.
The final wrapper uses that literal machine, not a faster evaluator or a
machine requiring a supplied initial configuration.

The public declarations in namespace
`SetTheory.BusyBeaver.ZFC.BinaryCompensated244` are:

| Declaration | Checked statement |
| --- | --- |
| `blank_initial_config` | State0, head 0 and empty tape for 244 working states. |
| `blank_halts_iff_routing245` | Exact 244 blank halting iff exact 245 blank halting. |
| `blank_halts_iff_zf_refutation` | Blank halting iff `BProv ZFax_s [] Form.fBot`. |
| `blank_halts_iff_zfc_refutation` | Blank halting iff `BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot`. |
| `nonhalting_iff_zf_consistency` | Negated blank halting iff absence of the displayed ZF refutation. |
| `nonhalting_iff_zfc_consistency` | Negated blank halting iff absence of the displayed ZFC refutation. |

`BlankHalts M` is the existing definition `∃ t, (M.run t).state = none`.
The reference to consistency uses the actual imported first-order proof
calculus and its ZF/ZFC axiom predicates; it is not an uninterpreted placeholder.

The proof first establishes the [exact local/global simulation](compensated244_simulation.md)
against Routing245, then composes it with the already checked
[Routing245 endpoint](routing245_binary.md). The244 reduction deletes old 122,
changes four retained actions, and uses a local tape invariant to justify
seven positive comparison blocks. Their endpoints preserve the entire tape.
The unchanged source program, logical seed and set-theory calibration are
inherited through the 245 endpoint. This avoids rebuilding their proofs.
The simulation quantifies over arbitrary finite-support tapes at the shared
start; its blank-tape specialization discharges the final machine's initial
condition without any runtime-frame premise.

The actual final source/audit check passes **six named axiom probes and six
typed callers**, with **zero warnings**, in 0.525/0.517 seconds. One axiom report
is empty, the halting-transport report uses `propext` and `Quot.sound`, and
the four calibrated statements additionally use `Classical.choice`.
There is no `sorry`, `native_decide` or added theory axiom. The
[actual execution record](results/compensated244-binary-verification.json)
is `313c078f066db3452a5e6cb37ef5b8dbb6b515f302a0350b9fd3c0f3ad4abf34`.
The checked source is
`65049c0a126f49207f36dfecd85c5997bad51e13402602c02f23e73d78e32f47`,
and its freshly compiled object is
`f2681e2e5854d47dc3c61ff1682d21f1421c86b619094a5d332c3b253fdfaec4`.

The guard selects exactly 857 existing project source/object pairs from two
successful actual parents, plus the pinned Init/Omega toolchain objects.
It checks 1,734 inputs before and after execution, records the new source
object before auditing, and verifies first-provider identities. Source and
audit run serially with `-j1 -M4096` and default proof limits under one
120-second budget. There is no dependency build, download or version query.
This is a fresh final composition check over previously checked dependencies,
not a fresh recompilation of all 857 providers.

Independent source, guard, preparation and actual-evidence reviews are retained
in [compensated244-formal](compensated244-formal/). An initial unexecuted audit
draft omitted `open SetTheory`; that namespace issue was corrected before
the first compiler invocation and its original draft is preserved. The actual
source and audit are published byte-identically. The maintained guard changes
only their path defaults.

## Reproduction

From the repository root, with the exact recorded compiler and cached providers:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_binary_compensated244.py \
  --repo "$PWD" --prepare-only --output /tmp/c244-final-prepared
python3 -B Computability/BusyBeaver/Research/ZFC/check_binary_compensated244.py \
  --repo "$PWD" --output /tmp/c244-final-checked
```

Use fresh external output directories. Preparation runs no proof command.
Historical cache paths are part of the recorded provider boundary; this
checker does not bootstrap dependencies on a new machine.

The [ordinary source and executable reproduction](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-166.md)
remain separate evidence. Their full runtime replay passes 8,391 universally
guarded cases and their blank startup checks 407,951 transitions. Those Python
results are not used as axioms in the Lean composition.

Credits remain Mira-Cult for the original calculus and proof search,
Jeff Ketchersid for verification, Andrew James Wade for the compiler framework,
and the ProveIt reductions and incoming 18 October 2026 contribution for the
compensated fold. See the candidate page for the exact arrival, pinned commits
and preserved notices. Internal PA calibration and the assumptions needed for
each independence direction remain explicit separate obligations; consistency
alone must not be substituted for arithmetic soundness.
