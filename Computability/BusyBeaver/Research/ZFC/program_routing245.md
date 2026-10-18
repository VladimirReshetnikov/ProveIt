# Exact register decoder for the routed 245-state candidate

[ProgramRouting245.lean](../../Lean/BusyBeaver/ZFC/ProgramRouting245.lean)
defines the candidate's register program and proves that its decoder unfolds
to the exact instruction tree. Sharing identical subtrees gives 203 stored
internal nodes; the complete tree has 6,459 internal nodes, 6,460 instruction
leaves, maximum depth 51, and one halt leaf. The number 203 is a representation
size, not a Turing-machine state count.

The source generator and independent parser compare all ordered paths,
operations and operands with the delivered logical-site certificate. Logical
register numbers and break/continue depths are preserved. Compared with the
original program, 6,241 paths change while all ordered instructions remain
the same. Their changed control flow still requires its own bisimulation proof.

The Lean identity holds for every decoder fuel at least 51, including the
actual program's fuel 204 and root 202. `walk_eq_tree` covers every finite
pointer and starting index. `step_eq_tree` covers every pointer and every
register function `Nat → Nat`, using the actual consumed pointer and all
instruction effects. These are general semantic statements, not finite
register examples.

The [actual successful run](results/program-routing245-verification.json)
passed all 11 named axiom probes and 13 typed callers, with zero warnings.
Source checking took 6.034 seconds; the audit took 0.283 seconds. Six reports
have no axioms, three use `propext`, and two use `propext` and `Quot.sound`.
The source and audit use default proof limits and no native decision axiom.

The successful record is
`1efd9f64fc8067e85518fc9968752a9a10f78cdeb4f24aa8dd9e8c58d2a53c71`;
source identity is
`060a95566e6162b845b3ee734b4134aefeeb3e9c079de705c2d094ca9119ef0b`;
the fresh object identity is
`d0b2f23c453d895f2e4aa065ff0c1ab4bdfc67bb57e92509488ba90694582369`.
The [history](results/program-routing245-history.json) retains the preceding
two failed attempts, their exact sources and logs, the two focused proof
repairs, preparations and independent reviews. Attempt one failed in the
two general semantic clients; attempt two passed the source but failed two
concrete audit proofs. Attempt three freshly checked both source and audit.
The repairs changed proof scripts without changing theorem statements or
program data.

The guard selects exactly four checked project dependencies: `RegisterPath`,
`RMDag`, `RMEquiv` and `RMBisim`, plus the toolchain's `Init`. Source and audit
run serially with `-j1 -M4096`, sharing 120 seconds. The guard records the
fresh object before the audit and checks inputs and providers afterwards.
It performs no dependency build, download or compiler-version query.

The [publication record](results/program-routing245-publication.json)
connects maintained files to that execution. The exact executed emitter is
retained as provenance; the separate
[portable generator](generate_program_routing245.py) changes only
repository discovery and reproduces the source, audit and program-data bytes.
The maintained guard requires the pinned historical providers. Its
`--prepare-only` mode invokes no proof command.
The [maintained-path check](results/program-routing245-maintained-publication.json)
confirms all installed files and the successful preparation without replaying
the proof. The [independent publication review](results/program-routing245-portable-review.json)
also checks the preserved failed attempts and the lossless history.

From this directory, with fresh external output directories:

```sh
python3 -B generate_program_routing245.py --output /tmp/routing245-program-generated
python3 -B check_program_routing245.py --output /tmp/routing245-program-prepared --prepare-only
python3 -B check_program_routing245.py --output /tmp/routing245-program-checked
```

The next source obligation is the delivered 3,013-pair bisimulation with
`Prog254`, for arbitrary registers at the empty pointer. The binary runtime,
complete decoder coverage, 407,915-step blank startup and final 245-state
consistency equivalence remain separate Lean obligations. PA internalization
also remains open. Attribution and the ordinary executable verification are
preserved in the [candidate documentation](candidate-routing245/README.md).
