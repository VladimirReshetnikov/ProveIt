# Exact 250-state table in Lean

[TablePrefix250.lean](../../Lean/BusyBeaver/ZFC/TablePrefix250.lean) defines
the exact [prefix-carry machine](candidate-prefix250/README.md), with 250 working
states, 500 literal actions, start 0, dispatch 92 and a separate halt. The generator
checks all 500 rows against both frozen table forms and the exact renumbering.
The final halting transition retains its write and movement.

Lean has checked 40 named theorems and 40 direct callers. These include the table
size, action count and target bounds; the unique halt edge; the old/canonical
state inverse; and both incoming-edge equivalences required by the pulse
initializer. Twenty-two literal row theorems support the new operation proofs.
This is a finite table theorem, with no runtime, bootstrap or consistency
endpoint asserted by this unit.

The [successful record](results/table-prefix250-verification.json) binds the
exact source, audit, compiler and fresh object. Source compilation took 21.736
seconds; the audit took 0.321 seconds, with zero warnings. The first six axiom
reports are empty; the other 34 contain only Lean's standard `propext`.
There are no new axioms, `sorry`, native-evaluation axioms or project-specific
assumptions. The finite facts use trusted `decide +kernel` reduction under
default proof limits.

The check reuses only one previously checked, source/object-matched
`BusyBeaver.Core` module, plus the supplied Lean toolchain. It performs no
dependency build, download or version query. Both commands run serially with
one thread, a 4096 MiB Lean memory limit and a shared 120-second wall limit.

The [history](results/table-prefix250-history.json) preserves all failed
attempts and original source/audit/guard snapshots. Run 1 failed at launch
under an address-space limit before proof elaboration; run 2 hit tactic
recursion limits. Run 3 compiled both units but its guard incorrectly required
empty axiom sets. Run 4 changes only that audit expectation to the exact observed
distribution, retaining the same source, audit and object as run 3.
The initial axiom-free expectation was wrong and is not retained as a claim.

Reproduce source generation from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/generate_table_prefix250.py --check
```

The focused checker requires the selected existing Core object and the pinned
Lean 4.32.0 toolchain recorded in its parent evidence:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_table_prefix250.py \
  --output /tmp/zfc-prefix250-table-check-new
```

Use `--prepare-only` to check inputs and provider bindings without invoking
Lean. The maintained defaults passed this preparation after publication, and
the generator reproduces the source exactly. The
[publication record](results/table-prefix250-publication.json) distinguishes
the executed guard from its maintained copy, whose default paths were adapted.

Next are unbounded marking/carry/rollback contracts, the strengthened frame,
regenerated instruction proofs and the full 585,431-step blank prefix. The
external exact 250 consistency theorem and its internal PA formalization remain
unfinished. Attribution remains with the original machine/calculus/compiler
authors and the prefix/pulse research identified in the candidate README.
