# Logical calibration of the 246-state candidate's seed

[LogicalSeed246.lean](../../Lean/BusyBeaver/ZFC/LogicalSeed246.lean) proves
that the unchanged literal register program, started with empty PC and logical
registers `(3,0,0,0,3,0,0,0,0)`, halts exactly when ZFC has a refutation.
All logical registers beyond the nine primaries are zero. These logical
registers are distinct from the physical spare blocks used by the binary
machine.

The proof composes the existing all-register program bisimulation,
`DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0`, the native/ZF comparison,
and the constructible-model Choice comparison. The three formula fields
remain their safe zero codes; the nonzero numerical fields are permitted by
the dirty-root theorem. The empty PC is also proved clean.

Seven named theorem audits and seven typed clients pass with zero warnings.
The first source compilation passed, but four audit clients lacked an
`open SetTheory` declaration. After that audit-only correction, the complete
source/audit rerun passed in 0.305 and 0.281 seconds. Both attempts and the
independent review's correction are preserved in the
[history](results/prefix246-logical-seed-history.json). The final
[verification](results/prefix246-logical-seed-verification.json) binds the
fresh object before its audit and checks all 197 inputs afterwards.

The guard reuses 94 exact project providers from the existing checked
integration, plus `Init`. It rebuilds no dependencies and performs no
compiler-version query. Source and audit run serially with one thread,
4,096 MiB, a shared 120-second wall limit and default proof limits. Finite
seed values and the zero tail have no axioms; the consistency comparison
uses only standard Lean axioms, including classical choice.

From the repository root, with a fresh external output directory:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_logical_seed246.py \
  --output /tmp/logical-seed246-check --prepare-only
```

Removing `--prepare-only` checks the two proof units. The exact recorded
toolchain and cached prerequisite objects must be available. Published source
and audit match the successful run; the published guard changes only path
defaults. The maintained-default preparation is recorded separately.

This is a logical register-program theorem. It does not yet prove that the
246-state binary machine reaches the corresponding frame, simulates that
program, or satisfies the equivalence inside PA. Those are separate
obligations. The seed comes from source 63 of intake 162; the original
Mira-Cult/Jeff/Wade program and the existing ProveIt calibration retain their
attribution.
