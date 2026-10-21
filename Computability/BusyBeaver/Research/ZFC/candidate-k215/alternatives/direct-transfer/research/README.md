# Independent research checkers

These four scripts use only the Python 3 standard library. They do not import
the source packet's runtime checker or any repository module. Place the scripts
under the final packet's `research/` directory.

Run from any working directory:

```sh
python research/check_st215_bootstrap.py
python research/check_scratch_control.py
python research/check_rotating_adjacency.py
python research/check_biased_sync.py
```

The first script reads `machine/st215.native.tm` and
`source/st215.sites.json`, resolved relative to the script's parent packet.
It independently executes the 70,506-step literal blank prefix, reconstructs
the complete sparse-tape frame, resolves the complete source CFG in two
independent ways, counts the 201 distinct source DAG nodes, and records the
177-step synthetic-AX source bridge. Optional explicit arguments are:

```sh
python research/check_st215_bootstrap.py MACHINE SOURCE [CONTEXT_ROOT_SOURCE]
```

The optional unrotated source enables an additional whole-CFG equality check.
It is not required by the default finite bootstrap check. The all-natural
command contracts, primitive simulation, compiler, credit proof and calculus
calibration remain separate mathematical obligations.

The second script reads `source/st215.sites.json` as a correct return-to-root
baseline and `inputs/scratch-biased.sites.json` as the archived faulty source.
It resolves both complete CFGs independently, identifies the incorrect
continuation, and checks 64 instances of the exact halting suffix whose
all-natural duration is proved in the accompanying TeX. Override paths with:

```sh
python research/check_scratch_control.py CORRECT_SOURCE SCRATCH_BIASED_SOURCE
```

The rotating-pop checker is self-contained. Its formulas are explicit symbolic
terms, not imported or evaluated repository code. It proves all ten required
tag/injectivity mismatches for arbitrary natural parameters. The accompanying
written invariant supplies the transition-level and dirty-tail conclusions.

The biased-parser checker is also self-contained. It corroborates an abstract
synchronization theorem for 1,000 positive residuals and 18 word encodings.
It does not describe the archived faulty machine and does not claim a physical
implementation or state count. ST215 uses ordinary candidate increments and
does not depend on this abstract theorem.

Each script writes its JSON receipt beside itself. Existing receipts include
the script hash; rerunning after any script edit updates that hash. Receipts
record the input byte hashes where external input files are used.
