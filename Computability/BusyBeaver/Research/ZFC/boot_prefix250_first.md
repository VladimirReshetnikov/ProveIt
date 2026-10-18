# First 1,024 blank-tape steps of prefix250

[BootPrefix250First.lean](../../Lean/BusyBeaver/ZFC/BootPrefix250First.lean) proves the complete configuration of the exact [prefix250 machine](candidate-prefix250/README.md) after 1,024 steps from Core's blank initial tape. The theorem `first1024` gives a `ZipRep`, so its tape statement covers every integer position. The resulting state is 92, the head is at −2, and the tape has 19 ones.

The module also provides `advance_checkpoint`: a checked `zipBlock` equality of depth `d`, together with an established checkpoint at time `t`, gives the next actual blank-run checkpoint at `t + 2^d`. This supports a chain of independently checked finite computations. Expected checkpoint data are generated inputs; the kernel-checked equality establishes their correctness.

This is an initial finite prefix. It does not establish the final 585,431-step startup, the complete runtime frame at that endpoint, an unbounded simulation, nonhalting, or a consistency equivalence. Reaching dispatch state 92 at time 1,024 alone does not establish a runtime-frame invariant.

## Checked evidence

The source and audit passed on their first run in 1.046 and 0.436 seconds, with zero warnings, seven ordered axiom probes and nine client examples. `first_block` uses `propext`; the other six declarations use only `propext` and `Quot.sound`. Finite computation uses trusted `decide +kernel`, with the default proof limits and no native evaluation axiom.

The [exact PASS record](results/boot-prefix250-first-verification.json) has SHA-256 `f95ddc6525c8ea4d3d0c307f91b84892b9300a7dcd057e9f70dafa319b093e33`. Source SHA-256 is `6f0f713925a8b872e4088dc60b4949be83dc1cfdd6f8eae6b75369eb480d67cc`; the fresh object is `de2ee26c0fea40f7cbf1340d3e170064ba357feeb63c1977f9ceee8aec3edae4`. The [preserved history and independent review](results/boot-prefix250-first-history.json) include exact source, audit, executed guard, input generator, logs and review records. The [maintained-default preparation](results/boot-prefix250-first-maintained-prepare.json) checks the published paths and providers without compiling.

The selected project imports are `Core`, `TablePrefix250`, `FastTablePrefix250` and `FiniteZipper`; `Init` and `Lean.Elab.Tactic.Omega` are explicit supplied toolchain boundaries. The guard reuses their exact checked objects and performs no dependency build, download or compiler-version query. Compilation is serial with `-j1 -M4096` and a shared 120-second source/audit budget. Input hashes, first providers and the fresh object are checked before and after the audit.

## Reproduction

From this directory, use a fresh external output directory:

```sh
python3 check_boot_prefix250_first.py --output /tmp/prefix250-first-prepared --prepare-only
python3 check_boot_prefix250_first.py --output /tmp/prefix250-first-checked
```

Preparation executes no proof command. The full check requires the exact compiler and cached parent objects recorded in the evidence, and rejects missing or changed providers. Source and audit are byte-identical to the successful run. The maintained guard changes only repository discovery and path defaults; the [publication record](results/boot-prefix250-first-publication.json) binds those files to the original evidence.

The maintained `generate_fast_prefix250.py --boot-output /absolute/path/BootPrefix250First.lean` can regenerate the untrusted first-checkpoint source explicitly. The generator's output is not a proof by itself. Attribution for the underlying machine and the prefix construction is retained in the candidate and table documentation.
