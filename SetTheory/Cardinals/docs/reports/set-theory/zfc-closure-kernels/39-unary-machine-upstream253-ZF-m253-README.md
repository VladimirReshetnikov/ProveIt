# The 253-state ZF/ZFC machine

`machine/zfc_253.tm` is a complete binary Turing machine with **253 working
states**, blank symbol 0, start state 0, and one distinct uncounted terminal
state 253. Every initializer, register-file helper, and routing state is
included. The exact table has 506 transitions and SHA256:

```
84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95
```

This reduces Mira-Cult's 254-state machine preserved in
[`../m254/`](../m254/README.md). That original construction and its provenance
remain unchanged. The shared program, enumerator, proof calculus, and
set-theory transports are the accepted M254 sources. Their authorship,
licenses, and vendored dependency notices are retained in their existing
locations; this package adds no new vendored library.

The construction uses Andrew James Wade's framework
([license](../generator/LICENSE.wade)). The reused M254 proof, busycoq
([MIT](../stdzf_r3/vendor/busycoq/LICENSE),
[LibTactics license](../stdzf_r3/vendor/busycoq/LICENSE-LibTactics)), and the
Coq Library of Undecidability Proofs
([MPL-2.0](../stdzf_r3/vendor/undecidability/LICENSE)) retain their existing
notices. The vendored source pins remain busycoq
`bd2e36f6aa204eb011742d2ca6c8741102b2e59e` and Undecidability
`70dfc56f33a6e4835281044e68aa68279989047e`.

The end-to-end statements in [`coq/e2e/E2E253.v`](coq/e2e/E2E253.v) relate exact
blank-tape halting to finite classical refutations:

```coq
zf253_halts_iff_SIR : halts tm c0 <-> SIR ⊢TC ⊥
zf253_halts_iff_ZF  : halts tm c0 <-> ZFc ⊢TC ⊥
zf253_halts_iff_ZFC : halts tm c0 <-> (ZFc + AC) ⊢TC ⊥
```

The syntax and theories are those of the accepted M254 theorem: `TC` is the
Coq Library of Undecidability Proofs' classical natural deduction; `ZFc` is its
ZF with universally closed separation/replacement instances; `AC` is the
same choice-set axiom used by the existing ZFC transport. These are external
equivalences, not an internalized proof compiler or a consistency theorem.

## Reproduce and check

Use an existing **Coq 8.20.1** installation and Python 3. From the repository
root:

```sh
python3 -I -B ZF/m253/check.py --coqc coqc
```

The selected installation must include matching `coqchk` in the same resolved
`bin` directory. No downloads or installers are run. The checker:

1. Reconstructs the machine from the pinned unchanged 254-state baseline,
   exactly four changed rows, deletion of old state 8, and an explicit
   old/compact label bijection.
2. Verifies the complete generated `Table253.v`, both state maps, and its
   old-label proof view, then independently compares all 506 compact literal
   transitions with the machine file. It also regenerates the inspection
   inventory of all 6,460 instruction sites directly from the pinned,
   committed `../m254/coq/tm/Prog254.v`; no external `paths.json` is needed.
3. Rejects admissions, new axioms/parameters, and disabled kernel checks in
   authored sources. It reuses `../m254/check.py`'s dependency resolver and
   load paths, adding `M253` (`coq/tm`) and `M253E` (`coq/e2e`).
4. Serially rebuilds the complete mandatory `Audit253.v` dependency closure,
   including `E2E253.v`, from source
   using `coqc -q` and an environment without ambient `COQ*`/`ROCQ*` overrides.
   Every declared `Print Assumptions` probe in that closure must report
   `Closed under the global context`; the audit covers all authored proofs,
   and all three endpoint reports in `E2E253.v` are independently required.
5. Runs matching `coqchk` on every compiled logical module with recursive
   dependency checking. It uses neither `-admit` nor `-norec`.

Compiler calls have default 240-second wall/CPU and 2048-MiB memory limits;
recursive `coqchk` has a separate 900-second limit. The driver acquires
`/tmp/mm0-native-mac.lock` then `/tmp/mm0_compile.lock`, preserving existing
lock inodes, and refuses to overlap another native build. POSIX `flock` and
`ps` are required. Options `--wall-seconds`, `--coqchk-seconds`, and
`--memory-mib` change these explicit bounds.

The `zf253.yml` CI workflow uses the existing Coq 8.20.1 container convention,
pins the image by digest and the checkout action by commit, grants only
`contents: read`, and disables persisted checkout credentials. Its build
requires the complete 160-module, 194-report and recursive-check result.
The CI command allows 900 seconds per compiler call and 1536 MiB within a
60-minute job; the local defaults above are unchanged.

For read-only source and generator validation:

```sh
python3 -I -B ZF/m253/check.py --source-only
python3 -I -B ZF/m253/tools/generate_candidate.py --check
python3 -I -B ZF/m253/tools/gen_runtime253.py --check
python3 -I -B ZF/m253/tools/gen_sites253.py --check
```

`--source-only` never claims kernel acceptance. `--plan` prints the complete
logical dependency list without invoking Coq. The normal command prints
`CHECK PASS` only after rebuilding, auditing every probe, and completing
recursive `coqchk`. Unused axioms loaded elsewhere in an upstream library's
global context do not imply theorem dependencies; the separate probe audit
requires every checked result itself to be closed.

After the complete check passes and all sources are committed, prepare a
source-only ZIP with [`tools/package_source.py`](tools/package_source.py):

```sh
python3 -I -B ZF/m253/tools/package_source.py --plan
python3 -I -B ZF/m253/tools/package_source.py \
  --verified-commit FULL_VERIFIED_HEAD_HASH --output /tmp/zf253-source.zip
```

The builder requires every included file to match the specified committed
`HEAD`. It includes all canonical M253 sources, generators and machine, the
explicit `Audit253.v` dependency closure, the unchanged baseline machine and
resolver, and applicable dependency notices and licenses. It excludes build
products, optimization reports, PA sources, Git metadata, and compiler
installations. The ZIP has sorted entries, fixed timestamps and permissions,
and stored bytes without compression-version variability. `MANIFEST.json`
records the commit, dependency order, and each source's SHA256; the builder
prints the manifest and ZIP SHA256. It refuses to overwrite an archive.
Packaging performs source validation only: `--verified-commit` records the
caller's completed kernel verification and does not perform that verification.

## Exact reduction and proof bridge

[`tools/generate_candidate.py`](tools/generate_candidate.py) contains the
explicit state bijection and exactly these changes in the original labels:

| Old state/read | Write | Move | Target |
|---|---:|---|---:|
| 3/0 | 0 | L | 48 |
| 5/0 | 1 | R | 97 |
| 5/1 | 1 | R | 64 |
| 49/1 | 0 | R | 5 |

Old state 8 is deleted. Old state 5 becomes the shared initializer/helper;
it is compact start state 0. Old dispatcher 96 becomes compact state 33;
old terminal 254 becomes compact terminal 253. The old labels used by proof
lemmas are an execution view mapped to this literal compact table; they are
not additional physical machine states. Both generators use only committed
canonical source, with no dependency on optimization reports or old absolute
workspace paths. To regenerate deliberately, run `generate_candidate.py
--write`, then `gen_runtime253.py` without `--check`.

The blank bootstrap first reaches the initial register vector after 121,118
literal moves with header distance 37. A further finite prefix matches 330
steps of the unchanged `p254` register program. At total time **312,975** the
literal machine reaches dispatcher 33, head -17, PC `000`, and header
distance 40, with source-order registers `[5,0,0,0,2,0,0,0,0]`.

`Boot253.v` checks that complete endpoint, including all **158 spare blocks**
and their two nonzero values, against literal execution. Its RM330 witness
retains the actual register function and proves values pointwise. `Prefix.v`
preserves and reflects register halting across the finite normal prefix.
`Sim.v` starts from this later invariant; the universal gap-40 runtime
interface is retained. The complete box and instruction-site certificates
are instantiated for the changed table. `Main.v` composes these results with
the unchanged program/theory transport.

The checks establish the kernel trust surface: Coq 8.20.1, busycoq's TM
semantics, and the referenced library's syntax, deduction system, and axioms
as object-theory definitions. Finite Python simulations are provenance and
diagnostic evidence; they are not substituted for the Coq transports.
