# A checked normalized Rocq source proof for K215

This packet ports the already checked **1,426-entry normalized Lean source
certificate** to the actual inherited Rocq register-program semantics. The
normalization and certificate are inherited from the repository's incoming
`K215_Proof_Simplification_2026-10-21.zip`; this packet's contribution is the
new Rocq checker proof, its concrete source-equivalence instance, and their
fresh compiler/kernel checks. It does not claim to discover that normalization
or to construct a new Turing machine.

The two literal program definitions are byte-identical to ProveIt commit
`53269bcab1efc0f82d3022645bd7cf0c22d84959`. Their complete identities are recorded
in `exact_source_bindings.json`.

## The theorem

```coq
Theorem p215_dagPerm_normalized R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
```

Here `R` is any natural-valued register file. Both `p215` and `dagPerm` are
the existing literal Rocq programs, and `rm_halts` is the inherited semantics.
There is no consistency premise, assumed simulation, bounded-run premise,
changed machine table, or new axiom.

This supplies the same all-register source bridge as the production
`Source215.p215_dagPerm`. It does not rebuild the full 237-module binary/ZFC
endpoint. The proposal in `integration/Source215.v` retains that public theorem
name, but production adoption still requires updating the maintained source
generator and rebuilding its affected downstream modules and endpoint clients.

## Why fewer entries suffice

A path is a finite Boolean list interpreted with an implicit infinite false
suffix. Thus `[]`, `[false]`, and `[false,false]` observe the same path bits.
The inherited `RMEquiv.ipeq` relation expresses this observational equality.
The new `ibeq` checks it: when one list ends, every remaining bit in the other
must be false. The theorem `ibeq_ok` proves soundness by structural induction.

The branch checker still executes exactly the old `seg` function. It still
checks equality of the increment count for every register. It changes only
the comparison between a resulting pointer and its stored representative:
`ibeq` replaces literal list equality. Break and continue are still executed
on the exact consumed leaf path; their relative scopes are never normalized
prematurely.

The soundness proof uses the existing `RMEquiv.hn_ipeq` theorem to transport a
finite halting witness from the actual segment endpoint to its representative.
After applying the induction hypothesis, `halts_ipeq` transports the target
witness back. Register files remain equal at comparison points. A generic
mirror lemma supplies the reverse implication from the same forward check.
No second concrete evaluation is required.

The raw certificate distinguishes 2,240 pairs. Quotienting its redundant false
suffixes leaves 1,426 pairs: **814 fewer entries (36.3393%)**. There are 1,425
decrement entries and one halt entry, so the new check has 2,851 branch
obligations including its initial branch. This reduces the actual finite
obligations, in addition to compressing their printed representation.

## Source sizes and scope

| Item | UTF-8 bytes |
|---|---:|
| Production `Cert215Offsets.v` | 1,499,170 |
| Previous compact plain certificate (2,240 entries) | 171,678 |
| New normalized compact certificate (1,426 entries) | 109,115 |
| New generic normalized checker | 8,032 |
| New concrete source theorem | 901 |
| Inherited path codec | 1,325 |
| Inherited plain-checker mirror helpers | 2,570 |

The active certificate is 36.4421% smaller than the already compact plain
certificate, and 92.7216% smaller than the original explicit Boolean lists.
The generic checker has 196 lines; the concrete source theorem has 24.
These are source measurements, not a claim about total proof-object size,
complete endpoint compile time, or minimum machine size.

`NormalizedCert215.v` uses positive binary numerals and a transparent decoder
without a fixed path-length cap. Its materialized value is then checked by
the actual source checker. No Python generator or hash comparison is a
mathematical premise. The retained JSON is the exact inherited normalized
certificate; the renderer only changes its representation.

## Rebuild

The recorded local compiler is **Coq 8.18.0 with OCaml 4.14.1**. The production
repository uses **Rocq 9.1.0**. The only compatibility change is the inherited,
proved `Compat818.v` list-library alias shim imported into a private copy of
`RMEquiv.v`. Its original Rocq source is retained unchanged.

```sh
python3 generate_data.py
python3 build.py --out /absolute/path/to/new-build --recursive
```

The output directory must initially be empty. Every selected project module
is compiled serially from source. The shared proof-build lock covers each
compiler/checker invocation. A timeout or interruption kills and waits for the
entire process group before releasing the lock. The driver records exact
source hashes, compiler commands, raw logs, wall time, child CPU time and
Linux peak resident memory. `--recursive` additionally runs ordinary recursive
`coqchk` on `Source215Normalized`, with no admission or recursion bypass.

The accepted run is recorded in `verification/result.json`, with raw logs in
`verification/logs/` and a source/hash audit in `verification/audit.json`.
All **12 selected project modules compiled freshly**. The five new printed
assumption reports are closed, and the new modules have no warnings. Ordinary
recursive `coqchk -silent Source215Normalized` then succeeded, exit code 0,
with no `-admit` or `-norec` option. It took 543.8 seconds; the 12 compiler
children took 66.0 seconds combined (65.8 seconds CPU), with peak RSS
816,160 KiB. The concrete source module took 15.35 seconds; its forward
`vm_compute` transaction reported 7.006 seconds. These are measurements of
this standalone source closure, not a comparison against a fresh full endpoint
baseline. A prior development run compiled the same semantics
before a namespace-only cleanup; an intermediate clean run was stopped so
the warning-free final source could receive its own clean build. Those
development outputs are not used as the accepted verification record.

The driver recognizes the production Rocq 9.1 family and omits the Coq8.18
compatibility import there. That production-toolchain branch is supplied for
integration, not represented as locally executed.

## Attribution

The machine, numerical calculus, source programs and previous calibration
proofs are inherited from ProveIt. The normalization and 1,426-entry data are
inherited from the earlier incoming Lean packet. `NormalizedBisim.v` adapts
the pinned `K230P.Bisim230` soundness proof; the minimal K230 reference sources
derive from Elliot Glazer's `k230-rocq` commit
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`, with Jeff's reference ancestry.
The source files and license directory retain those notices. The path codec,
plain mirror helpers and Coq8.18 compatibility shim are inherited from the
prior `ZFC215_Proof_Simplification_2026-10-21.zip` packet. New port, rendering
and build work follow ProveIt's MIT No Attribution terms.
