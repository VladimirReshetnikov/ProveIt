# Literal 64/65 rational-leaf identity

The guarded Lean check proves pointwise equality of the complete generated
64-row and 65-row graphs, and binds the latter to the existing
`DiophantineConsistency.Carrier65.value`. The two values therefore vanish
on exactly the same inputs. The identity holds in **any commutative ring**
under the two explicit symbolic assumptions

```
beta * Urank = MF
Wrank = MC - MF.
```

The proof uses no division or cancellation, and does not assume positivity
or nonzero beta. `rank_identity` proves the changed local rank equation;
`ranks_equal`, `values_equal` and `zero_iff` propagate it through the
complete shared suffix. `value65_eq_carrier` independently binds the 65-row
definition to the existing `Carrier65.value` arithmetic front. The
definitions and theorems are in `RationalCarrier64.lean`.

For a rational instantiation with beta nonzero one may take the fixed
leaves `Urank = MF / beta` and `Wrank = MC - MF`; this makes the two
assumptions true. This specialization, the actual huge port values and
their nonzero beta, and any connection to the printed PDF or an iPRA
derivation are **not instantiated or newly proved by this Lean module**.
The rational leaf is fixed, not a fifteenth witness; it is not necessarily
an integer. Hence this is not an integer-leaf 64-operation record, and it
does not replace the maintained 65-operation integer polynomial.

## Graph binding

`generate.py` emits the Lean definitions directly from the frozen JSON
graphs in `../rational-carrier64-independent/`: common 28-row prefix,
five-versus-six-row rank, and common 31-row suffix. The Lean data structure
used to share the prefix is proof representation, not an additional counted
graph operation. The separate read-only `audit.py` checks each literal row,
its port/coordinate/field aliases, shared regions and the successful
receipt. Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/rational-carrier64-lean-identity/audit.py
```

The audit is not a Lean replay; `generate.py` writes the Lean source if run.
The underlying JSON files have hashes `8fd205a43c4045914d88f4117ba263cf7a232ac26c64dcf09a1c37a8d88e7b27`
and `408dde55352b837db3c606db446f3bf41dc7fd6d9242808ba4a123930bf0b5ff`.

## Guarded check and limits

Attempt03 passed with Lean exit 0 and no warnings or `sorryAx`. The reports
for `values_equal` and `zero_iff` list `[propext, Quot.sound]`; the report
for `value65_eq_carrier` lists `[propext]`. The run used `-M2400`, a
120-second timeout, sampled 3.5 GiB process-group RSS limit, 10 GiB
available-memory floor, nice 19 and idle I/O. It took 2.431 seconds, with
peak sampled RSS 2,008,924,160 bytes; direct guards were stable. Resource
sampling and inherited transitive/dynamic provider ancestry are limitations.
The direct `Carrier65.olean` provider has SHA-256
`50fcfd8fdc6a8abb6641a57e3fe2070dbab6c4d38ec28cf32f6e4e12caa89951`;
its guarded path resolves to an existing object in a different worktree,
not to a freshly built source closure. The successful output object is
`/tmp/rational-carrier64-identity-priority-check03/RationalCarrier64.olean`,
SHA-256 `a2aa0510f8dc710e455981b605c304c2a0dbfe75e343d443f33eac27aeef8b43`.

Attempt01 failed with binder shadowing and an unavailable tactic; attempt02
had Lean exit 0 but the strict runner rejected one unused-simp warning.
Their exact source snapshots, generator snapshots, logs and receipts remain
in `observations/attempt01` and `observations/attempt02`. Attempt03's
retained log and receipt are in `observations/attempt03`. The respective
runner scripts are `check01.py`, `check02.py` and `check03.py`.

| Artifact | SHA-256 |
| --- | --- |
| `RationalCarrier64.lean` | `8676e328432ca3fd070dbd4abe6ae097137138aff4b2ceeead955e671f8b9a3b` |
| `generate.py` | `0da19fc7a5c175d5712a3e530363cd0f41965e9f73a6570729ad6ca4a8d67fde` |
| `audit.py` | `0abd52c72544550cff3626e4a2cbc88be8ff2c5305b369abca3304099b4b1960` |
| `check03.py` | `747de8d47715789be9727eb0ba5d4f7e6f830c36856c27972f30a12cd33ca574` |
| `observations/attempt03/compile.log` | `b1c3a224d14db8b6fb9aff207e9958407a69e2d670414dde9c05eef63e5a720a` |
| `observations/attempt03/result.json` | `daf3391dff8d54ceb64999b288cb6303046323733382777a680aa1e0996a86f3` |
