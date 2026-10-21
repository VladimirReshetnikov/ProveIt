# CM215 transport in the exact Rocq stream semantics

This packet closes the representation gap for the previously supplied CM215 alternative. It does **not** introduce a new machine or claim a 214-state result. Its exact `marker215.tm` is the existing 215-working-state, 430-row conditional-marker machine, SHA-256 `1f4f084f7293e2b042d5746039f793ff72ed429083b504970c939a5515e666cf`.

`CM215Stream.v` imports the **unmodified** `K215F.Dense215` from ProveIt commit `aa66d0a33f1f8237a348899eb8095b045a502832`. Its states are that module's bounded naturals `bnat 215`, and its tapes are that module's pairs of coinductive streams with a scanned bit. It proves, for every left stream `l`, scanned bit `b`, and right stream `r`,

```coq
Dense.halts dense_tm (bmk 215 0,(l,b,r)) <->
Dense.halts cm_tm    (bmk 215 0,(l,b,r)).
```

The two final assumption reports are `Closed under the global context`. The theorem was compiled with Coq 8.18.0 and recursively checked by the matching `coqchk`. A clean reproduction receipt accompanies the packet. No functional tape semantics, functional extensionality, guessed stream equality, startup replay, or new source/calculus theorem enters this transport proof. The inherited BusyCoq tactic library imports some unused axioms; the **two target theorems** have closed assumption reports.

## What is new here

Earlier incoming proposals prove CM215 equivalence in standalone tape models or Lean Core, and include standalone Rocq transport for the related M124/FM215 marker family. This contribution proves the CM215 equivalence directly in the **same** bounded-state, stream-tape semantics as the accepted Rocq K215 endpoint. The machine and the underlying predecessor-marker method are inherited. The local facts are a single finite reflected certificate, and a small positive-progress transport proof reuses BusyCoq's existing `progress_halts` lemma.

The six changed dense rows are 52/0, 151/1, 160/0, 170/0, 170/1 and 184/0. State 170 is mapped to 52 at synchronization points. The source invariant has just three clauses:

1. At state 52, the bit immediately left of the head is one.
2. At state 170, if the current bit is zero, the left bit is zero.
3. At state 151, the bit immediately right of the head is one.

One old transition becomes one or three CM215 transitions. At every synchronization point, the entire stream tape is identical and only the control state is relabelled. Both halting directions follow from this one forward simulation because the target blocks have positive length and halting is reflected at boundaries.

## Reproduce

Python 3 and Coq 8.18.0 with its matching `coqchk` suffice; no network access or additional Coq packages are needed.

```sh
python3 check_inputs.py
python3 reproduce.py --work /path/to/empty/build-directory
```

The driver verifies the pinned inputs, compiles nine sources serially, checks both closed target-assumption reports, and recursively rechecks `CM215Stream`. It writes a detailed `verification.json` in the chosen build directory. The four `vendor/K215F` sources are copied byte-for-byte from the specified ProveIt commit; three `vendor/BusyCoq` sources are copied byte-for-byte from Jeff's pinned reference commit `c132d7eae8158cd3a9850ea3eb7251158c3dd821`, `ZF/stdzf_r3/vendor/busycoq/`. The input manifest records all hashes. `check_inputs.py` independently binds all 430 `.tm` rows to `CM215Table.v`.

## Endpoint composition boundary

`CM215Endpoint.v` composes `blank_halts_iff` with the existing
`K215F.CorrectDense215.tm215_halts_iff_ZFC_inconsistent`. Its statement is the expected ZFC refutation equivalence for `cm_tm`, but that integration client and the full inherited 237-source endpoint closure were **not** rebuilt in this packet. It is excluded from the nine-source standalone reproduction driver and identified as integration-only. The newly verified result is the closed, exact-semantic all-tapes equivalence to the accepted K215 table; no new calibration assumption is introduced into that result.

## Proof simplicity recommendation

For extending the accepted proof, CM215 now has a direct Rocq transport in the accepted semantics, so its extra proof burden is small. The M124 marker variant has an even simpler local invariant (two unconditional predecessor-bit clauses); its existing independent tape proof still needs a native adapter of the same kind. Neither alternative makes the inherited K-to-ZFC calibration disappear. The useful architectural change is to certify that calibration once and transport exact tables through local, positive-length rewrites.

## Attribution and license

The conditional-marker machine and all earlier calculus, compiler, source, calibration and symbolic-runtime work remain the contributions of their original ProveIt and upstream authors, including Elliot Glazer, Jeff's busy-beaver development, and the compiler ancestry documented in ProveIt. The new native-stream proof and reproduction scripts follow ProveIt's MIT No Attribution terms. BusyCoq is by Maja Kądziołka; its LibTactics dependency credits Arthur Charguéraud and Software Foundations. Their original notices are retained in `licenses/`, and their sources are unmodified.
