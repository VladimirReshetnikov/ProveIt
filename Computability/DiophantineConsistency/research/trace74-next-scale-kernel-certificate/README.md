# Bounded next-scale certificate attempt

This packet follows the [three successful scaled experiments](../trace74-scaled-kernel-certificate/README.md)
at `B=17,257,4097` with a separate `B=65537` candidate. The original
generator, runner, and observations are unchanged; the copies here allow
only the new scale.

An external Python computation first reported modulus and final residue
of 131,074 bits and `gcd=1`. The separately generated
[`trace.json`](observations/B65537/trace.json) and
[`Certificate.lean`](observations/B65537/Certificate.lean) are untrusted
certificate candidates. The Lean source contains 32 transition equality
checks, a Bézout identity, and a `Nat.Coprime` consequence, using
`by decide` and no `native_decide`.

The sole kernel-check attempt reached its **30-second timeout**. The
runner reports 30.083 seconds, Lean child peak RSS 1,384,452 KiB, an
actually observed cgroup `memory.max=2147483648`, `memory.swap.max=0`,
and no OOM/max events. Lean emitted no output before termination; no
completed theorem or `.olean` was observed. The full machine-readable
receipt and hashes are in [`result.json`](observations/B65537/result.json).

A P64 diagnostic began concurrently because of a coordination race and
was interrupted promptly after the overlap was noticed. The overlap
qualifies the timing as a performance measurement. The timeout is not a
mathematical failure, a failed gcd claim, or proof that a longer or
different kernel check would fail. This observation does not determine
an appropriate larger scale or resource limit.

## Reproduction and scope

From the repository root:

```sh
systemd-run --user --scope --quiet --property=MemoryMax=2147483648 --property=MemorySwapMax=0 timeout 30 python3 -I -S -B Computability/DiophantineConsistency/research/trace74-next-scale-kernel-certificate/generate.py 65537 Computability/DiophantineConsistency/research/trace74-next-scale-kernel-certificate/observations/B65537
systemd-run --user --scope --quiet --property=MemoryMax=2147483648 --property=MemorySwapMax=0 python3 -I -S -B Computability/DiophantineConsistency/research/trace74-next-scale-kernel-certificate/run.py 65537
```

The kernel runner verifies its actual cgroup memory and swap limits
before starting Lean and records the direct Lean command and package
paths. It measures child peak RSS because the host does not expose
`memory.peak`. SHA-256 hashes for this attempt:

```text
07393873a6b2fd5ae2ff8a076b6060f21b8502d49e92b34e8b3ca3a57ed8446c  generate.py
cfa890d2a5a356f2d4d885490dd5c593208825228e43dd0d99d3f37473329468  run.py
63eafa7643cb1f0505739b7b6902f9b457d5e4af9be19bac3a79573f281a6a2c  Certificate.lean
03bae13ef4a9cfdc74126d171ed037fd03d62fb20121c255df494a343c99636d  trace.json
0f5dc7ecbe8c8de7e4083e061af2410ed12797e329665ce052e99715b5373968  result.json
```

Even a future successful closed natural-number certificate would still
need its coefficient bindings and transfer to represented model arithmetic.
This attempt does not prove the target `B=590069` gcd, a graph zero, or
an iPRA endpoint.
