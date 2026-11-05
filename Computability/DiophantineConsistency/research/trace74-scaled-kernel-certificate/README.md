# Bounded scaled kernel-certificate experiments

The three scaled examples below each generate a deterministic 32-bit
Pell residue trace and positive Bézout coefficients. The generated Lean
file checks all 32 individual transition equalities and the Bézout
identity with `by decide`, then derives `Nat.Coprime` for the last ordinate
residue and modulus. There is no `native_decide`. The external Python
generator supplies **untrusted** trace and coefficient candidates; the
closed equalities and identity are checked by Lean.

| Scale B | Modulus bits | Lean exit | Wall time | Lean peak RSS |
| ---: | ---: | ---: | ---: | ---: |
| 17 | 34 | 0 | 1.870 s | 1,390,004 KiB |
| 257 | 514 | 0 | 2.016 s | 1,391,052 KiB |
| 4097 | 8194 | 0 | 2.516 s | 1,390,308 KiB |

These are the recorded 2026-11-04 runs. The runner verified from inside
each systemd cgroup that `memory.max=2147483648` bytes and
`memory.swap.max=0`; it imposed a 30-second subprocess timeout and Lean
`-M1800 -j1`. Each receipt records zero cgroup OOM/max events. This host
does not expose `memory.peak`, so the table reports the Lean child peak
RSS from `getrusage`, **not** cgroup peak memory. The kernel-enforced
cgroup memory limit applies to the whole scope.

For each successful run, `#print axioms` reports no axioms for the first
and last transitions and the Bézout identity, and `[propext, Quot.sound]`
for the derived `Nat.Coprime` theorem. All 32 transitions are separate
checked Lean declarations; only the first and last are printed in the
axiom report. Their sources, raw JSON traces, logs and cgroup receipts
are in [`observations/`](observations/).

These are **closed Nat checks**. The traces' numeric modulus and reduced
coefficients were generated externally; these files do not establish the
candidate's symbolic coefficient bindings, identify the list of checked
equalities with `Trace74PellBitlistChecker.run`, transfer the numerical
certificate to an arbitrary arithmetic model, or prove the concrete
`B=590069` gcd. They do not establish a graph zero or an iPRA endpoint.
The largest checked modulus here has 8194 bits, far below the candidate's
1,180,138 bits; no extrapolation to full-size feasibility is claimed.

## Reproduction

From the repository root, for each `B` in `17 257 4097`:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/trace74-scaled-kernel-certificate/generate.py B Computability/DiophantineConsistency/research/trace74-scaled-kernel-certificate/observations/BB
systemd-run --user --scope --quiet --property=MemoryMax=2147483648 --property=MemorySwapMax=0 python3 -I -S -B Computability/DiophantineConsistency/research/trace74-scaled-kernel-certificate/run.py B
```

Replace `B` and the suffix `BB` with the chosen number (for example,
`17` and `B17`). The runner verifies that the requested cgroup limits
were actually applied before launching Lean; it refuses other limits or
scales. It depends on the Lean 4.32.0 binary and the `LEAN_PATH` recorded
in each `result.json`. The direct imported
`Mathlib/Data/Nat/GCD/Basic.olean` SHA-256 is
`823dbab0d8c4e79d9bfc8aaa5637d880364bb11374210059fbd1884e94197e6f`;
transitive dependencies are the local built package artifacts. Generated
`.olean` files are ephemeral `/tmp` artifacts.

```text
7215491a511bc571fb908da475d48229f87150b4eaf574a946d81e823e4cf4e1  generate.py
3c76ad58839dff01df54be641ccf5e86e539fbfdd7cbf94289ef15018f17dd73  run.py
0438c83949897856c890fa21d0ddcf090f9ae94419563566d778ab459fbd2966  Trace74ScaledB17.olean
aa7ad0edee0f9102ccd845dc5467693554c2d5ecb8f10f469d2f735cb83eb6e2  Trace74ScaledB257.olean
4ec81010df5097dd9b6087eff0bbc5c523a8d89aacfa74feee3d15641ab8c2b2  Trace74ScaledB4097.olean
```

The first B=17 attempt used a 2 GiB **virtual address** limit and Lean
failed to create a thread before checking the source; the parent shell
reported exit 134, and the retained `address-limit.log` records the
failure. The accompanying `/usr/bin/time` output's `exit=0` reflects its
signal-reporting behavior and must not be read as a successful check.
An initial cgroup attempt then checked the Lean file successfully, but
the measurement wrapper failed afterward because `memory.peak` is not
available on this host; its Lean output is retained as
`first-cgroup-lean.log`. The table uses only the later complete receipts.
