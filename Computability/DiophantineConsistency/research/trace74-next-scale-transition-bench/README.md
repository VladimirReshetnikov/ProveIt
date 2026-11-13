# Isolated B=65537 kernel checks

Four standalone files were extracted from the exact frozen
[B=65537 certificate](../trace74-next-scale-kernel-certificate/README.md),
without changing that parent source. They contain its common definitions
and, respectively, the original `transition00`, `transition15`,
`transition31`, and `bezout` declarations with exactly their required
state/coefficient declarations. The extraction script checks the parent
hash and records hashes of every extracted line in [`manifest.json`](manifest.json).

All four Lean checks exited 0 with no warnings; each `#print axioms`
reported that its checked declaration depends on no axioms.

| Isolated declaration | Wall time | Lean child peak RSS |
| --- | ---: | ---: |
| transition00 | 2.773 s | 1,378,668 KiB |
| transition15 | 4.936 s | 1,381,520 KiB |
| transition31 | 4.890 s | 1,379,308 KiB |
| bezout | 5.074 s | 1,381,536 KiB |

The actual limits observed inside each cgroup were 2,147,483,648 bytes
and zero swap, with a 30-second process timeout and `-M1800 -j1`. Each
receipt records zero cgroup max/OOM events. The host lacks cgroup
`memory.peak`, so the table is child peak RSS, not a full-cgroup peak.
Sources, logs, and receipts are under [`observations/`](observations/).

These checks show that the selected declarations can be verified
individually. They do not check the other 29 transitions, prove the
32-step chain or its initial index binding, transfer it into represented
model arithmetic, or establish the full candidate gcd. They do not
identify the cause of the parent run's 30-second timeout; the difference
could include cumulative work, parsing, or other effects. The proof and
resource results concern `B=65537`, not the actual `B=590069` modulus.

## Reproduction

From the repository root, regenerate the extracts and run each selected
name separately after acquiring the shared Lean slot:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/trace74-next-scale-transition-bench/derive.py
systemd-run --user --scope --quiet --property=MemoryMax=2147483648 --property=MemorySwapMax=0 python3 -I -S -B Computability/DiophantineConsistency/research/trace74-next-scale-transition-bench/run.py transition00
```

The other names are `transition15`, `transition31`, and `bezout`. The
runner refuses to overwrite an existing receipt; use a fresh copied
packet for a new run. It verifies the actual cgroup limits, the parent
source hash, and the extracted source hash before launching Lean. The
Lean binary and library paths/hashes are captured in each `result.json`;
the package and transitive provider ancestry are inherited.

```text
a064547e399f81e069dbd6098c93e86c211bbe2e82c619987de2af21c2745b4a  derive.py
ff4800d62c94b9b878a37b532ec45e506fd1696937c88b40b3149519a55e3ec6  run.py
36416d9989ab4abe3edb0396cefc736bf503cf3547d756cdbb03983995468fcb  manifest.json
f2c4a91bd7fc509b753766b82870044e8f088a2a5773b26b70d90e13641b9664  Trace74B65537-transition00.olean
78b62067f3dbfaab9fee5fa736fdb2b3ec8d620b0e215e6ceb65bfe12f3e8ed5  Trace74B65537-transition15.olean
bc262e9e4d4838c9a2798954b19d8b08ce36b7a3f3dbc21cab44d1bb5ded59f3  Trace74B65537-transition31.olean
14e69b4bb471cca20d52186aa34bf8dfa537bd2e5ea4f0bc5b8d28a5eb4d3064  Trace74B65537-bezout.olean
```

The `.olean` paths are temporary artifacts, not persistent dependencies.
