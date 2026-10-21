# Second 216-state candidate: permutation 120

This corroborating variant assigns selector 0 to DROP, selector 1 to NIP, and selector 2 to MP. AX retains fields `[c+3,y,x]`. It has the same all-natural source calibration as the primary 210 candidate; the report proves both assignments.

`k216-120.native.tm` has 216 working states, 432 rows, initial state 0, native dispatcher 84, and halt label 254. Relative to the pinned native K217 predecessor, its recipe changes 38 retained rows, removes native state 134, and adds no state. `k216-120.tm` is its canonical renaming to states 0–215 and halt 216.

Native SHA-256:

```text
be663ef8daf05d42ad6f0c9972f4a3e7bd18e55f84d8c83f5c7b0867221fbb72
```

Canonical SHA-256:

```text
0e384c502134e67897a998fc679bcb7f7d2172000e54279b304a9c40bb8ab753
```

All 6,176 universal primitive cases pass, using 1,605,505 compressed symbolic steps. The smallest affine duration constant is 9; every case has a positive finite clock. Literal blank startup takes 96,244 transitions and ends at the same complete 95-one-cell clean source frame as the primary machine: native state 84, head −8, extra gap 1, registers `[4,0,0,0,0,0,0,0,0]`, and forty spare registers of value one.

The complete startup trace and ordered universal case receipts are compressed with gzip. From the enclosing packet directory, `python3 -B verify.py --secondary-runtime` reconstructs both tables and freshly derives all runtime cases for this secondary one. Add `--runtime` to derive the primary cases as well. The default verification already replays this secondary blank prefix and checks its stored runtime inventory.

This candidate has the same mathematical proof boundary as the primary: no new exact-table Lean/Rocq endpoint is claimed.
