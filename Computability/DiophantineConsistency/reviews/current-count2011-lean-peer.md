# Current count composition: independent peer review

Date: 2026-10-26 UTC. Reviewer: `controller_certificate`. Root authored the
reviewed module and audit; the reviewer changed neither source. Result: PASS
for the explicitly conditional endpoint described below.

Frozen sources, read in full:

| File under `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `CurrentCount2011.lean` (66 lines) | `efb3403e3abc771a73f388be6adfdc90263902c8f8303d47fc933beb1fcc5f86` |
| `CurrentCount2011Audit.lean` (4 lines) | `67b3782db01f0b0716b1126eeb1e96098b2eb76e9cf21770e5cf3d2537058578` |

I also read the full invoked `CurrentClause2011`,
`NativePreliminaryCount2011`, `NativeBooleanRotation`, and
`PaddingStaircase` sources for this review. The first three source hashes
were respectively `a76daeaa24d3b3b00cfb80e2aaa3c9082740f9f8349a8d18014c912a9001c566`,
`ee138db4fc12507fa9dbd11c49aa6677c159bd1795588b5d0070c142e0080d2c`, and
`d50110d8f2a959df7da69f23e80b4df09a1aad98ba2b66c67d2445203cf81f3e`.

The exact composition is correct. At an actual cell base `b`, the clause
target is `b+1005`; its incoming carry is `carry(b+1004)` and its surviving
bare term is `c(b+1)`. The other bare terms have physical residues 987 and
996 and vanish by the supplied actual low support. The complete reflected
sum is retained, including collisions. Its residue is twice the selector
count modulo 2048, and the proved physical permutation identifies that
count with the 942-position prefix sum.

The temporal term is derived from the actual Boolean cyclic rotation as
`2^(W%47) * c((b+1005)-(W/47))`. Its underlying bit is Boolean by `hc`;
neither phase zero nor whole-cell alignment is assumed. The actual high
mask at the clause is `2^45-4`; the target cannot be the origin, so no
origin subtraction changes that mask. These derived statements and the
explicit carry bound supply every clause/count input to the generic
phase theorem.

The remaining middle-phase premise is accurately exposed.
`MiddlePadding c digits b` asks for exactly 483 residues and bit-three
tests at positions `b+64` through `b+546`, with auxiliary contributions
bounded by two. The existential auxiliary function is selected from that
premise only when `7≤W%47≤10`; outside this range its value is irrelevant.
The generic phase proof derives the initial count bound from Booleanity,
uses the staircase only in those middle phases, and concludes at most one
selector without assuming the desired result. No numeric table enumeration
or native calibration is hidden in this composition.

Independent direct replays, sequentially, from the repository root:

```sh
lake env lean -M6000 -j1 -o /tmp/current-count2011-peer.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCount2011.lean
lake env lean -M6000 -j1 -o /tmp/current-count2011-peer-audit.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCount2011Audit.lean
```

Both exited zero under Lean `v4.32.0`. The main replay log is empty, SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The audit log SHA256 is
`14ee27d69ac918d79971b1d50aa41bb14f66a361d7d84d4d3e3029d40112defb`.
Its endpoint reports only `propext`, `Classical.choice`, and `Quot.sound`.
The main source was independently elaborated; the audit imports the
existing root-built object for the same frozen source. This is not a
fresh replay of the entire imported dependency closure.

No correction is requested. This receipt does not treat the conditional
padding witness as already discharged, nor assert fractional-phase zero,
decoded labels, whole-field alignment, or the final consistency endpoint.
