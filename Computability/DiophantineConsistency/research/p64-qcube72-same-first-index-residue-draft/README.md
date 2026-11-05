# Residue of the same fixed-compact first index

`FreeMainSameFirstIndexResidue.first_residue` proves in any IΣ₁ model that
`0<P` and `2*ycoord n (2*(P−1)+1)=k` imply `k=2n+4P*s` for some model
element `s`. It applies `residue_quotients` directly to that given `n`, so no
identification of an existentially reselected index is needed.

`fixed_window_residue` applies this to an actual positive 72-graph zero at
fixed compact44 beta and masks, for arbitrary natural K. It retains the same
`n` with `n<R<2n`, its two first Pell-coordinate identities, and the
residue with `P=XY²`. This supplies one premise of the separate
[carrier-gap analysis](../p64-qcube72-fixed-compact-carrier-gap/README.md).
It does not prove the old carrier, `2n=R+1`, reverse existence, or an iPRA
endpoint.

Attempt01 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and both expected `[propext, Classical.choice, Quot.sound]` axiom
reports. The source's unchecked-draft header predates this check. Its direct
provider is the fixed compact index-window object. Transitive/dynamic ancestry
and sampled monitoring are inherited; this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainSameFirstIndexResidue.lean` | `cfe7d173bca44c10d25bc39fb1175bc560d8f7e3c098cb2f488f823b8560c745` |
| `check01.py` | `4837efdeb6daa67fb71e6ea3bd8e1ae2117a65c038c50740483bbd010df213ed` |
| `observations/attempt01/compile.log` | `a9892d173505ef20be0090a9803dbaac0c4b5de292bc26ceea1e9fb48b854e77` |
| `observations/attempt01/result.json` | `d70e9ec84c6f808ae05498f909b160282ff9c1a356564650633e52bbee0c5e58` |
| `/tmp/p64-qcube72-same-first-index-residue-priority-check01/FreeMainSameFirstIndexResidue.olean` | `35e42a6ac21791795d2a7cb2c5aa6857203d721168f5f60d6852146b4df871a1` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority.
