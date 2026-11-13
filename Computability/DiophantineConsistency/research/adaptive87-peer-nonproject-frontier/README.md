# Recorded nonproject inputs for the peer provider trace

The pinned records for the previously traced project objects identify exact
object hashes for all **94** Foundation, Mathlib and Lean module names in the
two preceding nonproject frontiers. One additional direct `Init` input is
also included. Across 673 selected producer rows, the scan records **1,204**
direct input edges and 95 distinct names. No name has conflicting recorded
hashes in these scanned rows. The machine-readable receipt lists every
producer row, module, recorded hash, observed path and mirror comparison.

At the time of this observation, **1,136** recorded or reconstructed producer
paths exist and match their recorded hashes. The remaining **68** edges cover
**26** distinct Foundation names; their recorded paths or reconstructed
historical mirror paths are absent or broken symlinks. For example, the
historical HA and PRA package mirrors' `Foundation/.../Basic/Hierarchy.olean`
links resolve to the now-absent `/home/codex/src/Proofs/.lake/build/lib/lean/`
object. For producer states that record only an import name and hash, the
checker reconstructs the path under that state's package mirror; the receipt
marks those paths as inferred, rather than claiming they were recorded paths.

The separate `/tmp/foundation-rebuild-20261101/.lake/build/lib/lean` contains
all 26 missing names, but **all 26 objects have hashes different** from the
historical hashes. That bounded comparison establishes a byte-level mismatch;
it does not establish Lean incompatibility or validate use of the alternative
with these project objects. It is not an exhaustive search of all possible
Foundation providers. A concrete next step toward an authenticated selection
is to locate the historically recorded objects or establish and verify an
appropriate coherent replacement/build chain; object presence alone cannot
satisfy that requirement.

Two retained manifests pin the Lean binary to SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`,
which matches the currently observed Lean 4.32.0 executable. This pins that
binary, not a full package identity. The checker pins the available alternate
Foundation build's `lean-toolchain` and Lake manifest bytes for identification,
but does not prove that manifest describes the historical objects or that its
transitive providers, companions and dynamic inputs agree. No future combined
`LEAN_PATH` or actual selected package provider has been established.

The scan is restricted to the producer rows already traversed by the two
previous receipts and their recorded **direct** Foundation/Mathlib/Lean/Init
imports. Other namespaces, source imports absent from the producer metadata,
transitive package imports, companion files, dynamic loading, source-current
status and all-model/iPRA conclusions remain outside its scope. The predecessor
receipts are pinned, not rerun. The selected object paths and toolchain are
point-in-time observations; temporary artifacts can change or disappear.

From `Computability/DiophantineConsistency`, reproduce with:

```
python3 -I -S -B research/adaptive87-peer-nonproject-frontier/check.py | cmp - research/adaptive87-peer-nonproject-frontier/receipt.json
```

The check reads and hashes existing files only. No Lean process, build,
cleaning, staging or mutation of provider evidence was performed.
