# Site-25 source-controller and physical-frame bridge

The two Lean theorems relate the newly encoded finite PR source controller to the pinned literal PA194 physical stepper in every candidate PRA model. For arbitrary model-valued `k`, the nine logical register values, the physical spare, the physical suffix, and the separate encoded-controller file tail:

* `PA194SourceSite25Physical.zeroBranch` assumes logical register 8 is zero. The encoded controller takes site 25 to site 27 with its register file unchanged, and the matched physical site-25 frame with zero-run count `(k+1)+1` reaches the corresponding site-27 frame with zero-run count `k+1` at an existentially supplied model-valued clock.
* `PA194SourceSite25Positive.positiveBranch` assumes register 8 equals `m+1`. The encoded controller takes site 25 to site 26, updates that register to `m` and preserves the rest of the file, including its arbitrary tail. The matched physical frame reaches site 26 with the same register update, at zero-run count `((k+1)+1)+1` and an existentially supplied model-valued clock.

Both physical frames use the actual pinned source-program paths, the same eleven logical/physical inputs, and the same original physical suffix. The physical clock witnesses are supplied by the previously proved explicit-clock physical theorems; these two bridge statements quantify them existentially. The controller file's arbitrary tail and the physical spare/suffix are independent, and the theorem relates their shared nine logical registers. The positive file-update lemma proves equality of the complete nested-pair controller file, not merely its individual register projections.

These are all-model Lean theorems for one source instruction, not model-length simulation or native object-iPRA derivations. They do not prove a global source-frame invariant, cumulative clock, abstract scheduler correspondence, or either Con(PA) direction. In particular, the source run's earlier no-malformed model invariant does not establish that physical frames stay synchronized.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site25-controller-physical.sh "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-site27-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The staged wrapper rejects inherited Git overrides and checks source hashes, the site27 and earlier coherent manifests, and a receipt of 26 direct physical baseline objects. It rebuilds the controller source chain, the repository's `PA194Site27PathStep` and `PA194Path25To27`, and both bridge modules together in a fresh output; it audits their printed axioms. The single retained PA194 machine root is the prebuilt site27 coherent baseline. The graph/equality-code overlay and project and package foundations remain prebuilt. Hashes and manifests identify these retained dependencies but do not independently reconstruct or authenticate their full transitive source closure and cross-overlay compatibility. This is a staged replay, not a self-contained full build.
