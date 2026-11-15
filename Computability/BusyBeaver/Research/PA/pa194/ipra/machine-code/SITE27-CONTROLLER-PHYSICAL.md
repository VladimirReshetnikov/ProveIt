# Site-27 positive branch: encoded controller and physical frame

`PA194SourceSite27Physical.site27Instruction` kernel-checks that the actual resolved source instruction at site 27 is decrement register 0, with zero destination 31 and positive destination 28. `positiveBranch` proves in every candidate PRA model that if register 0 is `m+1`, one step of the finite PR encoded controller reaches site 28 with that register set to `m` and the complete remaining controller file, including its arbitrary tail, preserved. The matched literal PA194 site-27 frame reaches the site-28 frame with the same register update and the same physical zero-run count `(k+1)+1` at some model-valued clock. Its physical spare and suffix are arbitrary. `matchedPositiveStep` packages the result using the reusable `Matched` frame relation and an explicit witness for the positive branch.

The physical clock is existential in this bridge; the imported physical segment theorem contains an explicit clock. The site-27 zero branch, a common relation/clock for all 3,673 sites, first-order definability, arbitrary model-length synchronization, the abstract scheduler bridge, and native iPRA/Con(PA) equivalence are not proved here. This is an all-model Lean theorem for one source branch, not an object-theory theorem.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site27-controller-physical.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-site27-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The staged wrapper checks named source hashes, the retained site27 coherent manifest, and receipts for the direct physical baseline objects. It rebuilds the source controller chain, the site-25 physical suffix and relation, `PA194Path27To28`, and the new bridge together in one fresh output, auditing printed theorem axioms. The sole retained PA194 machine root is the prebuilt site27 coherent baseline; the graph/equality-code overlay and project/package foundations also remain prebuilt. The manifests and object hashes do not reconstruct or independently authenticate their full transitive closure or all cross-overlay compatibility.
