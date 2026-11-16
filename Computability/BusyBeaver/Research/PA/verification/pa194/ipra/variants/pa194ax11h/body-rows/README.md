# AX11H body source-row binding

The deterministic generator produces 28 Lean modules covering source sites 50–3518 in chunks of at most 128, plus an aggregate. Each chunk checks equality between the literal candidate source-program list and the corresponding instructions resolved directly from the primary source trie using `decide +kernel`. `PA194AX11HBodyRowsAll.agreement` combines those checked equalities into `PA194AX11HBodyCopy.BodyRowsAgree`, the sole finite source-binding premise of the AX body proof.

From the repository root, after replaying the body-proof and gate-window stages:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/body-rows/check.sh /dev/shm/pa194-ax11h-body-rows-repo /dev/shm/pa194-ax11h-body-proof-repo /dev/shm/pa194-ax11h-candidate-gate-repo
```

The output must be fresh. The checker regenerates the chunk sources in its output, records their hashes along with its generator, common proof, and named direct input objects, then checks every chunk and the aggregate in a single output. The body-proof output retains its documented staged transitive dependencies. The checker rejects `sorryAx` and reports Lean axioms.
