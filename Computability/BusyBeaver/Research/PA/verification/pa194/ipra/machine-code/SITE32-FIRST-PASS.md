# Site-32 source branches and physical first header pass

`PA194SourceSite32Controller.site32Instruction` kernel-checks the actual source instruction `.dec 6 (some 34) (some 33)`. `zeroBranch` and `positiveBranch` prove the corresponding encoded source-controller transitions in every PRA model: register 6 zero goes to site 34 with the register file intact, and a positive register 6 goes to site 33 with that register decremented. The other registers and the controller tail are arbitrary.

`PA194Site32HeaderTo17.to17` proves a separate all-model literal-physical prefix from the actual site-32 path and two leading gap zeros to dense control 17. It preserves all 11 model-valued file arguments, including the complete arbitrary suffix, and gives the exact clock and output tape. It composes the eight-step path dispatch, further four fixed steps, and the prior model-length file scan. `PA194Site32HeaderReturn.returnTo24` and `PA194Site32HeaderPass.firstPass` extend this through the return to the same site-32 path header, retaining the transformed complete file word and exact clock. No theorem in this increment matches the site-32 source branch to a complete physical instruction; that still requires the register-6 selection, branch routes, and their source-frame return.

A fresh source replay succeeded, with no `sorryAx` and explicit axiom reports, using the following invocation from the repository root:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-first-pass.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-loop-to32-coherent /dev/shm/pa194-site31-matched-coherent \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-first-pass-replay
```

Choose a fresh output directory. The checker records hashes of the six source files, upstream receipts and direct prebuilt machine imports, including available Lean companion artifacts, and checks that they do not change during replay. It rejects conflicting direct machine imports and `sorryAx`. The physical-loop, matched, tail, carry, baseline and general foundation stages are prebuilt; their complete transitive object closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from the Lean search path; only its general foundation view is used.
