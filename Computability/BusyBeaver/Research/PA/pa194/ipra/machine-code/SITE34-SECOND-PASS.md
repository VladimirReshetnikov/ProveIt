# Site-34 second root pass

`PA194Site34SecondPass.secondPass` proves in every PRA model the exact literal physical run from a site-34 frame with gap `k+2`, through the first and second header passes, returning to the site-34 root. Its exact PR arithmetic clock and output unary-header expression are stated explicitly in the theorem. The complete file, the individual register values, and arbitrary residual suffix are retained. The 24 literal rows of the final return are individually proved in Lean, with no reliance on the exploratory interpreter that suggested them.

This completes the second root pass, before the selected-register decision. It does not prove either site-34 branch, the full decoder, a native iPRA sentence, global simulation or a consistency implication.

A fresh staged source replay passed with exit 0, three axiom audits and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site34-second-pass.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site34-to14-repo /dev/shm/pa194-site34-first-pass-general-repo /dev/shm/pa194-site34-first-pass-repo /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site34-second-pass-repo
```

Use a fresh output directory. The checker rebuilds three modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires each named axiom audit, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
