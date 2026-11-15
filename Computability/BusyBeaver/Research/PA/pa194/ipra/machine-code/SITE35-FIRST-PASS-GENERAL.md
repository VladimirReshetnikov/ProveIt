# Site-35 first root pass

`PA194Site35FirstPassGeneral.firstPass` proves in every PRA model that the literal site-35 frame with gap `k+2` completes one physical root pass, preserving the actual site-35 path and transforming the entire file word exactly as shown in the theorem. Every register and the arbitrary suffix are model-valued; there is no blank-tail assumption. The prefix's 10 finite transitions and the return's first transition are kernel checked, and the rest of the return reuses the checked site-34 positive return. The clock is explicit and model-valued.

This is the first root pass, not the site-35 increment, a native iPRA sentence, the complete physical decoder, or the consistency equivalence.

The six sources in build order are `PA194Site35PrefixGeneral.lean`, `PA194Site35To15General.lean`, `PA194Site35To16General.lean`, `PA194Site35To17General.lean`, `PA194Site35RootReturn.lean`, and `PA194Site35FirstPassGeneral.lean`.

The fresh staged replay passed with exit 0. Replay with a fresh output directory:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site35-first-pass-general.py "$PWD" /dev/shm/pa194-site28-work /dev/shm/pa194-site34-positive-physical-repo \
  /dev/shm/pa194-site34-branch-repo /dev/shm/pa194-site34-second-pass-repo /dev/shm/pa194-site34-to14-repo /dev/shm/pa194-site34-first-pass-general-repo /dev/shm/pa194-site34-first-pass-repo /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site35-first-pass-general-repo
```

This incremental checker rejects conflicting direct machine-object overlaps and `sorryAx`, checks named axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this replay. The fetch machine-object root is excluded from Lean's search path.
