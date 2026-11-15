# One checked startup return to site 27

`PA194SourceSite30Physical.sourcePhysical` proves uniformly in every PRA model that the actual source-controller jump from site 30 to site 27 matches exactly 40 steps of the pinned physical machine. The theorem permits arbitrary model-valued logical registers, physical spare and suffix, and independent controller-file tail; the source state is unchanged except for its PC, while the physical zero-run padding grows by two.

`PA194SeedControllerReturn27.blankAndFiveSteps` composes that jump with the certified blank-tape startup and the four earlier matched source/physical steps. It proves that the physical blank and the startup's actual site-25 controller state reach matching site-27 frames after five controller steps and an existential model-valued physical time. The resulting file contains the two added one-valued spare blocks. This is a finite model-level theorem, not a native iPRA proof or an arbitrary-time source/physical simulation. In particular it is not an iterable loop theorem: the available increment proofs require particular fixed physical suffixes, while traversals extend the suffix.

The two new sources are `PA194SourceSite30Physical.lean` and `PA194SeedControllerReturn27.lean`; the checker also rebuilds the seven new sources and controller suffix listed in `SEED-CONTROLLER-REACH30.md`. Invoke from the repository root with:

```
/dev/shm/pa194-site28-controller/check-seed-controller-return27.sh "$PWD" /dev/shm/pa194-model-length /dev/shm/pa194-source-controller /dev/shm/pa194-source-physical /dev/shm/pa194-site27-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site28-controller /dev/shm/pa194-site28-work/build-complete /dev/shm/pa194-site28-work/build-finish-return /dev/shm/pa194-site28-work/build-site29-selected-return /dev/shm/pa194-site28-work/build-carry-seven /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site28-work/build-carry-codes /dev/shm/pa194-site28-work/build-site29-to-increment /dev/shm/pa194-site28-work/build-site29-return-to-root /dev/shm/pa194-site28-work/build-site29-path30-identities /dev/shm/pa194-site28-work/build-site29-complete /dev/shm/pa194-site28-work/build-site30-jump
```

The checker rebuilds the encoded-controller and physical bridge suffix in one fresh output and audits the printed axioms for `sorryAx`. The coherent site-27 baseline, eleven disjoint physical stage directories, graph overlay, and foundations remain prebuilt; direct pins and disjoint object names do not authenticate the stages' full transitive closure. The site-30 physical jump was separately replayed with exit 0 in `/tmp/pa194-site30-jump-check.log`. The combined independent replay log is `/tmp/pa194-seed-controller-return27-replay.log`; consult its final PASS and exit status before relying on it.

The repository-source replay also passed using this directory for all four
source-directory arguments and the same retained overlays.
