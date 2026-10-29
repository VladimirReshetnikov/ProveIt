# PA-minus translation refresh after the Q reduct refactor

The source-current refresh rebuilt 24 affected modules and checks from
`PRAQCompatibility` through `PRAPeanoMinusTranslation`, over reauthenticated
unchanged local providers. The author run at
`/tmp/pra-peanominus-current-refresh-5lt4b6p4` and two isolated replays at
`/tmp/pra-peanominus-current-independent-3c517ryw` and
`/tmp/pra-peanominus-current-independent-7jvvp2zi` all passed, with matching
source, object and complete-log hashes for all 24 modules. The [author replay
packet](pra-peanominus-current-refresh-author-replay/manifest.json) records
the focused source and provider hashes. Foundation and Mathlib remain
inherited boundaries; this is not a fresh transitive build.

This verifies the candidate-PRA PA-minus translation at this source snapshot.
It does not establish Σ₁ induction elimination, IΣ₁ conservation, or the
comparison with a standard PRA presentation. A further upstream change to
`PRAPeanoMinusOrderBasic` has arrived and is pending merge; the affected suffix
must be refreshed again after that merge.
