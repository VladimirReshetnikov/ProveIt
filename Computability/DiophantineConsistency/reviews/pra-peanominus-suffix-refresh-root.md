# PA-minus translation after the OrderBasic refactor

Seven affected modules and checks, from `PRAPeanoMinusPartial` through the
candidate-PRA theorem translation, were rebuilt after the OrderBasic source
change. Two isolated replays at `/tmp/pra-peanominus-suffix-independent-k53_gkdn`
and `/tmp/pra-peanominus-suffix-independent-4sn5py78` passed with matching
source, object and complete-log hashes for all seven modules. The [author
packet](pra-peanominus-suffix-refresh-author-replay/manifest.json) documents
the reauthenticated unchanged local provider chain. Foundation and Mathlib
remain inherited boundaries, not a fresh transitive source audit.

A newer upstream change to `PRAQOrder` has arrived and is pending merge, so
these replays cover the preceding snapshot. The relevant downstream chain
must be rebuilt again after the merge. Neither this result nor the translation
proves IΣ₁ conservation or comparison with standard PRA.
