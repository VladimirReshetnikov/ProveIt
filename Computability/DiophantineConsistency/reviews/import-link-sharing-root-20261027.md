# Preserving proof evidence while sharing duplicate import links

27 October 2026. A metadata-only operation recovered approximately
199 MiB by sharing 51,119 duplicate symlink inodes across 120 verified
terminal task build overlays. Eligibility required a terminal PASS/FAILED
state and the task's known overlay prefix. Active build directories were
excluded. Matching links had the identical target, device, owner, group
and mode. Each replacement used a temporary hardlink and atomic rename;
the original path, symlink target and provider content hash were verified.

All regular compiler outputs, source files and evidence remain present.
The complete pre-operation link inventory, terminal state pins, provider
hashes, executed driver and PASS result are preserved under
[the audit directory](import-link-sharing-root-20261027/FILES.json).
Free space rose from 570,802,176 to 779,644,928 bytes at observation time.
This changes no mathematical proof, dependency selection or acceptance.
