# Packaging path adjustment

The independent semantic-spine audit is newly authored research code. Its
additional-baseline directory was changed from
`audit/semantic_spine_extra_sources/` to
`review/snapshots/compatibility/` so the same 29 exact pinned sources are shared
with the main source audit rather than duplicated. This is a one-line path-only
change; source bytes, hashes, check logic, and measured metrics are unchanged.
The review note now names that packaged path and does not pin the number of
redundant convenience copies. The independently written decrement replay is
included unchanged. All audits run against a temporary package copy.
