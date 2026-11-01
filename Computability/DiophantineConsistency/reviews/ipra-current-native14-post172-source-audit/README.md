# Independent audit of the original 14-variable source capture

The audit checks all 995 frozen source bytes and their import headers,
reachability from the target, the 984 shared and 11 additional sources, the
four edits from the prior capture, topological order of the 11 additional
modules, and the inherited dependency receipt hashes and fresh Lean-header
outputs. Its receipt records the actual workspace drift in `LGlueCodes` and
`SetCongruence`. The Git HEAD changed during the original capture; the two
source drift scans and the independently checked captured hashes are reported
separately rather than treating a constant HEAD as evidence.

This is a source-only audit. Object origins, complete package and dynamic
ancestry, and a coherent original-equation proof replay remain separate.
