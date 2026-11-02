# Unlaunched source-current coexistence replay preparation

`freeze.py` computes a declared import graph rooted at the tracked
`FreeJProviderChecks.lean`, freezes exact current Git blobs into an isolated
snapshot, rejects shadowed research-source overrides, and requires the source
checkout, HEAD and config to remain stable. Its current workspace survey
finds 70 project modules and 22 direct external imports: the surveyed 64
project modules, five existing research-source modules, and this checks
module. This is a static source survey, not Lean's authoritative import
resolver or a successful freeze of the final committed endpoint. The target
prints three axiom reports for coexistence of the difference-ring provider,
free-J residual, and cleared identity; it does not prove graph transport,
ordinary integrality, checker calibration, or an iPRA theorem.

`test_freeze.py` passes source-parser, topology, external-import, cycle and
missing-source toy controls; `py_compile` also passed. The existing guarded
`fresh-project-closure/rebuild.py` and comparator are intended for two fresh
siblings. Their package-transitive and dynamic dependency limitations remain.
A sampled process-group monitor/coordinator is separately being prepared.
These components require independent review, a fresh tracked HEAD freeze,
actual compiler-dependency checks, sampled disk/budget monitoring and actual
process exits before any claim of a real run. No project rebuild has started.
