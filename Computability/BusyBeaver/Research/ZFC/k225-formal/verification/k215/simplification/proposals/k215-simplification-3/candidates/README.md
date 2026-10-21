# Reproduce the candidate-interface comparison

This directory is standalone. Python 3.10+ and its standard library suffice. No repository checkout, Git, network, received executable, or ZIP archive is required. The checker is independently written; `inputs/` contains only exact received tables, source-site lists, and the original native/dense renaming map.

Run with assertions enabled:

    python3 -I audit_candidate_interfaces.py --expected finite_interface_audit.json

The checker recomputes every result and prints JSON. The default does not modify this packet. To save a fresh result, add an external output path:

    python3 -I audit_candidate_interfaces.py --expected finite_interface_audit.json --output /tmp/candidate-audit.json

The checker rejects `-O` and `-OO`. It verifies the hash of `INPUTS.json`, then the SHA-256 and size of all 22 inputs before interpreting any data. `INPUTS.json` retains repository commit/URLs and received-archive or packet paths as provenance; none of these paths are runtime dependencies.

The audit checks the original table's literal native/dense commuting diagram, the CM215 six-row patch, unchanged rows up to the state map, its strengthened marker invariant over all satisfying local windows, its two exact local blocks, source equality, and seven candidates' table/source metrics. It does not verify the complete source CFGs, blank initializations, symbolic runtime, numerical-calculus calibration, or Lean/Rocq endpoints.

`portable_audit.json` records a fresh replay after copying this directory outside the original tree and running from an unrelated working directory under isolated Python. Its output was byte-identical to `finite_interface_audit.json`. Negative controls rejected optimized Python and a modified table.

Read `COMPARISON.md` for the mathematical assessment, evidence limits, source references and formal transport plan. The evidence is ordinary finite checking, not a newly kernel-checked theorem. Original authorship and inherited mathematical contributions remain those of ProveIt and the cited packet sources.
