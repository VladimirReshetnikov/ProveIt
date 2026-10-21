# Late public 216-state construction: credited reproduction

While this research was running, ProveIt advanced from the initially inspected
commit `d3d6b8c14e1ddff37eb1417c5448caa41cfd6da7` to
`d59b4418821c598c4703f0a60b1f7cbae4f3bcf6`. That latter commit adds
`docs/incoming/K216_Permuted_Commands_2026-10-21.zip`.

The complete original archive is retained here unchanged, including its report,
TeX sources, two machines, parent archives, and authorship/license notices.
**This is an upstream construction, not a machine discovered in the present
research.** It was under repository review when inspected. Our contribution
here is a fresh selected reproduction and comparison with our separate work.

The canonical primary machine is additionally available as `machine/k216.tm`:
216 working states, start 0, separate halt 216, 432 binary transition rows.
Its SHA-256 is
`b0cf986df02fc0383c788f3d06ac46ac179ed81b3f1546115668c13bf72eeaea`.

The fresh session replay reconstructed the exact source and native/canonical
tables, checked the command permutation and guarded source graphs, replayed the
entire 95,674-step blank prefix with sparse and dense interpreters, and freshly
derived all 6,176 universal primitive cases. Every ordered case and the entire
startup trace agree with the submission. The cases contain 1,605,450 symbolic
rules, minimum positive duration constant 6, and coverage of all 432 rows.

These are ordinary mathematical certificates with the pinned inherited
numerical-calculus/ZFC calibration. No new exact-table Lean/Rocq or internal PA
endpoint is asserted, and foundational interpretation or ancestor runtimes were
not freshly replayed as part of these selected checks.

Run from any directory, using a new output directory:

```bash
python3 -B /path/to/upstream216/replay.py --output /tmp/k216-selected
python3 -B /path/to/upstream216/replay.py --runtime --output /tmp/k216-selected-full
```

The first command checks the manifest, finite construction, both blank
interpreters, and the stored complete ordered case inventory. The second also
freshly derives every universal primitive case from the literal table, using
the exact checker extracted from the submitted ancestor archive. It typically
takes a few minutes. The supplied `fresh/` records are from an actual fresh
universal replay during this session; they are not inferred from the default
inventory check.

The contemporaneous `K216_Partial_Selector_2026-10-20.zip` arrived separately in
commit `6ec69081ca2a4abc03c35b573e22eb0d939a6324`. The successful further composition is the new 215-state candidate under
`../candidate215/`. Its source, constrained allocation, complete runtime,
and blank prefix were separately proved; the savings were not added by
state counting alone.
