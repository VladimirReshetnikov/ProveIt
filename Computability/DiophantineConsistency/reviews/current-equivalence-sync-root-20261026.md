# Root synchronization record after the external equivalence checkpoint

Root fetched `origin/main`, inspected the incoming active diff and read the
entire independent [source review](current-equivalence-upstream-sync-20261026.md)
(SHA-256 `a203946c17a22a740e6ab175e76a19fea0eaee15575b93ab7418e45abbb8e3b9`).
That review pins the eleven active proof-source changes through3299f4aa4c,
preserves all104 old theorem/lemma headers and every executable data field,
and explicitly distinguishes reported upstream builds from fresh replay.
Root read the full eleven-file active diff, including the doubled Pell
bound, impulse rotation, arbitrary-model environment restriction and formal
two-radicand combiner proof. No blocking finding was identified.

The final fetch advanced the remote to60fcb2a69b. Root inspected its complete
path inventory, both new placement records and both index diffs relative
to3299f4aa4c: it adds only two inert research packet placements and their
indexes, with no further active source, equation, toolchain or manifest
change. Packet scripts/proposals were not executed or adopted.

`git -c gc.auto=0 merge --no-stat origin/main` completed cleanly at
`b96d387147f0b0e2659446e3a7ff11447286affc`, retaining local external-equivalence
commit13389f141a and all preceding native/Pell construction commits.
`git merge-base --is-ancestor origin/main HEAD` and `git diff --check` passed.
The merge leaves the maintained decimal artifacts byte-identical:

- TeX `a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e`
- PDF `417c2fa109cacf99d0e83af35d06cbdc8fed1179054d7245e07f3e51ebfff978`

The final external-equivalence endpoint had independently fresh main/check
builds before this merge, with unchanged statements in the incoming
prerequisites. This synchronization record does not relabel those builds
as a fresh post-merge dependency closure. A source-authenticated current
closure audit is being prepared separately. The actual push uses the
ordinary non-force `git push origin HEAD:main`; success or a remote race
is reported by Git, not inferred from this pre-push receipt.

The unbounded goal remains active: internal-ZFC derivation and further
equation-size reduction continue. The unrelated marker997 proposal is
not promoted, staged or discarded by this synchronization.

## Remote race and successful ordinary push

The first push was rejected because the remote advanced to726ea9af9d.
Root fetched it and read its entire ten-path diff. Five annotated modules
only inline deleted one-line private list-lookup wrappers with the exact
same `List.mem_of_getElem?` / `List.getElem?_of_mem` calls. The sixth Lean
module replaces arithmetic index normalization by `Nat.sub_add_cancel ht`,
retaining ht≥1 and every declaration/data field. The two generator changes
specify UTF-8 and LF I/O; they were read but not executed here. The other
two files update explanatory/adoption documentation. No equation, machine,
port, witness domain or public theorem statement changed.

Root merged that `origin/main` cleanly into09eaa57ae5 and the ordinary
non-force push succeeded: `726ea9af9d..09eaa57ae5 HEAD -> main`.
The current-closure plan now pins the post-race source snapshot. This
addendum reports the actual successful push; it does not upgrade either
upstream-reported builds or old cached objects to fresh local validation.
