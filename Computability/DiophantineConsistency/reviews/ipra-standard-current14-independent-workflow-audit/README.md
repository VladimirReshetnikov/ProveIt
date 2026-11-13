# Independent historical current-14 workflow review

The paired workflow was reviewed at commit `0315f0f3ec`. Its source pins,
historical-parent boundary, complete sibling seed checks, observed-process
gates and four diagnostic policy agree with the documented procedure. The
workflow still requires the independently observed original parent pair and
the separate parent audit, a stable HEAD during preparation, and an independent
validation after any real paired run.

`launch-historical-pair.sh` is the runbook's exact shell block with the three
parent observation and pair-state pins filled from recorded evidence. Its
SHA-256 is `bfdc5454eb257dfee69b8c749bae423df2b752e8ed0a1aea2a4eba7f122e4c11`.
It passed `bash -n`; the three pinned evidence files and unused run-01 output
path were verified when this review was written. Run it from the repository
root after coordinating a stable-HEAD window through the preparation gate.
Capture its actual outer exit and complete stdout; never overwrite a failed run.

In an isolated copy, `run_controls.py` actually exited 0. All five ordinary
control programs passed, including real Lean paired toy and full-chain tests;
all five optimized-Python negative controls were rejected as intended. The
detached receipt records their separate output and source hashes. The copied
inputs were checked byte-for-byte against the workspace after the run, and
additional workflow and parent-tool inputs are listed in `receipt.json`.

`check_policy.py` independently checked the 16 ordered sources against the
author manifest and logged author rows, the four endpoint `#print axioms`
names against policy and recorded logs, and the permitted Lean axiom names.
It also rejected separately mutated report coverage, module order, and author
log hashes. The check actually exited 0. It reports source/log agreement only;
Lean's `Classical.choice` in metatheoretic axiom reports does not by itself
assert that the object theory has classical logic.

This is a policy and toy-workflow audit. It is not an original-14 paired proof,
a fresh current-source replay, or an audit of inherited package-transitive,
dynamic, or temporary-mutation ancestry. The Foundation build wrapper's outer
exit remains unobserved, although its inner Lake exit and the separate provider
verifier's exit were recorded as zero.
