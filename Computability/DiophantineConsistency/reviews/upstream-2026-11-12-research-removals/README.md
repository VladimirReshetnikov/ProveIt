# Upstream research-file removals and reproducibility

The merge of `origin/main` at `6be4878bc5` incorporated commit
`8963da8dfc`, which removed 48 tracked files under this directory's
DiophantineConsistency research and reviews tree. The removals cover parts
of the AQ20 substituted-scales graph and display, AQ22 quotient sources and
display, AQ26 quotient sources, and their related reviews. The files remain
available in Git history; this note does not restore or alter the upstream
change.

Two remaining checks were run after the merge and currently stop on missing
upstream files:

* `research/adaptive-aq20-factored-root103/check.py` cannot read its pinned
  `research/adaptive-aq20-substituted-scales104/candidate.json`.
* `research/generated-residual-vector-arity-audit/check.py` cannot read its
  pinned `research/adaptive-aq26-quotient122-model-draft/AQ26Quotient122Residuals.lean.src`.

These are reproducibility failures due to absent inputs, not mathematical
counterexamples or Lean failures. Other checks depending on the removed
files may also be affected; no exhaustive impact audit is claimed. The
current14 coherent-plan line-count check and the recent eta-85 conditional
composition and positive-81 exact-main review receipts still reproduced
after the merge. That narrow observation does not verify their theorem or
provider claims.

The removed paths and their previous bytes can be inspected read-only with
`git diff --name-status <merge>^1 <merge> --
Computability/DiophantineConsistency` and `git show <merge>^1:<path>`, where
the merge is `ee5aed719f`. Restoring files would reverse the upstream
deletions and is not done by this note.
