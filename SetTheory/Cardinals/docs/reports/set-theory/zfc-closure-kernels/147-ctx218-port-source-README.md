# Independent source proof

The unchanged `reconstruct_source.py` uses four files in its own directory.
The main portable driver copies this script and `dag_recipe.json` to a fresh
external source directory, supplies `baseline_sites219.json` from the verified
upstream packet and `candidate_sites218.json` from the released machine source,
then runs the checker there. It compares the reconstructed final source against
the independently reconstructed full table lineage.

This avoids modifying the release and avoids duplicating source files here.
The reproduction section in `PROOF.md` describes the resulting four-input
working directory. Use the top-level portable driver for the complete task.
