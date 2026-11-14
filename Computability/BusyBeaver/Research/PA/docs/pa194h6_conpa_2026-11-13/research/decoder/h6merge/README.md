# Whole-source-contract row-choice mergers on PA194H6

`python3 replay.py` reruns 62,073 candidate contractions of the exact PA194H6
input table. No candidate passed all affected universal primitive source
contracts within the 1,024-step symbolic bound. The receipt is `result.json`.

Each pair merger chooses each surviving row from one of the two original
controls. The protected arithmetic-box rows cannot change. The imported
symbolic engine therefore retains its existing arithmetic-block assumptions.
This screen is stronger in source contexts but narrower in replacement
instructions than the companion arbitrary-action local search.

The implementation and symbolic runtime were adapted from the supplied
PA194HS packet, `search/verify_reductions.py` and `search/symbolic_runtime.py`.
The precise PA194H6 input bytes, source sites, and instructions are frozen
under `inputs/PA194H6`. The script checks every parent source contract before
using its observed controls to choose affected cases. Keep assertions enabled.

This failed bounded search is not a proof that no merger exists: replacements
outside its row-choice family, simulations beyond its fuel bound, or changes
to the source convention are not covered.
