# Independent source/emitter checks

Run from any directory, with Python 3.10 or newer and assertions enabled:

    python3 -B check_combined_emitter.py --source PATH_TO_REBUILT_SITES_JSON --output RECEIPT_JSON
    python3 -B check_emitter_negative_controls.py --source PATH_TO_REBUILT_SITES_JSON --output-dir EMPTY_DIRECTORY

Both programs locate their immutable inputs relative to this directory. The
source-language module is in the parent directory, baseline source and seed
grammar are in `../inputs`, and macro data plus pinned Dag230 are local.
No network or earlier workspace is used. All inputs are read-only.

The emitter checker does not import `build222.py`, the source optimizer, or
its recipe. It writes the expected native G and seed-without-H formulas
independently, converts them to postfix constructor words, verifies exact
symbolic stack effects, and relates optimized arithmetic macros to pinned
upstream macros by finite all-register bisimulations. It verifies the complete
primitive word has exactly two declared replacements, makes its own closed
splice reference, and compares every guarded target through two independent
complete source CFG resolvers. Candidate hashes are reported, not assumed.

The six negative controls change an unaffected instruction, a G instruction,
a seed-bundle instruction, the G binder's R constructor to Q, restore the
unwanted H subexpression, and re-associate a nonclosed block without changing
primitive order. All six must fail semantic source or CFG checks. The last
control specifically demonstrates that primitive equality alone is insufficient.

These are executable ordinary mathematical certificates of source binding.
They do not replace the theory proof, exact blank bootstrap, or unbounded
binary-runtime certificate, and do not claim a new proof-assistant endpoint.
