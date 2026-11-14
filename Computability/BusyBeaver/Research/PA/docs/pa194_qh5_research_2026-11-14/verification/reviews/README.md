# Scoped reviews

These reviews are supplementary critical readings by separate research agents,
not external peer review or kernel proof checks. Each states its own scope.
The complete physical acceptance evidence remains in `../acceptance.json`
and `../../machine/independent/`.

The stale proof filename reported in `source_review.txt` was corrected in
`proof/check_commands.py` before release. This changed only a docstring.

The second review identified a missing retained copy of
`RestrictedImplication.lean`. The exact committed upstream file was added
under `references/logical/`, with its source, license, and SHA-256 included
in the provenance and input manifest. The final byte-integrity receipt
checks all 28 inherited inputs; the prior integration replay checked the
27 files present when that replay ran.
