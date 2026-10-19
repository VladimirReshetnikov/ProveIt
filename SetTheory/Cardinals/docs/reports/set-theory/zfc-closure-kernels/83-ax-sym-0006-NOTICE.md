# Attribution and scope of this auxiliary package

This is auxiliary research for Vladimir Reshetnikov's ProveIt repository.
It preserves original binary-machine labels and copies the small number of
prior checker/source files needed to reproduce the newly checked composition.
The source bytes and origins are pinned in `sources/import_manifest.json`.

Mira-Cult is credited with the compact calculus and original 254-state machine.
Jeff Ketchersid is credited with the verification and symbolic machinery.
Andrew James Wade is credited with the compiler framework. The public
253-state reduction is credited to mira-emmy. The ProveIt physical register
permutation, earlier prefix and pulse reductions, reassociation, and alternate
detector retain their respective prior attribution.

`vendor/code/` contains unchanged excerpts of the already supplied research
archives, except that the directory organization is reduced to the files
needed here. `code/verify_whole_frame.py` is adapted from the prior direct
symbolic replay with only imports and its command driver replaced; its
symbolic transition and individual-case routines are unchanged. The precise
prior file hash is stated in that source header.

The retained `sources/NOTICE.txt`, `sources/LICENSE.ProveIt`, and
`sources/README.upstream-attribution.md` are historical notices whose paths and
package-size descriptions refer to the original distributions. They do not
assert that those complete distributions are included in this auxiliary
package. Original license scope remains unchanged. No additional grant is
asserted for upstream files without an applicable upstream license.

This package establishes no result with fewer than 246 states, no new
initialization-time record, no state minimality theorem, no unconditional
nonhalting theorem, and no new exact-table Lean or PA endpoint. Its positive
result is compatibility of two previously supplied transformations, checked
on one explicit 246-state binary transition table.
