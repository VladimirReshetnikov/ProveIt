# First-four positive-selected blank-tail file return

`PA194FirstFourPositiveReturn.markerFirstFourPositiveBlankReturn` extends the
first-four positive-selected marker path from dense 7 back across every block
of the fixed-length encoded file. It states both returned tape halves exactly,
using the existing primitive-recursive return-file code; register values and
execution times may be nonstandard in any candidate-PRA model.

The proof recognizes the additional blank-tail delimiter as a one-cell prefix,
uses the existing single-cell prefix return, and then composes the general
prefix-file return. It assumes the stated marker/file layout and a blank final
tail. The subsequent selected-block return, dense-24 endpoint, source-frame
correspondence, blank-tape reachability, and literal-machine iPRA implications
remain open.

The module passed a suffix replay against separately checked positive-file and
blank-tail prerequisites and retained deeper controller objects, without
`sorryAx`. `check-first-four-positive-return.sh` specifies the full nested
rebuild but has not been run.
