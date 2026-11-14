# First-four positive-selected marker through its finite file

`PA194FirstFourPositiveFile.markerFirstFourPositiveFile` proves that the
first non-first marker entry, with first physical value four and a positive
selected value, reaches dense state 2 after scanning the selected unary run
and every block of the remaining fixed-length encoded file. The output left
half is the explicit `PA194PrefixFile.leftCode` result and the right half is
the final file tail. The number of file blocks is a fixed Lean natural, while
register contents and execution time may be nonstandard model values.

`PA194FirstFourPositiveBlankTo7.markerFirstFourPositiveBlankTo7` adds the
assumption that the final tail is blank. It composes the state-2 and state-0
exits, state-1 carry entry and checked blank-tail path to dense state 7, with
both final packed halves exact.

Both results assume the stated marker and file layout. They do not establish
blank-tape reachability, return from dense 7 to the source root, source-frame
correspondence, or a literal-machine iPRA consistency implication.

The two modules passed ordered suffix checks against the retained first-four
marker entry and separately checked scanner/controller prerequisites, without
`sorryAx`. `check-first-four-positive-blank-to7.sh` specifies a full nested
rebuild but has not been run.
