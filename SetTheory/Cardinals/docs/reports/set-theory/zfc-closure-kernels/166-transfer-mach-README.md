# Verified 215 state implementation

transfer215.native.tm and transfer215.tm are the same calibrated machine under
canonicalization.json. There are 215 working states, plus a separate halt label.
Canonical labels are working states 0 through 214 and halt 215. Native labels
retain the construction labels, with start 0, dispatcher 84 and halt 254.

These files are not a 214-state solution. The source has 201 DAG nodes, a different
quantity from the machine's working-state count.
