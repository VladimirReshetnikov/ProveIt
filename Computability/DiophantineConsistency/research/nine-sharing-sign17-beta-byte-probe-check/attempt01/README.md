# Symbolic beta byte-pattern probe: partial failure

Author-observed outer session `97508` exited 1. The fifteen prior stages
passed. The final probe's general repunit declaration reports standard axioms,
but the beta-pattern and current-port declarations fail due to exponent
rewrite order, a recursion-depth failure and an unintended integer-valued
`ofDigits` elaboration; both report `sorryAx`. The final object and postflight
are absent. No Lean beta-pattern theorem is claimed. Independent terminal
review is pending.
