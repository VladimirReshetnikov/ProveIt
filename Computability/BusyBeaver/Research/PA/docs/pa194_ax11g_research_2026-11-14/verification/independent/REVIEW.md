# Independent review of AX11G

The reviewed literal table has dense SHA-256
`7e1c6442816e5df05e961f2057719252a1976c9a195a786978bf1e2d3c8e466d`.
This review concerns the new construction and its relative preservation
argument. It does not certify an unconditional primary-machine calibration
to PA consistency.

## Construction and physical checks

The table has 194 working controls, 388 transitions, dense start 0, and
separate halt label 194. Its native table is conjugate under the supplied
label bijection, with start 74 and halt 254. All working controls are
reachable in the directed transition graph.

An independently reconstructed source-tree comparison confirms that the
only change from the PA194G source is its terminal AX leaf at address
`10101001111`. Old source site 3553, a jump to old site 3641, is replaced
by the 19-site Push interval `[3553,3572)`. All retained primitive
instructions and their successors agree under relocation. The inserted
Push has one exit, from site 3569 to site 3572, which begins the complete
MP parameter reader. This establishes the reason for the fourth AX
operand; treating this command as a three-operand AX would be incorrect.

The full independent literal replay passes every one of the 4,779 source
outcomes, rederives all four list-sweep lemmas from the candidate rows,
checks the complete 58,154-step blank startup, and obtains strictly positive
physical durations. It imports no construction compiler or arithmetic-box
oracle. The retained certificates and their exact digests are under
`recorded/`.

The union of the literal rows used by the symbolic source contracts and
the complete startup is all 388 rows. This does not claim that all rows
occur on the single blank computation; it shows that the difference is not
padding with a control unused throughout these certified execution families.

## Command and mathematical review

The four-operand AX command has the stated effect: it adds eleven stack
entries, leaves visible top and cache zero, and places its fourth operand
`z` in the offset. The fallthrough MP comparison succeeds at `z=0` and
fails for `z>0`, but both branches leave the visible theorem zero.

The potentially delicate stack identities are valid, including Cantor's
zero-pair alias. Pop remains total even with visible contradiction code 1,
because the saved universal has code at least two at the relevant sum test.
The reserved zero in the MP compiler handles an antecedent equal to 1 by
an earlier halt and a consequent equal to 1 by returning it safely before
the final halt command. AX's explicit binder gives the generalization
word with eleven final shifts and no offset-setting command.

The bounded-store induction addresses the unbounded all-store quantifier
that cannot simply be placed inside iPRA's quantifier-free induction rule.
The reviewed version defines leaves to have height one and makes the
successor-stage input bounds explicit. The finite word evaluator and
bounded conjunction of its correctness conditions are primitive recursive.
The cofinal scheduler prefix is valid with the corrected four-field
continuation encoding.

No substantive flaw was found in the resulting relative command/compiler
argument. The literal symbolic certificates and their positive-duration
composition support an ordinary computer-assisted iPRA preservation proof.
They are not a new proof-assistant endpoint. The separate uniform
PA-refutation-to-numerical-calculus calibration remains an additional
premise for the absolute consistency statement.

## Structural novelty

The independent comparison finds no match to any of the 94 prior spanning
194-control graph classes, even after arbitrary state renaming, every
spanning start, reflection, global symbol exchange, and ignored final halt
actions. Exact full canonical tuples were compared. The accompanying
comparison replay also finds no nontrivial ordinary control quotient of
any of those 94 tables or of AX11G.
