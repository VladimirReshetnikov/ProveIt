# A restricted obstruction to replacing NIP by a fixed command macro

This is an ordinary mathematical observation about the existing command
semantics. It is not a lower bound on Turing-machine states, a general
impossibility of merging opcodes, or a claim about a redesigned primitive.

Use the pinned ProveIt command boundary `(T,S,d,H)` and Cantor pairing

\[
P(a,b)=\frac{(a+b)(a+b+1)}2+b.
\]

Allow a macro to be a fixed finite sequence of MP, DROP, and AX commands,
with fixed numerical operands. Use either the original MP semantics or the
cache-result variant. The macro is not permitted to inspect the numerical
stack directly, add a new primitive, or change the boundary semantics of
one of the permitted commands.

**Proposition.** No such macro has the effect of `NIP(0)` on every Safe
working state, even if the requested simulation is restricted to NIP's
nonhalting cases.

**Proof.** Say that two working states agree observably when their
`T,d,H` fields agree, with no condition on their stacks. MP preserves this
relation: its comparison and its result in those three fields depend only
on `T,d,H` and its fixed operand. DROP also preserves the relation, since
its new current formula is the cache and its only use of the old stack is
to push the old top. AX's generated formulas and new `d,H` also depend
only on these fields and the fixed operands; it pushes its generated
formulas and old current formula onto the old stack. Thus each permitted
command preserves observable agreement. Induction gives the same result
for every permitted finite macro.

Consider the initial states

\[
 s_0=(0,0,0,0),\qquad s_1=(0,3,0,0).
\]

Both are Safe. Formula0 is a theorem, and formula2 is
`All(0,0)`, derived by generalization from formula0. Since `3=P(2,0)`, the
second stack is a theorem2 followed by the zero theorem stream. The states
agree observably, so any permitted macro returns equal caches on them.
But `NIP(0)` returns cache0 on `s_0` and cache2 on `s_1`, and neither run
halts because the incoming cache is0. This is a contradiction. ∎

The internal pairing and unpairing operations used while implementing MP
do not invalidate the argument. Their net command-boundary stack effect
is already fixed: the original MP may push a zero, while cache-MP leaves
the stack unchanged. Neither loads a pre-existing stack entry into an
observable formula register.

A reduction that deletes the NIP opcode must therefore give some other
operation a new stack-reading effect, change the representation/interface,
or use a different proof-search construction. This observation does not
exclude any of those possibilities.

## Source attribution

The command semantics and code conventions are from
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum254.lean` and
`Code254.lean` in VladimirReshetnikov/ProveIt at commit
`43026ff42f0939f09b9e95495248cfadcad38e38`.
The cache-result MP semantics and its ordinary correctness argument are
specified in the companion `cache_mp_proof.md`.
