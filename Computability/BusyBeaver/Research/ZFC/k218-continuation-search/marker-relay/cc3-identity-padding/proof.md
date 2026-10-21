# Exact open contract of the neutral insertions

Registers are arbitrary natural numbers. The source pair `(L,R)` enters R
when L returns normally; a break1 from L exits the pair normally, and a
higher left break loses one level. Left continues pass unchanged. A
continue1 from R restarts the pair; a higher right continue loses one
level. Right breaks pass unchanged. These are the inherited source rules.

`N_r=(CI_r,CD_r)` always terminates normally after two primitive actions.
The increment makes r positive, so its following decrement takes the
positive branch and restores the exact old value. Every other register is
unchanged. This includes r=6 and input value0. It does not rely on a finite
test or a scratch-register assumption.

The old `P=(CD6,CC2)` has exactly two outcomes. If register6 is0, its zero
decrement exits normally without modifying any register. If it is positive,
the decrement subtracts1 and CC2 in the right child returns continue1.

For `P_left=(N_r,(CD6,CC3))`, N_r first restores the input vector. At zero6,
CD6 exits its pair normally, and the outer pair also returns normally. At
positive6, CC3 crosses the right edge of `(CD6,CC3)`, becoming continue2,
then the outer right edge, becoming continue1. Register6 has decreased
exactly once and all other registers retain their inputs.

For `P_right=(CD6,(N_r,CC3))`, zero6 exits the entire pair before N_r.
At positive6 the decrement occurs first, and N_r restores that post-decrement
vector. CC3 again crosses exactly two right edges and returns continue1.
Thus this form has the same two outcomes, including when r=6 and the old
register6 was1.

All three blocks terminate after a positive finite number of primitive
steps and have identical complete-vector and open-exit contracts. Replacing
any occurrence in any source context therefore preserves terminating exits,
halting and divergence, with a finite stuttering correspondence. Replacing
all nine occurrences is valid simultaneously; the replacement does not
contain another old P. No assumption about the proof-search seed is needed.

The independent source measurements preserve a map from every original
primitive ordinal to its retained copy. They compare all primitive effects
and every control target after contracting only the added increment and
its necessarily positive matching decrement. The unused zero branch of that
added decrement is excluded by the immediately preceding increment, not
silently equated to an original edge.

The separate comparator-only register swap conjugates each entire proved
clean equality macro by the permutation5↔6. Equality is symmetric; both
output counters are cleared; other registers and the normal-versus-break1
exit agree. This proves that source option, while its initial CD6/CC2 block
outside the comparator remains unchanged.

These source arguments do not supply a generic right-CC3 engine entry,
justify any newly generated decoder action, or establish the startup or
arithmetic runtime of the relay217 table. The allocator stops before those
questions can be checked.
