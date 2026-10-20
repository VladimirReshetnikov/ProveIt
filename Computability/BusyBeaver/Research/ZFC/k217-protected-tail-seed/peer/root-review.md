# Independent root review of the protected-tail argument

I independently read the complete frozen `proof.md` (the version beginning
with the result for `np=0` or `np=1`) and the relevant definitions and block
interfaces in `Enum222.lean`. The following ordinary argument checks pass:

- The exact decoder gives suffix index `f(y)-1` for MP, DROP and NIP, and
  `f³(y)-1` for AX, only when the corresponding suffix pointer is positive.
  The scheduler preserves the working tuple between candidates.
- The second-coordinate sequence of Cantor unpairing is a concatenation of
  `[0,...,s]`. It therefore preserves nonnegative finite prefix sums. Its
  threefold use in the induction needs only `b(0),...,b(s-1)`, which precede
  the current diagonal. There is no induction on an unproved later prefix.
- The three initial diagonals and the stated within-word bounds suffice.
  For diagonal `s>=3`, the final bound `7s-17` is positive, and intermediate
  bounds before and after each of its three last command words are valid.
- Exact `cstep` pushes zero or nothing for MP, one theorem for DROP, and ten
  theorems for AX. The bundle gate does not suppress stack outputs. Each
  successful NIP must therefore encounter a nonempty newly pushed prefix.
  A halting NIP checks the already-derivable cache. The conceptual prefix
  remains legitimate when `P(0,0)=0`, by the exact unpairing identities.

The proof consequently establishes ordinary source-level soundness from an
arbitrary initial stack, with a theorem current formula and theorem cache,
`pl=0`, and `np` equal to zero or one. Its completeness paragraph relies on
the separately retained cofinal reset/block-compiler argument for arbitrary
initial tuples; the original `Enum222.complete` alone states the standard
initial-seed result and should not be cited as the whole generalization.

The observed ordinal-161 relay frame has cache **1**, so this theorem cannot
be applied there. Its application is after the complete AX suffix clears the
cache and returns a gated axiom as current formula. The ordinary inherited
suffix/source correspondence and a correct binary simulation are still
necessary. The current 217-state relay has a concrete runtime counterexample
at ordinal 4569. Neither this review nor the scheduler theorem certifies it.

This review used source reading and mathematical reasoning. It did not rerun
the schedule experiment, the source, a binary table, or Lean.
