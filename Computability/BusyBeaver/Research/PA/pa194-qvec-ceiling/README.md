# A fixed ceiling for arithmetic qVec traces

In every IΣ₁ arithmetic model, `bounded_trace_explicit` constructs a coded
sequence of the actual arithmetic-language (`ℒₒᵣ`) `qVec` iterates through any
model-internal length. It gives the seed, each successor equation, and a
single bound `iter limit seed` for every entry up to that length, including
nonstandard indices. The bound is the monotone arithmetic tower iterator
already established in the PA196 witness-bound research.

This is a prerequisite for a fixed-ceiling induction on formula substitution,
whose quantified branches repeatedly lift the term vector. It does not bound
the separate formula/substitution graph witnesses, identify the unported
arithmetic-to-PAeq interpretation, or prove the substitution agreement. It
concerns the arithmetic source language, not the PA194 relational language.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-qvec-ceiling/check.sh
```

The final module passed a fresh suffix check using retained PA196 qVec
prerequisites and the audited project and Foundation overlays. Its printed
axioms contain no `sorryAx`. The script rebuilds the prerequisite prefix up to
tower algebra; this full prefix replay remains pending.

An independent suffix replay rebuilt the ceiling module against the retained
PA196 qVec prerequisites and audited project/Foundation overlays. It passed
without `sorryAx`; this did not rebuild the full prerequisite prefix.
