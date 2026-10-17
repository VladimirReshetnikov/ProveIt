# A sufficient theorem for binary countdown acceleration

This is a sufficient certificate rule. Concrete replay results from this
investigation are reported separately in `binary_loop_audit.md`; the theorem
alone does not certify a mutation. It makes precise the proof needed to cross a repeatedly
executed binary control loop whose net primary effect depends on the entry
counter. A source-loop summary by itself cannot justify this rule.

## Complete-interface cycle hypotheses

Let `C(v,S,kappa)` denote a concrete binary configuration described by one
complete symbolic interface: exact working state, head, left tape, header,
PC, gap, blank exteriors, and a plain register box with primary vector
`v in N^9` and arbitrary finite spare suffix S. The tuple kappa contains
every other interface parameter. Each cycle below preserves kappa exactly.
Equality only of the binary state, decoded PC, or nine primary values is
insufficient.

Fix a primary counter r and a constant integer vector d such that d_r=-1
and d_i>=0 for every i different from r. Let J(v,kappa) be a natural-valued
cutpoint invariant. Suppose universally:

1. For every J-satisfying complete interface with v_r>0, an exact, finite,
   positive binary execution reaches
   `C(v+d, S ++ replicate(e,0), kappa)` for some finite e>=0, without an
   earlier halt. The run may be built from protected full-tape box contracts
   and exact literal/scan steps. Every intermediate box guard is proved
   under the current J and v_r>0, not only under one prepared input.
2. `J(v,kappa)` and v_r>0 imply `J(v+d,kappa)`. This includes the boundary
   v_r=1, whose successor has counter zero. Alternatively supply a separately
   named zero-boundary invariant and prove the transition to it.
3. For every J-satisfying complete interface with v_r=0 and arbitrary
   valid S, a separately checked finite zero-exit execution reaches its
   specified complete output frame, or the actual binary halt, in positive
   binary time. No earlier halt is allowed on an output that is live.

The cycle's e may be constant (a fixed number of positive box decrements)
or a proved finite function of the current data. The global relation needs
only a valid existential final spare suffix. If a stronger affine spare
count is reported, that count must be separately derived.

## Conclusion and proof

From initial `C(R,S,kappa)` with J(R,kappa), put n=R_r. After n complete
positive cycles, the interface has primary vector U where

`U_r=0`, and `U_i=R_i+n*d_i` for i different from r.

Its spare suffix is S followed by finitely many zero blocks. Its kappa is
unchanged, and J(U,kappa) holds. The independently proved zero exit then
supplies the stated final binary frame or halt.

Proof: induction on the remaining counter, or equivalently on the number
j<=n of completed cycles. After j cycles, the current primary vector is
`R+j*d`, so its counter is n-j. For j<n the counter is positive, the
inductive invariant supplies the next universally proved cycle, and its
whole-interface endpoint permits composition. Appending the finite zero
suffix preserves validity for every subsequent box. At j=n the zero-exit
premise applies. The concatenated run is finite; every constituent cycle
and the final exit have positive time. No sample-run bound, guessed cycle
period, or source-program equality substitutes for these hypotheses.

If the same composed matrix effect and complete endpoint are reached by an
exact source summary, the adaptive positive-source-block theorem in
`compositional_box_simulation.md` can compare the two. The source's final
spare history does not need to equal the binary spare history.

## Guard preservation is the principal trap

Suppose a first traversal used a zero decrement on register i. If d_i>0,
that same zero guard will normally fail on the next traversal, despite an
apparently repeated control state. A checker may not reuse the entry fact
`R_i=0` after a cycle that changed it. It must either strengthen/choose a
preserved J, verify every iteration using `R_i+j*d_i+prefix_delta_i`, or
reject the proposed cycle. Likewise, a test on the counter after it has
been decremented may distinguish the last cycle (initial counter one) from
earlier cycles; uniform positive-cycle semantics must account for that
distinction.

The binary control interface must be equally stable. A repeated decoder
state with a shifted head, changed PC or gap, leftover marker, extra finite
left-tape bit, or changed exterior is not the required cutpoint recurrence.
The source catalogue's zero positive-cycle gap growth does not establish
any of those binary equalities.

## Translation-equivariant variant

The sufficient theorem above fixes the absolute head as part of kappa.
There is also a useful more general version. Write the interface as
`C(v,S,h,kappa)`, where h is the absolute integer head and kappa records
the complete tape pattern **relative to that head**, the control state,
head-side flag, PC/header/gap geometry, and exterior conditions. Require
the cycle contract for every integer h, but allow its endpoint to be
`C(v+d,S',h',kappa)` for some integer h'. The same induction works: its
next instance uses the actual output witness h'. The zero-exit contract
must likewise be uniform in h. No formula for accumulated absolute head
displacement is needed for the halting comparison when the dispatch frame
relation already existentially quantifies its head.

Canonical symbolic left/right tapes in the trace diagnostic describe this
relative interface; they do not themselves record a separately tracked
absolute head coordinate. Equality of those canonical tapes, the state,
and the head-side flag is therefore appropriately reported as a complete
relative-interface recurrence, with the primary effect erased and the
valid spare suffix existential. It is not equality of two absolute
configurations or proof of a loop. The universal cycle and guard premises
are still required. Translation equivariance follows from the actual
Turing-machine transition rule and the arbitrary-integer-head hypotheses
of the protected box contracts.

## Scope

This rule enlarges an offset-only register ledger to a controlled
affine-matrix effect. It is a sufficient, deliberately narrow rule. It
does not certify a binary loop merely by detecting a repeated symbolic
shape. Exact cycle and zero-exit replays implementing the rule are audited
separately in `binary_loop_audit.md`. No surviving machine with fewer than
252 states is supplied. Every application must exhibit and check its own
exact binary cycle, preserved guards, zero exit, entry coverage and source
endpoint comparison.
