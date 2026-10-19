# Second ordinary review of the 946-bit packet

This is a human-readable ordinary mathematical review, not a Lean/Rocq
certificate or an internal PA proof. It rereads the current complete
`stack946_note.tex` against the preferred literal equations. No new finite
test is used as a substitute for the unbounded argument.

## Checks that pass

1. **All objects receive finite class interpretations.** The positive
   residues of the pairing constructors partition the nonzero external
   natural numbers. Each constructor argument is strictly smaller than
   its result. Class recursion therefore covers every object, including
   every descriptor code, rather than a bounded or well-formed subset.
2. **Both native equations are universal.** The selector index satisfies
   `idx(d)=0` and `idx(A(j,d))=1+idx(j)` for arbitrary `j`, including
   noncanonical selectors. Ordinary stream projection consequently
   validates head and tail on every `P(x,s)`.
3. **The shared constructor imposes compatible conditions.** Native
   projection reads a `P` code as a cons cell; incidence reads it as the
   NAND of its two class arguments. No equation says that `P` itself is
   a commutative Boolean operation. Identifying Boolean `N` with `P`
   would be invalid, and is explicitly excluded.
4. **Descriptors stay in the inherited schema's scope.** Every fixed
   class is a finite pure-membership formula in finitely many stream
   coordinates. Evaluating it on `P(y,P(x,b))` gives a pure-membership
   relation in `x,y` with finitely many parameters from fixed `b`.
   Neither external pairing nor the entire decoder is assumed internally
   definable in the possibly nonstandard ZFC model.
5. **The witness slice is actually unconstrained.** Class `d` is false
   on all streams. Thus `Q(d)` is also false, both sides of the chosen
   existential-witness equation are false at `a=d`, and the arbitrary
   candidate implication has false antecedent. Choosing `W(x,d)` to
   be a member of nonempty `x` does not conflict with existential
   witnesses at the other class codes.
6. **Booleanization preserves the native equations.** Transport a
   countably infinite Boolean algebra onto the already constructed
   carrier, arranging that its top is `d`. Retain every native and
   Skolem function literally. Only predicate-valued functions become
   top/bottom-valued. Object `d` being Boolean top is compatible with
   the distinct expression `p_eps(s,d)` being Boolean bottom.
7. **The lower direction is a literal interpretation.** Defining the
   removed symbols by `J=P`, `Pick(x)=W(x,d)` and `top=d` recovers the
   original equations and separating endpoints. The subsequent
   ultrafilter is applied only to predicate values; native functions
   are not quotiented. The original adequate EPSC kernel follows.
8. **The claim is the correct ground nonderivability statement.**
   Equational consistency alone is trivial because a one-element
   model exists. The target is separation of `N(d,d)` from `d`.
   Ground contextual completeness and the supplied fair certificate
   specification are appropriate for precisely that target.

## Remaining dependencies and boundaries

The raw EPSC/hereditary-saturation comparison with ZFC, the Sheffer Sh1
basis theorem and ordinary first-order/equational completeness remain
explicit mathematical dependencies. The upper model uses ordinary ZFC
completeness and a countable model; no transitivity or omega-standardness
is assumed. No proof assistant has checked the new full interpretation.

The 946 bits improve a complete equational packet. Source 42's 901 native
bits become 1,998 with explicit equality; its separate 917-bit native
variant becomes 1,703. Source 44's 881 bits are a template with external
signature and arities. None of those bit counts is a binary state count.
The main report's 239-state machine is a separate calibrated-machine
transformation, not a consequence of this equational packet.
