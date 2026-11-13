# A bounded certificate invariant for the PA196 stack

The PA196 numeric stack uses the Cantor encoding `pair(0,0) = 0`. Thus a
zero formula pushed onto an empty numeric stack is indistinguishable from an
empty stack. A reverse proof-transport argument can handle this alias with a
parallel certificate stack whose entries beyond numeric underflow are ignored.
The observation below is a mathematical lemma about the encoding; it does
not establish the PA196 reverse consistency implication.

Let `decode` be the inverse of `pair`, with `decode(0) = (0,0)`, and let
`walk(x,i)` apply the second component of `decode` to `x`, `i` times. For a
numeric stack `w`, a certificate stack `p`, and a relation `Cert(proof,formula)`,
define `Good(w,p)` to mean that, for every `i`, whenever `walk(w,i) != 0`,
the first component of `decode(walk(p,i))` certifies the first component of
`decode(walk(w,i))`. In particular, `Good(0,p)` holds for every `p`: once the
numeric stack is zero it remains zero, and all later certificate entries are
ghosts.

Suppose `Good(w,p)` and `Cert(q,a)`. Then
`Good(pair(a,w),pair(q,p))`: at index zero the two decoded heads are `a` and
`q`; at every later index the decoded tails are the original stacks, so the
old invariant applies. When `pair(a,w) = 0`, the new invariant is vacuous;
no assumption about the ghost certificate stack is needed.

For a pop, if `w != 0`, return the head of `p` and advance both stacks to their
decoded tails. The invariant at index zero certifies the returned numeric head,
and the remaining obligations follow by shifting the old index by one. If
`w = 0`, return a fixed certificate of formula zero and leave `p` unchanged.
The numeric decoder returns head and tail zero, and `Good(0,p)` still holds.
For example, a push of numeric zero onto numeric zero, paired with a ghost
certificate stack headed by 42, has numeric code zero and certificate code
`pair(42,0) = 903`; underflow returns the fixed truth certificate, not 42.

For the PA196 pairing `pair(a,b) = triangle(a+b) + b`, the second component of
`decode(w)` is strictly less than `w` whenever `w > 0`. Indeed, if
`w = pair(a,b) > 0`, then `a+b > 0`, so `triangle(a+b) > 0` and `b < w`.
Consequently `walk(w,i) = 0` for every `i >= w`, by induction. The apparently
unbounded `Good(w,p)` is therefore equivalent to checking the displayed
condition only for `i < w`. The exact pairing and decoder are defined in the
imported [Cantor source](../../jamesyc-upstream/pa196/M6/Source/Cantor.lean).

A PA-internal proof still needs a primitive-recursive checker proof predicate,
representations of bounded walking, pairing, and conditional pop in the chosen
arithmetic language, and proofs in PA of these preservation statements and
induction for arbitrary, including nonstandard, codes. It also needs
proof-producing updates for every command, a connection to PA196's actual
checker, translation of accepted derivations into PA proofs, and extraction of
an appropriate command run from an arbitrary model-length halting trace. None
of those end-to-end obligations is discharged by this lemma.
