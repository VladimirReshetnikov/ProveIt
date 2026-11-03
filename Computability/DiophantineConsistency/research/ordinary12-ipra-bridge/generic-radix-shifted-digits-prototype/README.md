# Generic repunit shift as a digit-list transformation

`RadixShiftedDigits.add_repunit` proves for any positive natural base `b`,
any list `tail` with `tail.length + 1 = k`, and any natural `a`:

```
(b^k − 1) + Nat.ofDigits b ((a+1)::tail)
  = Nat.ofDigits b ((a::tail) ++ [1]).
```

This identifies the carry-free representation of **one** added radix
repunit: decrement the positive low digit and append one high digit. It is
an equality of natural values; it makes no digit-range, file, MF or iPRA
claim. A future concrete specialization must establish that the symbolic
high-mask list starts in 4 and has length 8,807, then instantiate the
theorem with radix `2^67` and `a=3`.

The bounded author run `observations/attempt02` exited 0 in 1.721 seconds
without warnings or `sorryAx`; direct dependency and companion guards were
unchanged. Source SHA-256:
`3472a2a81af1c4aac5dfcf8aa530a075d2c6aeceb9e0658eda885c6fac203378`;
object SHA-256:
`b1b24a8da200084184f1e4331fbdfa9390ce1019a6f1c8e05649ba0b67046dac`.
Lean reports `[propext, Quot.sound]` as metatheory dependencies, not iPRA
axioms. Attempt01 failed because the empty-list term had not been simplified;
its exact source, warnings, error and receipt are retained. This is an
author-only package-backed check, not a paired replay or full transitive/
dynamic ancestry audit; guard checks are point-in-time.
