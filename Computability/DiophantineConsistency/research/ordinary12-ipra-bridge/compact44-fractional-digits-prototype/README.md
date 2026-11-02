# Exploratory fractional radix digits

In every IΣ₁ model, `FractionalDigits.split_quotient` establishes a generic identity for positive d and t, expressing `(Y / d) % (d*t)` using the two adjacent radix-`d*t` quotients and remainders. `AdjacentDigits.adjacent` specializes this to arbitrary model values X and q and r < 67:

```text
(X / 2^(67*q+r)) % 2^67 =
  dig 67 X q / 2^r + (dig 67 X (q+1) % 2^r) * 2^(67-r).
```

The exponentials in the Lean source are internal model exponentials. No bound on q or finite standard-model argument is used. Author-only compiler sessions 50739 and 44653 actually exited 0, with no warnings or `sorryAx`; the named axiom reports are `propext`, `Classical.choice` and `Quot.sound`. A fresh symlink overlay was rooted in the graph-temporal/carry pair's author provider; `FractionalDigits` was rebuilt locally before the second module. This is exploratory evidence, not a paired replay or independent artifact audit.

This is a quotient identity. Its application to a cyclic bit rotation still needs the appropriate wrap/index equations and source-digit facts; it does not prove a clean predecessor or a graph-column theorem. For example, Boolean adjacent digits alone do not imply a strict half-radix bound: with r=1, lower digit 0 and upper digit 1 the displayed expression equals 2^66. No retained K binding or iPRA completion is claimed.
