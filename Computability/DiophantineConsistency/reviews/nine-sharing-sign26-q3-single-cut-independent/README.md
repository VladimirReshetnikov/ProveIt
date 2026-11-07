# Independent restricted q3 single-cut survey audit

The independent checker pins the 26-witness AST and evaluates every selected
literal substitution directly in the reduced polynomial ring, reducing
`A³` to `Q−3A²−3A−1` after each multiplication. It uses fixed-length exponent
tuples, weights A and witness variables by one and ports by zero, and leaves
the q3 equation itself unreduced at formal degree 3. The resulting maxima
and rows for all ten selected cuts exactly match the retained survey. The
checker exited 0 under `python3 -I -S -B`; checker SHA-256
`ac4707228a92abda72b7b7cef86d16f84fde394112822cf3e3cb30f7ba93b108`,
result SHA-256
`674dde0c9bf7f637a0a8288737ff974f9472c15321ee7b0f0ec14e553f4634e4`.

The conclusion is restricted to those direct cuts and that specified formal
remainder, with A independent of v1 and ports. It is not a semantic lower
bound or an obstruction to a different identity, change of variables or
encoding, and it proves no Lean result.
