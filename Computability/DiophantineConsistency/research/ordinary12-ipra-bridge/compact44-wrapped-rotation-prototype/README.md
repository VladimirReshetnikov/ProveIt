# Exploratory wholly wrapped rotation digit

In any IΣ₁ model, `RotationWrapped.wrapped` proves that if `e = 67*k+67+u`, the 67-bit digit at k of `rot 1 L X e` equals `(X / 2^(L−e+67*k)) % 2^67`. The theorem uses internal truncated subtraction and does not require an X bound. `WrappedAdjacent.wrapped_adjacent` further assumes `L−e+67*k = 67*q+r` and `r<67` and expresses the result using the adjacent radix-67 source digits. All parameters and exponentials are model values.

The author-only compiler sessions 15201 and 14757 actually exited 0 without warnings or `sorryAx`; their named axiom reports use `propext`, `Classical.choice`, and `Quot.sound`. Session 9623 actually exited 1 on a rewrite mismatch; its exact source and diagnostic are preserved, and its `sorryAx` report proves nothing. The same fresh author overlay and local fractional/rotation sources from commits 5152fadc5e and ce88d22a4f were used. This is exploratory evidence, not a paired replay or independent artifact audit.

The case where a 67-bit output window straddles the rotation cut remains open. These explicit index assumptions have not been derived for the graph witnesses, and no strict half-radix bound, clean predecessor, graph-column, retained-K binding, or internal iPRA conclusion is claimed.
