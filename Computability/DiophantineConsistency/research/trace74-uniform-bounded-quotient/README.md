# Bounded quotient obstruction with a variable Pell parameter

`Trace74UniformBoundedQuotient.impossible_of_bounded_quotient` proves the
reduced projection equation is impossible in a discretely ordered ring if
`h,y,L,j` are positive, `j<y`, and `Lh<y`. The reduced numerator is
`h(4y−1)(4(4L+1)y−1)((4L−1)y−L)` and the divisor is `4y(x+1)−1`.

The proof uses the congruence `j≡Lh (mod y)`, the stated bounds to force
`j=Lh`, and a second polynomial identity to derive `4y | y`, which
contradicts positivity and discreteness. The parameter `L` is arbitrary; it
need not be a standard numeral or an exponential. This theorem assumes a
bounded quotient and does not derive it from a graph zero or a size bound,
prove a reverse guard, or establish an iPRA endpoint.

Lean 4.32.0 was run with `/tmp:` prepended to the `lean_path` field in
[`trace74-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as `--root`,
and output `/tmp/Trace74UniformBoundedQuotient.olean`. Actual session 88921
exited 0 and reported only `[propext, Classical.choice, Quot.sound]`.
Earlier attempts failed on the sign of a polynomial witness and its
`linear_combination` coefficient.

```text
Trace74UniformBoundedQuotient.lean  0ee6c260164fa83ca0605f89cda4d535f57bbbe363539f300fccddcf1405d66d
Trace74UniformBoundedQuotient.olean e217b2d6913b1056bc8b4257e31bf9727e2da3984813dfa355f448598f811708
Trace74UniformHeightContradiction.olean c994954d496b9bc17f1354d28342699e2b0e02bd91eac3f0c3333421143c159e
```

This is an author check against temporary captured providers, not an
independent replay or coherent current-source build. Full transitive and
package ancestry and search-path selection remain unauthenticated.
