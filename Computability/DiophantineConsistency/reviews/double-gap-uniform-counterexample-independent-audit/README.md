# Independent symbolic auxiliary-port obstruction review

The independent review actually exited 0; its receipt SHA-256 is
`64e89a3c0c7c2dc587bd4555481f8b4d49026376049d630921e46938f1d92de7`.
It independently evaluates both complete pinned source graphs using sparse
rational polynomials, checks the coordinate-change identities with independent
symbols, and expands the small auxiliary Pell polynomial identity exactly.
The original checker was separately rerun successfully; both checkers reject
optimized Python. An initial independent review fixed one coordinate symbol to
3; its receipt is retained, and the final review makes that coordinate an
independent variable and reruns all checks.

The large algebraic power is deliberately **not expanded**. Its mathematical
justification is as follows. Set `(s,c)=(13837575261124,3572846569215)`, the
coefficients of `(4+sqrt(15))^15`. Exact arithmetic gives `s²−15c²=1`.
Define `(f,B)` by `(f+B sqrt(15))=(s+c sqrt(15))^c`. Both coefficients are
positive integers and norm multiplicativity gives `f²−15B²=1`. In the odd
binomial terms for `B`, the first has factor `c²`, while every later term has
at least three factors of `c`; hence `c² | B` without expanding the power.
Consequently `i=15B/c²` is a positive integer, `I=c²i=15B`, and
`I²=15(f²−1)`.

For `t=I²`, exact sparse polynomial arithmetic checks
`t v₇(t)²−(t−1) w₇(t)²=1` and `v₇(-15)=-c`. Polynomial remainder then gives
`15f²=t+15 | v₇(t)+c`, so `P=(v₇(t)+c)/f²` is an integer. Since `I≥15`,
`t≥225`; the displayed recurrences imply `v_j≥t v_(j−1)>0` and
`w_j≥t w_(j−1)>0` by induction. Thus `v₇≥t⁷`, `f²≤t`, and
`P≥t⁶>c`. The stated `R0` is a separately checked positive integer, making
the constructed `gamma=P−c+R0` positive. All 13 rewritten coordinates are
therefore positive. The specific inverse has `q=1`, `h=2`, and `F=q−h=-1`.

The full-graph evaluator independently verifies that, under this substitution,
the first two residuals vanish, the strong residual is `I²−15(f²−1)`, and
the auxiliary residual is the displayed Pell expression. Both the four-square
and product-minus-one outputs therefore vanish after applying the two verified
local coordinate identities. This is a counterexample to a reverse positive
transport uniform over the indicated auxiliary integer ports, including
`beta=0`, `K0=-2`, and a specially chosen negative `MC`.

It is **not** a counterexample for the actual fixed ports, a verified smaller
equation, a Lean formalization, or a proof of consistency or inconsistency.
The enormous power is justified symbolically, rather than computed or printed.
