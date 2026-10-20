# Independent consequence of the supplied five-value matrix

The unchanged supplement states its theorem only for `rho8(A,B,C,R(A,B))`. Its proof also gives the following strictly broader ordinary result, without a new search or a substitution principle:

> Retain native truth, MP, GEN, rho1–rho6, merged G and the gated literal C222 bundle. Allow any collection of rho8 instances whose fourth argument is a membership code `R(i,j)`, with i and j arbitrary functions or relations of the other parameters. This enlarged calculus is PA-provably consistent. In particular, the union of all six ordered distinct-input membership orientations is covered simultaneously.

Use exactly the supplement's carrier `{0,1,2,3,4}`, designated values `{3,4}`, truth4, falsity2, constant equality3, implication J and uniform quantifier q. Native membership codes all receive2, regardless of their labels. Thus every newly allowed row has value `L_J(a,b,c,2)`. No formula substitution or label renaming is used, and correlations between code values and labels can only restrict the cases below.

For transparency, the finite facts can be checked directly from the displayed table as follows. Native negation `N(x)=J(x,2)` is `(3,3,4,1,0)`, and q is `(1,1,1,4,4)`. The designated antecedent rows3 and4 have designated outputs only at designated consequents; q maps both designated values to4. Also J(4,4)=4 handles the native `I(0,0)=0` alias. Therefore MP, GEN and truth are sound.

For the restricted rho8 put `X=J(N(c),a)` and `Y=J(J(a,c),J(b,c))`. The output is `J(X,Y)`. The table never outputs2, and a second application to two outputs yields `Y` in `{1,4}`. Output4 for Y=4 is immediate. If Y=1:

| c | Necessary condition when Y=1 | Consequent value of X |
|---|---|---|
|0|a=0|1|
|1|a is 0,1,or2|1|
|2|a is not4|0 or1|
|3|a is0 or3|1|
|4|impossible|—|

Both J(0,1) and J(1,1) are4. Hence every restricted row has value4.

The remaining rows can be reduced without enumerating natural codes. Rho1 has value `N(q(N(3)))=3`. Rho3 and rho5 have value `J(3,J(2,2))=4`; G has value `J(3,J(3,q(3)))=4`. Rho4 has identical sides and every diagonal of J is4. For rho2, `J(q(b),q(c))` is1 only when b is designated and c is not; MP preservation then makes `q(J(b,c))=1`, so the outer J is again4. Rho6 has values `(4,4,3,4,4)` as its formula parameter ranges over the carrier.

The exact bundle keeps both repeated quantifiers in clos. Direct evaluation gives `Sub=4`, `req(m)=(4,1,1,1,1)`, `clos(m)=1` for every m, `nks(m)=1`, and `vrel=4`. Thus `bundle=N(J(4,1))=3`, even without the numerical gate. These are evaluations of the literal req/clos/nks expressions, not classical equivalents.

Finally construct the valuation of every natural code by course-of-values recursion on the positive constructor code, setting v(0)=4. Pairing arguments are smaller than every positive enclosing code; the sole zero alias satisfies its equation. This is primitive recursive and PA proves the constructor equations. Induction on each finite derivation now keeps every theorem designated and excludes native falsum1, whose value is2. The same proof permits adding equality code3 and every identity. It does not permit adding K or EFQ: the supplement gives actual reachable-code counterexamples.

This is an ordinary written extension of the supplied certificate, not a new Lean/Rocq result or a fresh execution of its checker. It strengthens the maintained six *separate* orientation obstructions, while agreeing with them. It says nothing about replacing the fourth input by arbitrary non-membership formulas, adding stronger propositional axioms, or the calibrated K/S plus quantified-stability proposal. No machine state count follows.
