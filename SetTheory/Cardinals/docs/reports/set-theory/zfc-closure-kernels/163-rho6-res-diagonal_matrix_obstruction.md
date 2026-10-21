# Why setting the fourth parameter equal to the first cannot work

Consider the current native numerical calculus with all its retained rows,
generalization, truth, modus ponens, and the full set-theoretic bundle, but
replace the dominated fourth-parameter row by

\[
  ((C\to A)\to A)\to((A\to C)\to(B\to C)).
\]

The repository's `k219-fourth-parameter` already rules out a broader family
containing this specialization. The contribution here is a smaller,
independently checked three-valued matrix, rather than a newly excluded
family.

This three-parameter specialization is **provably consistent in elementary
arithmetic**, including on the raw numerical codes. Consequently it cannot
give the required ZFC-provable consistency equivalence, assuming ZFC is
consistent. This rules out one especially inexpensive-looking reduction.

## Explicit matrix

The carrier is \(\{0,1,2\}\); the only designated value is \(2\).
Truth has value \(2\), falsity value \(0\). Rows are first arguments and
columns second arguments. The four binary constructors have these tables:

\[
I=\begin{pmatrix}1&2&2\\2&2&2\\1&1&2\end{pmatrix},\qquad
R=\begin{pmatrix}1&1&0\\1&0&0\\1&1&0\end{pmatrix},\qquad
E=\begin{pmatrix}0&0&0\\0&0&0\\0&0&0\end{pmatrix},\qquad
Q=\begin{pmatrix}1&1&2\\1&1&2\\1&1&2\end{pmatrix}.
\]

The independent checker `check_diagonal_matrix.py` builds symbolic formulas
for each generator, then exhaustively evaluates every assignment. It checks
the seven retained logical rows, the specialized eighth row, and the
**unrestricted** bundle; each evaluation gives the designated value. This
is stronger than checking the native gated bundle, since gates only remove
instances. It also checks all nine argument pairs for each inference rule.

## Raw-code soundness, including the zero alias

Let \(P\) be the Cantor pairing in the repository, and use the constructor
codes \(I(a,b)=4P(a,b)\), \(R(a,b)=4P(a,b)+1\),
\(Q(a,b)=4P(a,b)+2\), and \(E(a,b)=4P(a,b)+3\).
Define \(v(0)=2\). For every positive code, unpair its quotient by four
and evaluate the corresponding table on the two recursively evaluated
arguments. Both arguments are smaller than the positive code, so this is
a well-founded, primitive-recursive definition.

The single exceptional constructor alias is \(I(0,0)=0\). It is respected
because the matrix satisfies \(I(2,2)=2\). Likewise the designated
falsity code \(1=R(0,0)\) receives value \(R(2,2)=0\), which is not
designated. Thus all four constructor valuation identities hold on every
raw natural number; no unique well-formed parsing assumption is needed.

Modus ponens preserves designated values: the last row of \(I\) has its
only designated output in the final column. Generalization also preserves
designation, since every entry in the final column of \(Q\) is \(2\).
Each axiom is designated by the finite exhaustive check. Induction on a
finite native derivation therefore shows that every theorem has value
\(2\), whereas the falsity code has value \(0\). This proves consistency
of the specialized calculus in arithmetic and hence in ZFC.

If ZFC proved equivalence of this consistency statement with
\(\operatorname{Con}(\mathrm{ZFC})\), it would prove its own consistency.
Godel's second incompleteness theorem excludes this when ZFC is consistent.
The conclusion concerns exactly the specialization \(U=A\), retaining
the repository's other generators; it says nothing against a different
three-parameter family or a different encoding.

## Reproduction

Run `python3 check_diagonal_matrix.py`. The output is also saved as
`diagonal_matrix_check.json`. The independent checker does not use the
model-search executable or its score function. The model was found by
`model_diag.cpp`; its search log and original JSON are separate provenance
artifacts and are not needed to check the mathematical obstruction.
