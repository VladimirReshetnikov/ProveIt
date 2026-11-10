# Independent review of the external sign22 kY substitution

`audit.py` checks the pinned sign23 and sign22 JSON bytes, the deleted row
`v17 - ((v11+1)+(v12+1))*v15`, all 13 remaining rows after substitution and
renumbering, the fixed coordinate, port list and coefficient binding. It
verifies the compressed and raw port hashes and the referenced certificate
and proof hashes. The substituted expression is natural on natural inputs;
the reverse implication follows algebraically from the removed row, but no
Lean model bridge follows from this review.

Each residual has syntactic total degree at most six. With v11=v15=v16=t,
input one and the other coordinates zero, the audit calculates N0 exactly as
`-t^6-4t^5-5t^4-4t^3-4t^2-1`. At fixed integer ports, the t^12 coefficient
of the sum of squares is a sum of squares of integer leading coefficients and
is at least one from N0. Thus the fixed-input external polynomial has exact
degree twelve.

`python3 -I -S -B audit.py` exited 0; its output is `result.json`. The
checked AST identities and hashes do not establish a Lean binding, the
sign22→23, sign23→24, or sign24→25 model bridges, an iPRA endpoint, or a
Jones reduction. In particular this is an external candidate and a
variable/degree tradeoff, not an established Con(ZFC) equation.
