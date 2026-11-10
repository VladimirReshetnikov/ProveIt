# Independent review of the external sign21 normalized S substitution

`audit.py` checks the pinned sign22 and sign21 JSON bytes, the deleted row
`v21 - (v6+1)*v17*(v17+2)`, the 12 remaining rows after substitution and
renumbering, the fixed coordinate, ports and coefficient binding. It verifies
compressed and raw port hashes and referenced certificate and proof hashes.
The substituted expression is natural on natural inputs; the reverse follows
algebraically from the removed row. Neither is a Lean model theorem here.

Each residual has syntactic degree at most seven. With v6=v17=v21=t, input
one and other coordinates zero, the audit calculates Na exactly as
`-t^7-6t^6-13t^5-12t^4-4t^3`. At fixed integer ports, the t^14 coefficient of
the sum of squares is a sum of squares of leading coefficients and is at
least one from Na. The fixed-input external polynomial thus has exact degree
fourteen.

`python3 -I -S -B audit.py` exited 0; the output is `result.json`. This
does not establish JSON-to-Lean binding, sign21→22 or later model bridges,
an iPRA endpoint, or a Jones reduction. This is an external candidate and
not yet an established Con(ZFC) equation.
