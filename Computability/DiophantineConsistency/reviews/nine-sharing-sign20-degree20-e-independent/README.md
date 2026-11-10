# Independent review of the external sign20 E substitution

`audit.py` checks pinned sign21 and sign20 AST bytes, the removed E row and
its natural product substitution, all 11 remaining rows after renumbering,
the input coordinate, ports, and coefficient binding. It checks the compressed
and raw coefficient hashes and the referenced certificate and proof hashes.
The retained beta bytes decode as a positive unsigned big-endian integer.

Each residual has syntactic total degree at most ten. For input one,
v1=v9=v11=v15=t and all other coordinates zero, the audit computes the N0
coefficient of t^10 symbolically in `Z[t,beta]` as `-beta^2`. At fixed integer
ports and nonzero beta, the t^20 coefficient of the sum of squares is a sum
of integer squares and is at least beta^4. The external fixed-input polynomial
therefore has exact degree twenty under that condition.

`python3 -I -S -B audit.py` exited 0 and its output is `result.json`. These
checks do not prove the beta bytes represent the Lean port, JSON-to-Lean
semantics, the sign20→21 model bridge, an iPRA endpoint, or a Jones reduction.
This is an external candidate, not yet an established Con(ZFC) equation.
