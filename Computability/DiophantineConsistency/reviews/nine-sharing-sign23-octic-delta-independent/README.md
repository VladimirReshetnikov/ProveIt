# Independent review of the external sign23 Delta substitution

`audit.py` independently checks the pinned sign24 and sign23 JSON bytes, the
deleted row `v18 - ((v16+v15)^2 + 4*(v16+v15) + 3)`, all 14 remaining
rows and their fields after substitution and renumbering, the fixed coordinate,
port list, and coefficient binding. It verifies all compressed and raw port
hashes, plus the certificate and proof hashes. The substituted polynomial is
natural for natural inputs; recovering the removed coordinate from a zero is
an external algebraic observation here, not a Lean model theorem.

Each row has syntactic degree at most four. With v16=v17=t and all other
coordinates zero, the audit computes N0 exactly as `-t^4-2t^2-1`. Every
specialized row has degree at most four. For fixed integer ports, the t^8
coefficient of their sum of squares is a sum of squares of integer leading
coefficients and is at least one from N0. Hence the external polynomial has
exact total degree eight, without requiring the other rows' t^8 contributions
to vanish.

`python3 -I -S -B audit.py` exited 0; its output is `result.json`. This does
not establish JSON-to-Lean semantics, the sign23→24 or sign24→25 model
bridges, an iPRA endpoint, or any nine-variable Jones reduction. Port hashes
identify bytes; they do not prove the ports' Lean or PDF interpretation.
