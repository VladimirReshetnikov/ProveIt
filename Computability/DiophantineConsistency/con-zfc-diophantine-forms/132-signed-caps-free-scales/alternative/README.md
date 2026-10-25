# Signed pooled Pell cap: direct quartics in 352 and 355 integers

Preferred result: 352 unrestricted integers, exact degree 4, 219 quadratic residuals, 9,355 expanded monomials, coefficient height 15,020,718. Simpler sibling: 355 integers, 220 residuals, 9,370 monomials, same degree and height.

The new arithmetic principle recovers the sign and index of sixteen Pell ordinates together. A single certified cap V=Y_(2W)(A) bounds their squared magnitudes; one pooled squared congruence then forces every signed index to equal its desired positive index. This removes their sixteen separate comparison/index certificates. An explicit odd-quotient construction removes the remaining auxiliary-ordinate sign guard for the 352 endpoint.

The literal equations are `odd_cap/equation.json` and `signed_cap/equation.json`; full coefficient lists are supplied beside them. All unknowns are unrestricted integers and no exponentiation or special-function primitive remains. `PROOF.md` gives both directions, the cap's ordinary polynomial certificate, noncircular size/sign bootstrap, all nineteen power-request orientations, and the exact inherited logical boundary.

The no-zero sentence is equivalent in ZFC to Con(ZFC) at the same ordinary-proof level as the frozen direct parent. This is not a new kernel-checked or literal object-language ZFC proof. No consistency assumption is used. Neither construction simulates K215 or uses Jones's universal polynomial.

Compared with the new incoming 442-integer quartic, the 352 result uses 90 fewer integer coordinates (20.4%). It trades that improvement for greater coefficient height and support. Compared with its direct 489 parent, it saves 137 coordinates. The incoming 261-variable capped equation is over naturals, not unrestricted integers; the counts are not interchangeable. No global record or historical-priority claim is made.

Rebuild and check, using standard-library Python only:

    python build_signed_cap.py rebuilt352 --odd-auxiliary
    python check_signed_cap.py rebuilt352
    python build_signed_cap.py rebuilt355
    python check_signed_cap.py rebuilt355

Repeat with Python -O. The independent checker checks literal cap formulas, parent deletion boundaries, retained power coverage, the exact 41-atom frame identity, all sixteen presemantic index lower bounds, every monic restoration, and the complete expansion. Independent mathematical review, finite arithmetic receipts and concrete negative controls are included. Their scope is finite syntax/arithmetic checking, not deciding consistency.

Credit is given to the incoming natural pooled-cap theorem, the earlier signed comparison-base and power theorems, the parent's paired guards/factorial radius, and the direct C222/refutation calibration. The squared signed cap and its instantiated endpoints are the new contribution. Frozen dependencies and source hashes are retained; no remote state was changed.

Final verification: both endpoints passed normal and optimized Python; 26 altered-input/certificate/extra-row controls were rejected in each mode. All four fresh builds (two endpoints, normal and optimized) reproduced every generated artifact byte for byte. The independent Horn audit checks 17 affine roots, 11 product links, 18 rewrites and no factor escape.
