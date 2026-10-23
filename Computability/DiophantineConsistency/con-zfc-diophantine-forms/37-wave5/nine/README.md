# Nine-variable completed-square synthesis

The sharp equation has 9 natural unknowns, one equation, degree 92324·5^32+296 and 1505 binary operations; the strictly positive translation uses 1500 operations. Compare source 30's 9-natural equation at degree 120724·5^32+366 and 1840 operations. This is an ordinary-mathematical synthesis, not a new kernel theorem or a minimum claim.

The full definition and proof are PROOF.md. Fixed ports use the complete source 30 compact943 tuple in ../coefficients, unchanged. Jones constants and the 31-variable quartic are pinned under source/30-quartic31. The two executable commands are:

    python3 build_nine.py
    python3 verify_nine.py

The circuits are generated/nine_sharp_natural.json and generated/nine_sharp_positive.json. generated/ledger.json contains exact counts; generated/DEGREE_CERTIFICATE.json and generated/VALIDATION.json record executed audits. Every fixed leaf has an explicit bounded recipe; no circuit register is an additional unknown. N means nonnegative integers. The natural-domain majorant arguments must not be applied to nine unrestricted integers.

Also included is the less cancellation-sensitive structured source 28/source 30 synthesis at degree 93264·5^32+288, 1503 natural / 1498 positive operations. Source28's majorants/finalizer and source 27's evaluator are credited in PROOF.md; upstream licenses and notices are retained.
