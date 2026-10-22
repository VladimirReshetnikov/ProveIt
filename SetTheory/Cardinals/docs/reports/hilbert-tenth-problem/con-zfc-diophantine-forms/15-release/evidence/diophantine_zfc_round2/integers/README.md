# Unrestricted-integer refinements

All counted variables range independently over the integers. The four fixed compiler-coefficient ports are bound by the release's COEFFICIENT_BINDING.json. Domain proofs are in SIGNED_DOMAIN_PROOF.md; finite arithmetic receipts are not substitutes for those proofs.

Recommended packets:
- start_only_integer32_polynomial138_degree584.json: 32 variables, 138 arithmetic operations, degree 584.
- start_only_integer33_polynomial134_degree159.json: 33 variables, 134 operations, degree 159.
- start_only_integer33_polynomial130_degree304.json: 33 variables, 130 operations, degree 304.
- ordinary33_integer_60_degree4.json: 60 variables, 33 quadratic equations; their literal squared sum is an exact quartic.

Other final tradeoffs are retained in the JSON packets and INTEGER_LIFT_RECEIPT.json. No global minimum is claimed.

Use the top-level run_checks.py for a read-only release replay. The independent verifier uses only Python's standard library and checks exact residual substitutions, counts, degrees, compact namespaces and liveness, Pos prefixes, formal-cut degree upper bounds and attaining exact specializations. Parent JSON packets are included under parents/. Research emitters are not needed for verification and are not distributed. Running this helper directly writes its receipt in this directory, so prefer the top-level temporary-copy driver.

Pos(a,b,c)=1+a^2+b^2+c(c+1) has exactly the positive integers as its image. Only J,F,alpha,z,i,s,w,eta,zeta require this substitution. All remaining sign issues are treated by the signed-domain proof, not omitted.
