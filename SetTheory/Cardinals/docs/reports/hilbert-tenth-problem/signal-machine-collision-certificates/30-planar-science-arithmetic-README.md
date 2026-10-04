# Arbitrary rational elliptic backward-orbit certificate

The requested extension from Gaussian rational rotations to every rational infinite-order elliptic matrix in SL₂(Q) is proved in `PROOF.md`.

## Main result

For a fixed list of J nonzero rational contacts:

- Pure avoidance of all nonnegative backward orbits: 81J ordinary positive witnesses and 44J equations
- Radius-and-avoidance strict kernel: 1+81J positive witnesses and 1+44J equations
- Sum-of-squares polynomial: exact total degree 12

The proof uses the rational contact basis [z,A⁻¹z]. For reduced trace p/q, q≥2, its n-th backward orbit point has exact joint denominator q^(n−1) for n≥1. The time-zero point is excluded separately. Bounded quadratic-ring coefficient extraction uses the fully displayed fifteen-equation Pell POWER module twice per contact.

The same denominator theorem yields an elementary uniformly polynomial-time rational elliptic membership algorithm, without a general Orbit Problem call. The algorithm does not build Diophantine witnesses.

## Files and verification

- `PROOF.md`: complete theorem, bounds, equations, soundness/completeness, domains and ledger
- `check_certificate.py`: newly written, inspected, standard-library exact checker
- `CHECKS.json`: passing fixture counts and full symbolic witness/equation ledger
- `SOURCE_PINS.json`: hashes of proof, checker and read-only arithmetic dependencies
- `PACKET_MANIFEST.json`: frozen hashes for this packet

The fresh checker passed 32,300 power instances across 1,292 reduced signed traces, including even and composite denominators; 330,752 factorization instances; rational conjugacy, forward/backward orientation and strict-boundary checks. Its complete one-contact positive-adapted symbolic expansion has 82 positive witnesses, 45 equations, 847 monomials and degree 12.

This is conventional proof plus finite exact supporting tests. No upstream source, legacy constructor/checker, physical simulator or Lean build was executed. The POWER characterization relies on the identified pinned constructive Pell theorems. No generic arithmetic DAG, gate count, small witness, finite-fold or formalized end-to-end claim is made.
