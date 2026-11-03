# Same-witness fresh first coordinate for an actual 80 zero

`TenPositive80FreshFirstCoordinate.graph_fresh_first_coordinate` combines one
actual positive 80-graph zero and its symbolic β/low/high ports with one fresh
unscaled source tuple. It constructs the same r, η, ζ, γ, h used in the main
reconstruction together with a **positive** transport quotient t and a
**positive** first-factor coordinate s. For `P=X*Y²`, fresh doubled first
ordinate K, and its positive Pell root τ, it proves the transport equality,
first norm and exact coordinate equation

    (p₁+w)*Cmask = F + b*t,
    τ² = 1 + P*(P+1)*K²,
    τ + q*t*(b*K+1) = P*K + K + s + original_s.

It retains the fresh interval, positive main projection and main offset
in the same existential tuple. It proves `K≥8P+4`, `P*K<τ`, and
`original_s≤P` internally to justify positivity of s. p₁ is arbitrary; no
external K0 bytes are identified. This is a source-factor ingredient, not
yet an actual 90 factor zero or a simultaneous graph zero, and not a halt,
PDF, or iPRA equivalence.

Accepted guarded check `observations/first-attempt02/` produced
`/tmp/tenpositive-80freshfirstcoordinate-etahy1so/Direct80FreshFirstCoordinate.olean`,
SHA-256 `a3a1cc1e97e3d59ecf0be7481ed1762e411e8a800349244827066897dc514d19`.
Attempt01 failed due to an omitted import. The accepted runner individually
pins its selected direct `ArithmeticPellCongruences.olean` and the corrected
fresh-main-offset producer. It inherits the project/package, dynamic-library
and historical transitive source-object limitations.

The original FirstCoordinate provider receipt omitted an individual direct
`ArithmeticPellFirstNorm.olean` pin. The self-pinning `run-v2.py` selects its
corrected producer `/tmp/first-coordinate-rdzd04a5/`, whose v2 receipt pins
that exact object. The dependent rebuild `observations/v2-attempt01/` outputs
`/tmp/tenpositive-80freshfirstcoordinate-v0hdfs98/Direct80FreshFirstCoordinate.olean`,
bit-identical to the earlier object. Broader inherited boundaries remain.
