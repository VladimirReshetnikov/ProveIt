# Independent external review: serialized macro cost

Pass for the explicitly stated serialized-macro convention. An independent iterative typed traversal of the pinned 45-node JSON counts 39 additions, 23 subtractions, 64 multiplications, 44 power nodes, two range sums and one star sum: 173 unit macro operators. Named references are shared, every explicit within-node occurrence and each sum body is counted once, while exponent/bound syntax and leaves are excluded. The author output reproduces byte-for-byte.

This is not a binary arithmetic circuit count, finite-sum expansion, numerical coefficient-construction cost or evaluation cost. The external JSON remains unbound to Lean by a semantic theorem.

Checker SHA-256 `5a4f147317e55e12ce85a57eb9cac8d9df1c710c3ea8f86ae5432039d5038cc9`; result SHA-256 `5ba1efed48b1c28d64df266ad88c1c4d4b11510f4b145cf81c4b7fbffdf0b111`.
