# Internal square divisibility: author result

`ArithmeticSquareDivisibility.dvd_of_square_dvd` proves in every IΣ₁ model
that `0<m` and `m*m ∣ z*z` imply `m ∣ z`, including `z=0`. It uses the actual
internal Bézout gcd certificate from `ArithmeticGcdNormalization`. The gcd
is positive because it divides the positive m. Its coefficient identity is
cancelled by that positive gcd to give a Bézout unit for the normalized
factors. The original square divisibility is cancelled by the positive square
of the gcd; unit-certificate cancellation gives the normalized scale divides
the normalized root, and the Bézout identity then makes it divide one.
Positivity forces the normalized scale to be one. No standard gcd, prime
factorization, quotient premise or extra axiom is supplied.

Current `ArithmeticGcdNormalization` differs from the older accepted provider,
so it was rebuilt from its current source before the new pair. Two fresh
author runs match all three objects and full logs. The main logs are empty;
the new theorem's axiom report contains only `propext`, `Classical.choice`,
and `Quot.sound`. Each run rehashed 347 inherited provider entries. This is
a same-author replay; independent review remains necessary.

The [35-file evidence manifest](arithmetic-square-divisibility-build-evidence/FILES.json)
SHA256 is `ff8a95d961141098e1f3b082deea49ac8a4635d5a73fdaf9caadd1eab76f764c`.
It preserves the first failed compilation, successful attempts, sources,
provider inventories, complete logs, timings, and drivers. The first failure
used an unavailable `dvd_one` identifier; its repair derives equality from
positivity and `le_of_dvd`. The successful provider is
`/tmp/adaptive13-square-dvd-nli2er3n/lib`. Applying this lemma to the actual
adaptive scaled norms is separate work, not part of this generic theorem.

| Source | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| ArithmeticGcdNormalization | `62edfd87c326e7f14a7f14dc11a2076cf203b21c09d9739667f8be3ddbadcd3b` | `d5603d6f08940f9c29efde9bc927464d9fdd1a5e2fe82af348c8d359ea37a031` |
| ArithmeticSquareDivisibility | `f775c2050a794b1ea026cdec0950e42528260fa1d75a03f1ef625f258670e660` | `98ccde1178ce7f3600472ed68bcd38b1701e42a1f0e54ed268de7891959be134` |
| ArithmeticSquareDivisibilityChecks | `d92fafd24bfc61f04d607eca29cbf7834978c64fe6bdfe660e63f32288f4ae9a` | `af34eb52744683768bbed5489c547c585af3efd9331ebc932b777391234735cb` |
