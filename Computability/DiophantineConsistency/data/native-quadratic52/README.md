# Literal package-52 quadratic source

`source_system60.json` is copied byte-for-byte from
`nine/data/source_system60.json` in the arrival archive
`con-zfc-sparse-pell-124c07c0b7.zip`, committed at `4b4349064a`.
Its SHA-256 is
`ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48`.
The historical repository pin inside the file is retained unchanged.

It specifies 60 arithmetic gates and 22 comparisons over 31 source inputs,
with four coefficient ports in the order `beta,K0,MC,MF`. This copied
algebraic interface contains no machine transition table or native
coefficient payload. Its original positive-domain source is translated to
nonnegative coordinates by replacing every input with its successor.

The generator `scripts/generate_native_quadratic_parent.py` independently
expands the gates, compares all coefficients with the pinned package-52
interior-regular certificate, and emits `NativeQuadraticParent.lean`.
Lean checks the resulting exact identity and extraction theorem for every
commutative ring and every value of all four ports. Neither the data copy
nor that local theorem identifies a particular native coefficient tuple
with the finite ZFC-refutation predicate.

The source originates in the ProveIt report collection and retains its
original metadata and provenance. The surrounding repository license
applies; the delivered package-52 notices remain at
`con-zfc-diophantine-forms/52-sparse-pell/NOTICE.md`.
