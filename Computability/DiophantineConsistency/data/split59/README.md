# Authoritative old-z report59 source and split116 certificate

These are exact inert copies of `nine_free_adjunct/data/` members in the
report59 archive at proposal commit `beb0192cb8dc36f78c369c080f2adfbc1887a486`.

| File | SHA256 |
|---|---|
|parent_source.json|`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`|
|split_code.json|`abbedad94a3e619d71d61551c9cd76db5dd9ec35e67bd8382a18deb90fb8f38e`|
|split_kernels.json|`445de50798fe3c22a195d9e643b5684f0224c7130b56a316bcb29681a58dd02a`|

The source has 31 positive coordinates and 22 quadratic equations. Its transport
coordinate is the **old** positive z, with residual
`(K0+w)*(q-F-alpha)+(q-F)-z*(q-1)-1`. The auxiliary `source_system60.json`
shipped alongside these files is not the authoritative parent and is not copied
here. Relative historical coefficient paths in the byte-preserved parent are
provenance, not a selected numerical instance for the Lean certificate.

The split code makes the invertible row changes rho14=r14+r2 and rho15=r15+r3,
then permutes the rows and separates constant/linear/quadratic channels. It has
31 distinct positive weights, maximum 116, 22 distinct targets, maximum 2129, and
89 coefficient records split as 7 constant, 39 linear, 43 quadratic. The 39 distinct
active quadratic pairs are isolated among all 496 unordered input pairs. The
same-degree interaction count is7+39*31+43*496=22544.

`../../tools/generate_split_certificate59.py` checks the three input hashes,
independently parses each displayed source residual and compares it with the
sparse term list, checks the old-z transport, recomputes the row changes and
all isolation interactions, and matches the supplied literal kernel lists.
Its emitted Lean source checks the arithmetic identities and finite certificates
independently. Native coefficients remain arbitrary ring parameters; neither
this data transcription nor a source extraction identity proves their calibration
to K215 or syntactic ZFC refutation.

The checked Lean interfaces are:

- `SplitGeometry59`: literal weights/supports, isolation and cross-row exclusion,
  input position cardinality31/range117 and target cardinality22/range2162.
- `SplitCertificate59`: authoritative old-z `sourceRows`, the two invertible row
  operations, and `coeff_zero_iff_source_zero` over the integers. Each extracted
  coefficient is twice the corresponding transformed/permuted source residual.
- `SplitKernelData59`: the actual7/39/43 kernel records, degree ceilings
  1719/2027/1929, quadratic top coefficient1, and `kernelBounds_box`. The latter
  bounds every coefficient by2*Bcap*Kcap under Bcap>=2, Kcap>=16Bcap and the
  supplied nonnegative port bounds beta,MC<Bcap, MF<2Bcap, K0<Kcap.
- `SplitKernels59`: the literal kernels equal the three abstract extracted
  channels over every commutative ring; `sourcePolynomial_zero_iff` specializes
  this exact binding to integer source zeros. The source polynomial has degree
  at most2161. `kernelBounds_pow` specializes the height to2^(p+q+1), so the
  whole54 port box p=429959,q=434054 gives the sharp height2^864014.

The finite checks use kernel-checked `decide +kernel`, and every public endpoint
has a dedicated `Lean/checks/` axiom audit. The generated three Lean files are
byte-reproducible from the two generators and the pinned JSON. The handwritten
`SplitKernels59.lean` checks the final literal/channel identity. Python execution
is not an assumption of any Lean theorem.

The all-one source tuple cannot vanish: its row9 equals-7 for arbitrary ports.
Consequently a natural digit tuple whose positive shifts solve the source has
at least one positive digit. This supplies the nonzero low-word boundary without
assuming positivity of beta or importing the older shifted-z transport domain.

These theorems do not discharge the whole native tuple's compiler calibration
to K215/refutation, and do not assert an object-language ZFC proof of the final
consistency/unsolvability biconditional. The port-box assumptions in a sharp
numerical instantiation must also be proved for the actual selected tuple.
