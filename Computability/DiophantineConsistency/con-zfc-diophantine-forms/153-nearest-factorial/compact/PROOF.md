# Shared kY in the partial-saturation equation

The incoming `Coprime_Products_and_Positive_Centers` component's
`compact_xy/equation_80_382_partial.json`, retained here as
`upstream/equation_80_382_partial.json`, defines a polynomial in ten
strictly positive integer variables. Its ordinary proof is retained in
`upstream/PARTIAL_Q2_PROOF.md`, with the accompanying source closure in
`upstream/`. The local `parent80.json` is an exact byte copy of that source.

Its circuit contains `kY=k*Y`, `D=X*Y`, `V0=D*Y`, and `V0k=V0*k`.
The register `V0` is used nowhere except in the definition of `V0k`.
Consequently it can be deleted and the last definition replaced by
`V0k=D*kY`. Associativity and commutativity of multiplication prove that
every surviving register has the same polynomial value, for arbitrary
integer inputs and arbitrary values of all four coefficient ports.

There are now 79 live binary arithmetic operations instead of 80. The
single polynomial itself is unchanged. It has the parent's exact degree
382, the parent's positive zero set, and the same ZFC-formalizable
no-positive-zero / Con(ZFC) equivalence with precisely the parent's
ordinary calibration dependencies. This is a circuit improvement, not a
new polynomial, a new variable-count result, or a newly formalized proof.

The full highest homogeneous component, inherited unchanged, is

    -2^10 (beta J)^206 w^34 s^80 i^14 (eta+zeta)^46 T^2.

It is nonzero for the actual fixed positive beta. The other fixed ports
K0, MC and MF are also unchanged. Their complete binding, including file
names and compressed/uncompressed hashes, is embedded in the
`coefficient_binding` field of both local equation JSON files. The four
compressed integer payloads are supplied in `coefficients/` and identically
in `upstream/coefficients/`. The finite reconstruction recipe is
`upstream/rebuild_coefficients.py`; it is checked by the local `verify.py`.

The identity is the composition of that partial-q-saturation endpoint
with the `kY` sharing already used in the incoming `Centered_Residues`
component. Neither ingredient is claimed as a new invention here. This
specific 79-operation evaluation was not found among the eight incoming
archives inspected at ProveIt commit
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`.

## Reproduction and verification

Run the following from the release root:

```sh
python3 -B compact/build_partial79.py --check
python3 -B -O compact/build_partial79.py --check
python3 -B compact/verify.py
```

The builder uses only the Python standard library and locates its retained
source relative to its own file, independently of the working directory.
With no arguments it performs the same read-only check as `--check`.
It authenticates the source's SHA256, checks the sole-use property,
constructs the transformed graph, verifies that every other row and the
entire coefficient binding remain unchanged, and checks topology and
liveness. It then compares the generated `equation79_degree382.json` and
`parent80.json` **byte for byte** with the supplied local files. These
commands do not rewrite the equations, receipts, or coefficient payloads.

To write the reproduced JSON pair into a different directory, use, for
example:

```sh
python3 -B compact/build_partial79.py --output-dir /tmp/conzfc_partial79_rebuild
```

That option writes the two JSON files and reports their hashes. It does not
copy the coefficient or proof closure; the complete release supplies those
dependencies. The builder rejects an output directory or output symlink
that would overwrite either retained local equation.

The mathematical equality of the polynomials follows from the displayed
associativity/commutativity identity and the literal equality of every
other gate. Separately, the builder performs 40 modular evaluations as
supplemental regression checks. These finite comparisons do not establish
the polynomial identity, the exact degree, or the logical calibration.
The local `verify.py` independently checks the rewrite, the inherited
attained leading form, all coefficient payload hashes, and reconstruction
of the complete fixed tuple from the supplied finite recipe. The semantic
calibration remains the ordinary theorem in the retained source closure.

The JSON output is an ordinary addition/subtraction/multiplication circuit.
Intermediate registers are polynomial abbreviations, not additional unknowns.

New analysis and code were prepared with AI assistance. The inherited
source's attribution and notices must accompany any redistributed copy.
