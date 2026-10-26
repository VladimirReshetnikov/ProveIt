# Suggested additive integration into ProveIt

The package is self-contained for the new finite constructions and suitable for
an additional directory under `Computability/DiophantineConsistency/` or an
incoming submission. It does not require overwriting any earlier endpoint.

## Recommended entry points

Use `ConZFC_Exact_Contractions.pdf` as the readable report and
`ConZFC_Exact_Contractions.tex` as its standalone source. Advertise the main
result as **92 unrestricted integer variables, exact total degree 692**, with
29 residual squares and the proved expanded-height bound **less than 2^1655**.

Keep `principal92/circuit92.json`, `projection92.json`, the three files in
`principal92/sources/`, `PROOF.md`, `PROVENANCE.json`, and their independent
verifier together. The graph or the printed source-plus-substitution definition
is a full definition of the ordinary polynomial. A display containing only the
29-square schema without those literal data would not be a complete replacement.

Keep the source-binding certificates with the lower-degree profiles too. In
particular the 193-variable, height-16,866 sextic has a different 217-variable
source from the 191-variable sextic. `PROFILES.json` gives exact paths, hashes,
and metrics. Preserve the original inherited notices and archive hashes if
deduplicating dependencies into the repository.

## Suggested verification gate

```sh
python3 -B check_manifest.py
python3 -B verify.py --components
python3 -B -O verify.py --components
python3 -B code/check_report.py
```

The manifest covers the delivered bytes, while the verifiers prove the relevant
finite algebraic identities. Rebuilding the report may change PDF metadata; it
does not change the polynomial if the equation checks continue to pass. Do not
use receipt files as substitutes for executing the checker when modifying data.

## Useful formalization boundary

An economical formalization begins with a generic theorem for a unit residual
`epsilon*y + f(x)`, where `epsilon` is +1 or -1, inside a sum of squares.
Prove that coordinate projection and integer polynomial restoration give
inverse maps between the zero sets. Then check the finite acyclic definition
graph and connect its source to the retained 220-variable polynomial.

The remaining degree proof can use the supplied nonzero coefficient witness
over the finite modulus plus the integer sum-of-squares leading-term argument.
The height bound is an inductive coefficient-norm bound. Neither requires
expanding the degree-692 polynomial.

The unbounded arithmetic and logical source theorem remains a separate
dependency. Preserve the actual C222/ZF/ZFC interfaces and the constructible
Choice argument; do not replace them with an assumption that finite testing has
verified the whole logical calibration.

## Comparison wording

The 92/692 construction improves the inspected direct-calculus 94/65540
construction in dimension and total degree. It has one more residual square
and a larger largest literal scalar. It is not the fewest-variable equation in
the repository across all domains and construction families.

The compact contribution is the proved `b^2` transport factor. The late `bV`
graph and 85/232 metric are already present in incoming work. Supporting
oriented-pooling and factored-radix sections should retain their stated scope;
neither should be described as a new best endpoint on every metric.
