# 31-witness sextic candidate by eliminating the f² cut

This is an external AST candidate derived from the independently reviewed
[32-witness sextic](../nine-sharing-sign32-sextic-candidate-v2/). Replace
old coordinate 27 everywhere by `(x₅ + 1)²` and remove its `f2` defining
residual. Old coordinates 0 through 26 stay fixed, and old 28 through 32
become new coordinates 27 through 31. The distinguished input 0 is still
unused. The candidate is the sum of squares of the resulting 22 residuals
in 31 natural witness coordinates.

The only other residuals containing the eliminated coordinate are `V` and
`scaled_Ns`; after substitution both have syntactic degree 3. The checked
maximum residual degree is 3, so the degree of the sum of squares is at most
6. The unchanged first `q3` residual has coefficient `−beta³` on `x₁³` when
all other variables are zero. The coefficient of `x₁⁶` in the full sum of
squares is thus a sum of integer squares at least `beta⁶ > 0` for the fixed
positive beta. This gives exact degree 6 as an external mathematical argument,
not a Lean degree theorem. The same first residual is `−(beta+1)³` at the
all-zero assignment, so the seed is nonzero there.

For a prospective proof of equisolvability, insert the natural square at
old coordinate 27 to lift a 31-coordinate solution. Conversely, zero of
the old sum of squares forces the `f2` residual to vanish; injectivity of
the natural embedding then allows dropping that coordinate. The semantic
bridge and the iPRA endpoint remain **unproved for this candidate**. In
particular, the available nine-variable Jones construction requires a
quartic seed and cannot be applied directly to this sextic. The coefficient
binding is inherited from the 32-witness AST; byte bindings do not by
themselves establish model-port equality.

`python3 -I -S -B build.py --check` reproduces the entire transformed
AST; `python3 -I -S -B check.py` checks syntax-tree degrees and 16 finite
lift controls. These finite controls are not an all-model proof. The build,
check and retained result were run successfully with exit 0. SHA-256:

* builder `dc2ab36a55f32f5603d5ea32d3856e661a0f69b4d788471a033800bad65f38b8`
* checker `a41fe2f4e0b04ae789cc133fed5d9482319bbddf218edda174a28417894e36a0`
* seed `827740a7f65961bd1a04ae424f4c8873a636285d2b1410bb72d0bee7e3e9e6c1`
* result `1da9cad5e0ddcba02dfe8ba895174d1302c4c54b250ebc809897038547b77413`

The [independent audit](../../reviews/nine-sharing-sign31-sextic-frontier-independent/README.md)
passed the substitution, coefficient paths and exact-degree argument. The
natural lift/drop argument depends on ordered-ring and embedding properties;
it is not a Lean bridge or an iPRA endpoint.
