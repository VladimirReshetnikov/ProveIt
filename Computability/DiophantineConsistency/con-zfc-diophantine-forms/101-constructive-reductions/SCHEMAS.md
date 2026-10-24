# Reading the literal polynomials

All variable indices and node indices are zero based. A register name is an annotation of a polynomial expression, not an additional variable. The domain declared in each file is essential.

## Fourteen-integer circuits

Schema: `integer-polynomial-dag-v1`.

- `variables` is the ordered list of fourteen unrestricted integer unknowns.
- `nodes` is a topological array. A node is `['variable', name]`, `['integer', integer]`, `['coefficient', name]`, or `['add'|'sub'|'mul', left_index, right_index]`.
- A binary node uses earlier array entries. Repeated indices implement squaring or reuse without creating a new unknown.
- `output` selects the polynomial whose value is set to zero.
- `coefficient_binding` identifies `upstream/coefficients/BINDING.json`; its payload records bind named ports to complete unsigned byte strings and hashes. These six ports are positive integers. The finite recipes reconstruct those exact integers.
- `named_registers` records the formula-to-node correspondence. `exact_degree` is justified by the cancellation-resolved proof and leading-form certificate, not just maximum-degree propagation.

The variable order is `j,C,z,h,r,v,w,T,c,n,t,p2,p3,p1`. In the printed formula the four-root norm is a polynomial abbreviation. The JSON graph has no square-root or division operation.

## Nine-positive-integer circuits

Schema: `saturated-positive-nine-v1`.

- `variables` is the ordered list `b,g,h,s,w,C,i,j,n`, all strictly positive.
- `nodes` is a topological array of dictionaries. Variable nodes have `kind: variable` and a name. Binary nodes have `kind: add`, `sub`, or `mul`, with `left` and `right` indices. Numeral nodes have `kind: literal` and an integer `value`; fixed coefficient nodes have `kind: fixed` and a binding `name`.
- `output` is the single polynomial output. `named_nodes` identifies the displayed registers.
- `profile` selects the coherent original31 or compact54 data. Fixed leaves are under `fixed/boundary` or `fixed/compact`; `BINDING.json` lists complete gzip-compressed unsigned little-endian magnitudes with a separate sign.
- `coefficient_recipes` are ordinary finite polynomials in the four native ports, in the documented port order. They supply independently checkable exact values, not free parameters.
- `power_plan` lists fixed-exponent addition-chain steps. These are a compact evaluation schedule for fixed powers, never variable exponentiation.
- `raw_degree_bound` can exceed `exact_degree`: cancellation in the norm is explicitly resolved in the proof and independent degree audit.

The full-radical majorant is the exact 333-term polynomial in `data/saturated_corrected_P.json`. Its positivity certificate is checked after the documented positive shifts.

## Direct sum-of-squares equations

Schema: `finite_quadratic_residuals_v1`.

- `variables` is an ordered array of dictionaries. Names and kinds are explanatory; the array position identifies the actual variable.
- Each entry in `residuals` has a label and a `terms` array.
- A term `[c, [i1, ..., ik]]` means the signed integer coefficient `c` times the product `x_i1 ... x_ik`. Repetition expresses powers; an empty list is the constant monomial. The residuals have total degree at most two.
- The final equation is **the sum of the squares of all residuals equals zero**. It is a single ordinary polynomial equation. Over either stated integer domain this is equivalent to the vanishing of every residual.

For example, the integer equation's first residual is encoded as

```json
[[-9, []], [-6, [2]], [-1, [2, 2]], [1, [4]]]
```

and denotes `x4 - x2^2 - 6*x2 - 9`. There is no hidden coefficient parameter.

The accompanying `sparse_integer_polynomial_v1` file contains the full collected expansion with exactly the same term convention. Its `variables` field is the variable count. `metrics` in the residual equation reports this expansion's total degree, number of nonzero monomials, and maximum absolute coefficient. All are recomputed by the verifier.

## Certificates and digests

The natural elimination certificate gives explicit inverse substitutions with nonnegative coefficients. The integer elimination certificate gives signed monic substitutions; these are used only after changing the domain to unrestricted integers. Each step binds its pivot residual, eliminated coordinate, sign, and restoration polynomial.

The domain certificate records the initial guard set, an ordered sequence of local sign implications, the exact frame conclusions, and a final sequence of implications. Its checker verifies the literal identities and prerequisites before using each implication. The raw frame interface is first bound to arithmetic-gate residuals and then polynomially restored to the retained coordinates.

Some certificates hash canonical JSON (`sort_keys=True`, compact separators, and one trailing newline), while some source pins hash original file bytes. The relevant checker specifies which convention applies; these digests must not be interchanged. `MANIFEST.sha256` always hashes the exact delivered bytes. Finite hashes establish identity of artifacts, not their unbounded mathematical interpretation.
