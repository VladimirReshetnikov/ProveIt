# Exact polynomial and arithmetic-graph formats

All polynomial variables range over **unrestricted integers**. Indices are zero based. Coefficients are exact JSON integers; use arbitrary-precision integer parsing. Python's standard `json` parser preserves them. JavaScript's default numeric JSON parsing can round the primary coefficients, which exceed its exact integer range.

## 1. The ordinary polynomial

`equations/polynomial.json` has this schema:

```json
{
  "format": "ordinary-polynomial-sparse-v1",
  "domain": "unrestricted integers",
  "variable_count": 3,
  "terms": [[5, []], [-3, [0]], [7, [0, 0, 2, 2]]]
}
```

This illustrative object specifies

\[
5-3z_0+7z_0^2z_2^2.
\]

Each term is `[coefficient, monomial]`. The monomial is a sorted list of variable indices, repeated according to multiplicity. The empty list denotes the constant monomial 1. It is **not** an exponent vector: `[0,0,2,2]` means two copies each of variables 0 and 2. No absent variable or monomial contributes a term. Equal monomials are collected, zero coefficients are removed, and the supplied terms are sorted lexicographically by their monomial lists.

In the actual primary file, `variable_count` is 1873 and there are 77,523 terms; every variable from 0 through 1872 occurs. The largest monomial-list length is exactly four. The companion has 3,292 variables and 11,218 terms. Both are complete coefficient lists, with no parameter or coefficient file to fetch separately.

A minimal exact evaluator is:

```python
def evaluate(polynomial, values):
    if len(values) != polynomial["variable_count"]:
        raise ValueError("wrong tuple length")
    result = 0
    for coefficient, monomial in polynomial["terms"]:
        term = coefficient
        for index in monomial:
            term *= values[index]
        result += term
    return result
```

This evaluates one tuple; it does not decide whether any integer zero exists.

## 2. The sum of quadratic squares

`residuals.json` is a JSON array of objects

```json
{"label": "example residual", "terms": [[-1, []], [1, [0]], [-1, [1, 2]]]}
```

The example residual is \(Q=z_0-z_1z_2-1\). Its terms use precisely the preceding sparse format. Every actual residual has degree at most two. The polynomial is the **sum of their squares**:

\[
P=\sum_Q Q^2.
\]

Labels identify gate equations, original semantic equalities, or natural-domain guards; they do not change coefficients. `verify_polynomial.py` reconstructs all residuals from the circuit, squares and collects them independently, and compares every coefficient with `polynomial.json`. A hash match alone is not used as a proof of this identity.

For each semantic coordinate required to be nonnegative, the integer compiler adds three fresh integer witnesses and the residual

\[
z_j-a^2-b^2-c^2-c.
\]

Its vanishing implies \(z_j\ge0\), since \(c(c+1)\ge0\) for every integer c. Conversely every nonnegative integer has this form, by the three-squares theorem applied to \(4z_j+1\). Thus these guards enforce the intended natural domain without imposing an external domain restriction on the final variables.

## 3. Arithmetic DAGs

Both `circuit.json` and `semantic_certificate.json` identify their format as `mixed-integer-arithmetic-dag-v1`. The `nodes` array is topologically ordered:

| Node | Value |
|---|---|
| `["c", n]` | Literal integer n |
| `["v", j]` | Semantic input j, named by `variable_names[j]` |
| `["a", p, q]` | Value of node p plus value of node q |
| `["s", p, q]` | Value of node p minus value of node q |
| `["m", p, q]` | Product of values of nodes p and q |

Every p,q refers to an earlier **node**. Each equality `[p,q,label]` requires its two node values to agree. Subtraction is ordinary integer subtraction, including in intermediate wires. There is no power or factorial opcode.

`circuit.json` is the pruned graph used by the quartic compiler. Its 245 semantic inputs are partitioned by `nonnegative_inputs` and `unrestricted_inputs`. `sign_inference` records the division-quotient cases whose nonnegativity follows from other constraints and therefore needs no separate guard. These logical domain claims are checked by the source auditor.

`semantic_certificate.json` retains the graph before pruning, together with `source_binding`, `call_ledger`, and `batch`. These objects bind the local row and arithmetic interfaces to the actual emitted nodes. The batch includes all forty power-call ports, the sixteen seed index records, and the three recurrence-derived index records. These are audit metadata; the corresponding arithmetic equations have already been expanded into the DAG. **Node identifiers from the two DAG files must not be mixed.**

The first 245 variables of each final polynomial correspond to the semantic input slots. Additional variables are allocated deterministically to retained nonlinear/affine values and then to the three witnesses per explicit natural guard. A DAG node identifier is not generally a final polynomial-variable index. The residual labels and the exact flattening verifier supply the connection.

`local_row.json` stores the projected local source using its own variable and node numbering. Its output is the inherited nonnegative pair whose difference is the row polynomial; the source auditor also checks the direct signed evaluation used by the release.

## 4. Metrics, serialization, and reproducibility

`metrics.json` records measured counts, including variable and residual counts, exact degree, nonzero collected monomials, and coefficient height. Height means the maximum absolute coefficient after full collection. It does not measure proof length, evaluation time, or witness size.

Both variants use the same semantic graph. `--affine-cap 16` retains 37 affine values and produces the 1,873-variable primary; `--affine-cap 1` retains 1,456 and produces the 3,292-variable companion. The complete variable accounting and guard coverage are checked independently.

The builder writes compact UTF-8 JSON with separators `,` and `:`, followed by one newline. Byte hashes therefore detect serialization changes as well as mathematical changes. The primary polynomial SHA-256 is

```
18d09e54a3d66ed33422560a35724a5073fd1ca1a2a76bfaf16e634cb019ea1d
```

Run `python3 verify_release.py` for deterministic rebuilds, exact coefficient comparisons, and the separately scoped semantic-interface checks. The ordinary unbounded correctness arguments remain in the report and proof notes; a successful finite replay is not itself a proof-assistant verification of the consistency theorem.
