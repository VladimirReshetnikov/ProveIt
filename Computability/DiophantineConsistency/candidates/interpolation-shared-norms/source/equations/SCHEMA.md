# Literal polynomial circuit format

The principal packets use schema integer-polynomial-dag-v1.

Each node is exactly one of:

    ["integer", n]
    ["variable", "declared_name"]
    ["coefficient", "authenticated_fixed_port"]
    ["add", left_index, right_index]
    ["sub", left_index, right_index]
    ["mul", left_index, right_index]

An arithmetic node references only earlier nodes. The output field is the
index of the final polynomial value. All nodes are live in that output.
The named_registers map is explanatory and introduces no variables.
Only names in variables are quantified. The coefficient leaves resolve
through the indicated binding to actual fixed integer numerals.

Evaluation is ordinary exact integer arithmetic. There are no conditional
branches, division nodes, radical nodes, variable-power nodes, or calls to a
proof predicate. Powers in the mathematical presentation have already been
compiled into binary multiplications, with identical expression sharing.

The operation count is the number of live add/sub/mul nodes. It does not
count fixed leaves, byte lengths, bit operations, or full expanded monomials.
The exact total degree is separately certified; a naive degree bound on
the DAG can overestimate the degree because it misses cancellation.

The quotient companions retained only inside the inherited source package
have their own documented compatible DAG format,
using port as the fixed-numeral leaf tag and including explicit residuals.
Their sums of squares are likewise single ordinary integer polynomials.

The three new graphs resolve all six numeral leaves through
`../inherited/root_fusion/coefficients/BINDING.json`. Their `semantic_proof`
paths point to the complete new proofs under `../proofs/`.
