# Source substitution vectors and allocation stacks

For any model-valued free-variable index `witness`, `sourceSubstQVec_trace_entries` proves that the actual relational-source qVec history of `[free witness]` has entry j equal to `bound j` for every j<i and entry i equal to `free witness` at every internally coded depth i; the vector is also internally scoped and has length i+1. `sourceSubstStack_aligned` proves the two bound stacks formed by allocating an arbitrary model-valued number of identical inner labels agree below that number and the second stack contains the substituted root label at that index. Both results include nonstandard depths and are proved using internal Σ₁ induction in models of PRA plus IΣ₁.

These are prerequisites for arbitrary-depth existential substitution, not a formula-level substitution theorem, unrestricted existential rule, full compiler, PA identification, or machine/consistency equivalence.

The independent same-output source replay passed against previously source-replayed baselines, retaining prebuilt workspace dependencies. Run `check-source-subst-stack.sh --out OUTPUT` for the repository source-closure audit and two axiom reports; retained workspace foundations are documented by `check_bridge.py`.
