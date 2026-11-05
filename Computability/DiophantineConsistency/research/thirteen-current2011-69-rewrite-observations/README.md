# Local 13/69 rewrite observations

These observations concern the graph pinned by SHA-256 `8667df5fe2f33c14a4280972336611218ebfb68883347bbfbb9215e5ab72a517` in [the 13/69/174 packet](../thirteen-current2011-69-174/). They are gate-count comparisons for individual replacements in that graph, not lower bounds and not new equivalence theorems.

- Replacing `Delta = a^2 + H` by `(a+2)^2 - 1` needs three operations for the latter expression, while the existing calculation needs only a squaring and one addition using the already shared `H`. In either case `H = 4a+3` remains necessary for `gammaH`.
- Replacing `q^2 - 1` by `(q-1)(q+1) = qm*(q+1)` needs two operations after the existing `qm` and `q` rather than the single subtraction from the already shared `q^2`.
- Expanding the main norm as `(X+gamma*H)*(X+gamma*H+2*a*c)-H*c^2` does cancel its highest formal terms, but the direct straight-line replacement needs an extra operation for `2*a*c` compared with the existing square and difference.
- Factoring the final scaled norm by `Delta`, and using the Pell equality to replace the shared squared term, leads to the existing 70/140 and 71/128 forms. Those have separately checked model-zero equivalences; they are not identical polynomials and are not a 68-operation improvement.

No smaller candidate or global optimality claim follows from these observations.
