# Lower-degree nine-variable circuit with shared products

This candidate improves package71's nine-positive equation from478 to
**475 live binary operations**, retaining its exact degree **1,379,730**.
Its nine-natural translation improves from485 to482 operations. Both
polynomials, all named registers and the complete original31 coefficient
tuple are unchanged. The package71 delivery remains intact.

The reduction is the same three-gate saving independently checked for
[`gap2082-shared-products`](../gap2082-shared-products/README.md):

```
MU = M*U;   P = 2*M*MU;   A = M+MU;
E = k*(C*D);             K = R1+h*(P-1),
```

where `C*D` is also used in the majorant and `R1=R+1` has already been
computed before subtracting one to obtain `R`. The shared-product rewrites
and cancellation are exact identities over any commutative ring. No
assumption about the witnesses is needed for the identities.

Each rewrite receipt contains four exact local sparse integer-polynomial
checks and a complete structural gate remap. All local cut points precede
their replaced parent node. Structural induction then identifies the
entire output and every named register. The parent's ordinary exact-degree
certificate and positive/natural zero sets therefore transfer directly.
No new native compiler or object-language ZFC proof is asserted.

The checker authenticates both parent DAGs and reconstructs every fixed
leaf from the complete original31 tuple, using the authenticated payloads
under `con-zfc-diophantine-forms/31-sun10/coefficients`. The DAG metadata
retains all coefficient recipes, scale exponents, source/layout pins and
the original domain. Every node and all nine inputs are live. Squares and
fixed-scalar multiplication are charged; numeral leaves and reuse are free.

Sixty assignments per domain over three primes compare all named values
with the actual coefficients. These are transcription diagnostics, in
addition to the exact identities. Changing `A=M+MU` to subtraction must
fail the exact check. Normal and optimized Python runs pass.

From the repository root:

```
python3 Computability/DiophantineConsistency/tools/build_shared_products71.py --check
python3 -O Computability/DiophantineConsistency/tools/build_shared_products71.py --check
```

No Lean process is invoked. For the inherited full ordinary construction
and its scope, see
[`package71/nine_positive/PROOF.md`](../../con-zfc-diophantine-forms/71-determinant-guards/nine_positive/PROOF.md).
