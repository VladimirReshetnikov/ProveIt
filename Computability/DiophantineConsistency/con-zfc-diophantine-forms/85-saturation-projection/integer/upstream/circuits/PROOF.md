# Literal equivalence and accounting of the shared DAGs

## The claim

For each selected source packet in ../joint/, let Q be its displayed sum
of squared residuals, with its exact ordered variable list and fixed
coefficient tuple. The corresponding *_dag.json evaluates Q itself on
every assignment over every commutative ring. It does not merely vanish
on the same integer tuples. The arithmetic identities used are universal
integer-polynomial identities.

The live counts are109,112,115,118,121,127 for the19,20,21,22,23,25-variable
packets, respectively. The exact degrees remain88,32,20,16,12,8 because the
polynomials are unchanged. Degrees and their nonzero authentic-coefficient
witnesses are proved by the independent joint component; this component
proves exact equality with those literal polynomials.

## Compact registers and safe simplifications

The shared schedule retains the source definitions of q,W,X,Y,C,k,H,Delta,
R,det,T and Pos. It computes q-1 directly as beta*(3*J3+1), reuses q² in
both q³ and R, and uses W=12*w3+4 in place of4*(3*w3+1). All scalar
multiplications are counted.

For eliminated a and E it uses a=E+Y and, when E is also eliminated, E=XY.
Then a-E=Y is an exact identity, not an inference from an unsatisfied
residual. In the nineteen-variable case eta=c-kY, so c-eta=kY is exact.
For retained a or eta the corresponding subtraction is actually evaluated;
it is never silently replaced by a source equation.

The coordinates V and I are computed as fo-c and (2r+1)c² only when the
specific source packet eliminates them. Otherwise they remain free inputs,
and their restoring rows remain in the literal sum of squares. Likewise,
the25-variable packet keeps a free zeta and its restoring row; its final
joint guard uses eta*zeta, exactly as in that source packet.

The source's twelve base rows are independently specified in check.py.
The verifier checks the row omissions and complete substitution maps for
each selected packet. No live DAG operation is attributed to an unused
name, and no named register is counted as a quantified variable.

## Exact staged proof without a huge final expansion

The verification has four algebraically sufficient stages.

1. For the19-,20-,21-variable factored packets, recursively inline all
   compact and restoring registers in the independent reference rows.
   The resulting syntax trees equal the delivered source residual trees
   exactly. For the22-,23-,25-variable expanded packets, establish source
   equality by direct exact sparse-polynomial comparison instead.

2. Compute the DAG roots X,Y,W over the original polynomial ring in all
   retained witnesses and fixed coefficient ports. Compare them exactly
   with q*4*(3*w3+1), (2*v_scale+1)*q³, and4*(3*w3+1), where
   q=beta*(3*J3+1)+1. These identities validate the cut definitions.

3. Regard X,Y,W as independent symbols. Fully expand each residual, but
   do not substitute these three large polynomials and do not square the
   residual. The DAG and the independent partially inlined reference
   polynomial agree exactly in this cut ring. The largest cut polynomial
   has1,931 monomials, namely the nineteen-variable joint guard. Substituting
   the validated cuts into an identity preserves equality, proving every
   literal residual identity over the original inputs.

4. Regard the residual values as independent symbols. Expand the final
   DAG segment and verify that it is exactly the sum of their squares.
   By composition with Stage3, the complete DAG equals the source Q.

This is a proof by exact polynomial substitution, not numerical testing,
leading-term comparison, or equality modulo the residual ideal. It avoids
the expensive and unnecessary expansion of Q itself.

## Contracted displayed first norm

The report can display the nineteen-variable first norm as

    tau²-XY²(XY²+1)k²-1.

The exact source row is tau²-E(c-eta)[k+E(c-eta)]-1. After the validated
substitutions E=XY and eta=c-kY, the identity

    E(kY)[k+E(kY)] = XY²(XY²+1)k²

is checked in the small polynomial ring Z[X,Y,k]. The exported helper
displayed_first_norm() performs this check; check_packet('joint19_degree88')
establishes the source and cut bindings that license its substitution.

## Counting convention and limits

The source list contains only binary+,-,* gates. Reachability is recomputed
backward from the output, and every listed operation must be live. Every
witness and fixed port must occur in the live closure. Histograms count
squaring as multiplication and charge multiplication by small integers.
The residual-system subtotal excludes exactly the final squares and their
addition tree. Six complete normal and optimized exact audits pass.

No search for a smallest circuit was performed, and no bit-complexity claim
is implied. The consistency/refutation equivalence and its formalization
boundary remain exactly those of the authenticated joint source family.
