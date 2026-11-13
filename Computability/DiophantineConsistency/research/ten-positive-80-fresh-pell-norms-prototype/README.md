# Explicit first/main Pell norms for the fresh unscaled source

`TenPositive80FreshPellNorms.graph_fresh_pell_norms` constructs, from an
actual positive 80-graph zero at the explicit symbolic β/low/high ports,
positive η, ζ and positive first/main Pell roots τ and d. For the same graph
rank `R=2r+1`, X and Y, put `P=X*Y²`,
`K=2*ycoord(r+1, 2*(P-1)+1)`, and
`C=ycoord(2r+1, Y*(X+1))`. The theorem proves

    C = K*Y + η,   K = η + ζ,
    τ² = 1 + P*(P+1)*K²,
    d² = 1 + delta(Y*(X+1))*C².

The positive roots are actual Pell x-coordinates, obtained directly from
`norm`; P>0 justifies the natural subtraction in the first base. The fresh
C, K, η and ζ are not identified with the scaled 80-graph witnesses. The
result is an explicit source-reconstruction component: it does not establish
an old graph zero, source converse, halt equivalence, PDF binding, or an
internal iPRA proof.

Accepted guarded check `observations/fixeddigits-attempt01/` produced
`/tmp/tenpositive-80freshpellnorms-ie9ekj06/Direct80FreshPellNorms.olean`,
SHA-256 `6b498380d95dc1cce769cfb918aa9c7a8da9ddc67408c59029bb1bb36afe33cc`.
The receipt pins selected direct inputs and resources; complete project and
package ancestry, dynamic libraries and historical source-object provenance
are inherited rather than rebuilt here.
