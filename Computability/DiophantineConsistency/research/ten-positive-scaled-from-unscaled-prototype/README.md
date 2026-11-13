# Constructing the scaled Pell interval from the unscaled source interval

`TenPositiveScaledFromUnscaled.scaled_interval` is a generic theorem in every
IΣ₁ model. It assumes `X=2^(2r+1)`, `r>0`, `X,Y≥1`, `Y≤S`, the explicit
size bound `72*r<X+1`, and a positive unscaled source decomposition at the
same X,Y,r. It constructs the 80 chart's scaled Pell pair with
`P=X*S²`, `B=2*(P-1)+1`, `a=S*(X+1)-1`,
`K=2*ycoord(r+1,B)`, `C=ycoord(2r+1,a)`, and proves

    K*Y < C < K*(Y+1).

The proof derives the old source sandwich, extracts its exact small-remainder
floor, and applies separately checked scaled lower/upper Pell bounds. The
scaled upper bound uses a crude estimate derived from the old split, not the
conclusion being constructed. This establishes a missing **conditional**
reverse-construction ingredient. It does not show the assumptions from a
90 zero or halt, construct all 80 graph coordinates, prove an 80 zero,
connect an external K0/PDF, or establish an iPRA endpoint.

Accepted guarded check `observations/scaled-attempt02/` produced
`/tmp/scaled-from-unscaled-230l_w6i/ScaledFromUnscaled.olean`, SHA-256
`e0965f16e97c7a6d655517bb196dda850f0e1fa3fbd6e4176a5bf864cdf6a2c8`.
Attempt01 failed a multiplication-association proof. The runner validates
every direct source import against an explicitly declared selected path and
hash before and after Lean; the receipt records real paths. Project/package,
dynamic-library and full historical transitive source-object ancestry remain
inherited rather than audited by this check.
