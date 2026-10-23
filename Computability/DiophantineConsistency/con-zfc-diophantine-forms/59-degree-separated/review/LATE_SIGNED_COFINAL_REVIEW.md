# Late audit of the thirteen-integer cofinal witness choice

Status: PASS for the ordinary mathematical completeness argument. This is not a new Lean theorem or an exported object-language ZFC proof. No frozen construction file was modified by this audit.

## Question and source scope

The concern is whether replacing the Jones completeness witness by a square is justified, since the signature of `Jones1982.exists_B25core` promises only a positive integer witness and does not expose its chosen value.

The exact proposal review requested was read at commit `a71325bf18a412d7f5968fe0b53d1694123af1e2`, including its linked `PROPOSAL_REVIEW_QUADRATIC.md`. Neither retrieved file asserts a defect in the thirteen-integer cofinal construction. They do explicitly retain the compiler, complete Lean certification, and object-language ZFC boundaries.

The construction is audited against the pinned source files delivered with the signed family:

- `signed/upstream/Ratio.lean`, SHA256 `d002e81a5d2e752c2b2b2b136b238169854671fdcafc4ae932336940ca8720ac`.
- `signed/upstream/NineRatio.lean`, SHA256 `9eebed4a7968652a60301c8696afd4f334fb2ba36d0607294f24276585f76531`.

Both are pinned to repository commit `124c07c0b77a9e20e84676514d8b1ff78536ea3f` in `signed/RATIO_SOURCE_PINS.json`.

## Explicit witness trace

In `Ratio.lean`:

1. Lines 434–437 choose k with b=2^k and prove k<2R+1.
2. Line 438 explicitly chooses the original Jones witness omega=2^(2R+1-k).
3. Lines 440–442 establish b*omega=2^(2R+1) and U=N^2*omega.
4. Lines 454–488 choose the integer part Y of rho=(U+1)^(2R)/U^R, then M=RY, A=M(U+1), P=2M^2U, C=psi_A(2R+1), and K=psi_P(R+1).
5. Lines 549–554 return these same witnesses.

In `NineRatio.lean`, lines 270–280 obtain that construction, extend it by the product-Pell witnesses i,j, and return the same h,s,omega and the shifted phi=C-B'-W. The extension does not replace omega, U, Y, C, or K.

Choose the cofinal source bases b=2^(1+2r). Then k=1+2r and k<2R+1 imply r<R and

    omega=2^(2R+1-k)=2^(2(R-r))=(2^(R-r))^2.

Thus the circuit coordinate w can be chosen as 2^(R-r), so omega=w^2 exactly. No assertion that the unrelated witness s is square is made. Cofinality is only the elementary fact that 2^(1+2r) is unbounded, so every fixed finite source tuple eventually fits its digit bounds.

## The same witnesses satisfy the stronger interval guard

The full binomial expansion gives

    rho=Y+f,
    f=sum_{i=0}^{R-1} binom(2R,i)/U^(R-i),
    0<=f<2^(2R)/U=b/(2N^2).

The bound is strict because the sum of the displayed positive binomial coefficients is strictly less than 2^(2R), while each denominator is at least U. The construction already has f<1/8 and Y>=1.

`ratio_core`, at `Ratio.lean` lines 88–92, gives

    |C/K-rho| <= 2*rho*R/A
                 =2*(Y+f)/(Y*(U+1))
                 <4/U.

Consequently, since R>=8 and hence 4<2^(2R),

    |C/K-Y| < (4+2^(2R))/U
             < 2^(2R+1)/U
             = b/N^2.

For the source witness 0<g<c, the positive integer g(c-g) is at least 1. The established bounds b,c<=N therefore give

    c^2*(C-KY)^2/K^2 < c^2*b^2/N^4 <= 1 <= g(c-g).

Since K>0, this is precisely Delta=g(c-g)K^2-c^2(C-KY)^2>0. The same canonical witnesses therefore meet both the square-witness restriction and the strengthened interval guard.

## Compact signed threshold

The compact circuit uses the register Nhat=eta*epsilon*B^1201 only through its square. Soundness uses the positive proof-side parameter N=abs(Nhat). Completeness chooses epsilon=2^r>0, so Nhat=N, and the trace above applies verbatim. The compact source proof already establishes b,c<=N and R>=N>=8. Neither the spectator guard nor the exact CRT reparameterization changes omega, U, Y, C, or K.

## Remaining formalization obligation

The existing existential theorem signature alone does not imply that an arbitrary witness it supplies is square. One must replay or strengthen its explicit construction, preserving the displayed omega formula and the sharper approximation estimate. The delivered manuscript explicitly cites the proof construction for this reason. This is a valid ordinary mathematical argument, but a Lean consumer must add a strengthened completeness lemma exposing those properties rather than attempting to deduce them from the present theorem statement alone.

There is no identified mathematical defect, no required circuit change, and no change to the degree or operation count. The existing inherited compiler and object-language proof limitations remain unchanged.
