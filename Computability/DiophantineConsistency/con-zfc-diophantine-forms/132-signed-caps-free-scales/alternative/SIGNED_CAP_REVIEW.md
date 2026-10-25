# Independent review: one signed Pell cap for all seed indices

Reviewed 24 October 2026. This is an ordinary integer-arithmetic proof and a quadratic graph specification, not a claimed Lean formalization or an emitted-coefficient audit.

## Verdict

The proposed theorem is sound and complete. There is no sign, zero-index, or cap-endpoint gap. No seed abscissa or ordinate needs a nonnegativity guard. The cap's abscissa, auxiliary abscissa, comparison base, and all progression quotients may also be signed. The cap ordinate is positive directly from its aggregate equation, so it needs no additional positivity guard.

For the existing scale `A >= (W+1)^W`, the least positive-integer threshold ensuring `A-1 > 9W^3` for every subsequent W is **W=4**. Thus W>=18 has considerable margin.

## 1. Precise theorem and soundness

Let W,A,m be integers with W>=2, 0<=m<=W, and A-1>9W^3. Let each k_i be an integer with 1<=k_i<W. Let x_i,y_i,Q be arbitrary integers. Assume:

1. `x_i^2 - (A^2-1)y_i^2 = 1` for every i;
2. the cap is certified exactly as `V=Y_(2W)(A)`;
3. `V=2W+1+s+sum_i y_i^2`, where s>=0;
4. `sum_i (y_i-k_i)^2=(A-1)Q`.

Then `y_i=Y_(k_i)(A)>0` and `|x_i|=X_(k_i)(A)` for every i.

Classify the absolute-value Pell pair: there is an integer j_i>=0 and a sign epsilon_i in {+1,-1} such that

    |x_i|=X_(j_i)(A),    y_i=epsilon_i Y_(j_i)(A).

This includes y_i=0 by j_i=0; either epsilon_i is harmless in that case. The aggregate cap gives y_i^2<V, hence |y_i|<V (if |y_i|>=V>=1, its square is at least V). Strict monotonicity of Y_j therefore gives j_i<2W. In particular the endpoint j_i=2W is genuinely excluded.

Reduction modulo A-1 gives `y_i == epsilon_i*j_i`. Consequently A-1 divides the nonnegative integer

    E=sum_i (epsilon_i*j_i-k_i)^2.

Every summand has `|epsilon_i*j_i-k_i| <= 3W-2 < 3W`. For m>0,

    0<=E<9mW^2<=9W^3<A-1.

For m=0, E=0 directly. Thus E=0, so epsilon_i*j_i=k_i>0 for every i. Hence epsilon_i=+1 and j_i=k_i. The signs of the x_i never enter the argument; their absolute values are the canonical abscissae.

The quotient Q requires no guard. Its numerator is nonnegative and A-1>0, so any solution in fact makes Q>=0 automatically; the proof only needs the divisibility.

## 2. Canonical completeness, with a strict slack bound

Set `y_i=Y_(k_i)(A)` and choose either sign of the canonical x_i. The index congruence gives `y_i-k_i == 0 (mod A-1)`, so the required Q is an integer.

Put `M=Y_(W-1)(A)^2>=1`. Then `sum_i y_i^2<=mM<=WM`. The Pell doubling identity and positivity give

    Y_(2W)=2X_W Y_W > 2(A-1)Y_W^2 >= 2(A-1)M.

Indeed `X_W^2-(A-1)^2Y_W^2=2(A-1)Y_W^2+1>0`, so `X_W>(A-1)Y_W`. The assumed scale implies A-1>=2W. Therefore

    Y_(2W)>4WM >= WM+2W+1 >= sum_i y_i^2+2W+1,

where `3WM>=3W>=2W+1` uses W>=1. Thus the slack is not merely nonnegative: it is a positive integer. Every canonical seed family extends to the aggregate cap.

## 3. Exact scale threshold

For W=1,2,3, the differences `(W+1)^W-1-9W^3` are respectively -8,-64,-180. For W=4 the difference is 48.

Induct on W>=4. If `(W+1)^W>9W^3+1`, then

    (W+2)^(W+1) > (W+2)(W+1)^W > (W+2)(9W^3+1)
                         > 9(W+1)^3+1.

The last inequality follows from `W+2 > ((W+1)/W)^3` (already true for W>=2) and W+2>1. This proves the claimed least threshold 4.

## 4. A single cap certificate with every abscissa and progression signed

Let K=2W. Use unrestricted integer variables C,H,J,B,S,R,d,e,f,g,r. Impose

    C^2-(A^2-1)V^2=1,
    H^2-(A^2-1)J^2=1,
    S^2-(B^2-1)R^2=1,
    J=V^2*(2e+1),
    B=1+4V*d,
    B=A+H*f,
    S=C+H*g,
    R=K+4V*r.

The aggregate cap already gives V>=K+1>1. Since 2e+1 is a nonzero integer, |J|>=V^2>1. Thus |H|>=A>=2, and V^2 divides J. The inherited signed-comparison theorem explicitly permits a signed auxiliary ordinate J, so no sign hypothesis on e or J is needed. The potentially signed B is never degenerate:

- If d!=0, `|B|>=4V-1>=3`.
- If d=0, B=1 would imply H divides A-1, impossible because `0<A-1<|H|`.

Hence |B|>=2. The parent's stronger argument is also correct: |J|>1 implies the auxiliary Pell index is at least 2, so `|H|>=2A^2-1>A+1`, and B=A+Hf itself excludes B=-1,0,1.

Apply the inherited signed-comparison index proof with main abscissa |C|, auxiliary modulus |H|, and comparison abscissa `sign(C)*S`. Reflecting S alone preserves its norm and makes it congruent to |C| modulo |H|. C is nonzero by its norm. All congruences modulo H remain valid modulo |H|.

For signed B, use the polynomial Pell recurrences at integer B. At a negative base,

    X_h(-a)=(-1)^h X_h(a),
    Y_h(-a)=(-1)^(h-1)Y_h(a)  for h>=1,

and Y_0(-a)=Y_0(a)=0 separately. Classification at |B| therefore yields independent signed X_h(B),Y_h(B). Polynomial base-congruence transfer and `Y_h(B)==h (mod B-1)` hold at negative B as well. The original proof consequently still gives `h==+/-i (mod 2n)` and `h==+/-K (mod 4V)`, and its unchanged short-interval step yields i=K. Thus `V=Y_K(A)` and `|C|=X_K(A)`.

This signed-base extension is already present in the inherited ordinary research note:

    inherited/direct/repository/research/comparison-base-sign/README.md

The independent main-root reflection appears in:

    inherited/direct/repository/research/main-root-and-modulus-signs/README.md

### Explicit completeness of this cap certificate

No new selection principle is needed. For the canonical V=Y_K(A), C=X_K(A), the even index K=2W gives

    V=2X_W(A)Y_W(A),          C=2X_W(A)^2-1.

Thus V is even and C is odd, for every integer A>=2. Choose the positive Pell pair at index `n=KV` and call it (H,J). The composition identity gives

    J=V*Y_V(C).

The polynomial/binomial formula at base C gives an integer T with

    Y_V(C)=V*C^(V-1)+(C^2-1)T.

Here `C^2-1=(A^2-1)V^2`, so

    J=V^2*(C^(V-1)+(A^2-1)*V*T).

Consequently `J/V^2` is an odd positive integer: its first term is odd and its second term is even. Set `e=(J/V^2-1)/2`, an integer. This supplies the odd auxiliary quotient without any nonnegativity witness.

Also n=KV is even, so H is odd by `X_(2j)=2X_j^2-1`. Pell's norm and V|J imply gcd(H,V)=1, hence gcd(H,4V)=1. The elementary CRT chooses B>=2 with B==A modulo H and B==1 modulo4V. Put `S=X_K(B)`, `R=Y_K(B)`. Polynomial base-congruence transfer gives H|(S-C), and base-one reduction gives4V|(R-K). All progression quotients are integers. This supplies witnesses for every displayed equation.

This odd-quotient construction uses the even cap index. It is not a claim that every indexed-Pell certificate admits an odd quotient without further analysis. For this cap, it is fully constructive and replaces the earlier positive-factor certificate, removing three guard witnesses and one quadratic residual.

## 5. Economical quadratic graph

Use the universal nonnegative ternary form

    N(a,b,c)=a^2+b^2+c^2+c.

It is always nonnegative over the integers. Every nonnegative integer occurs: apply the three-square theorem to 4n+1; its square residues modulo4 force two even coordinates and one odd coordinate, giving the displayed representation after division by4. Thus one can eliminate the separate cap slack s entirely:

    V-2W-1-sum_i y_i^2-N(a,b,c)=0.

This is already quadratic and costs just three unrestricted witnesses. Do not add a V, seed-y, seed-x, C, H, B, d, f, g, r, or Q nonnegativity guard.

The auxiliary factor 2e+1 requires no guard. To keep every equation quadratic, add the product variables

    p_i=A*y_i,
    pC=A*V,    pH=A*J,    pB=B*R,    L=V^2.

Replace the norms and auxiliary product by

    x_i^2+y_i^2-p_i^2-1=0,
    C^2+V^2-pC^2-1=0,
    H^2+J^2-pH^2-1=0,
    S^2+R^2-pB^2-1=0,
    J-L*(2e+1)=0.

Keep the four displayed progression equations and the aggregate congruence equation unchanged; they too are quadratic. This gives an explicit system of `2m+14` quadratic equations in `3m+20` signed integer variables, apart from the already existing A,W,k_i parameters. Equivalently, if x_i,y_i already exist, the construction adds m+20 variables. These are local graph counts, not a count for any complete downstream source or quartic emitter.

For the count, the 20 non-seed variables are

    V,C,H,J,B,S,R,d,e,f,g,r,L,pC,pH,pB,Q,a,b,c.

The sum of squares of all these quadratic residuals is quartic and vanishes exactly when the system holds. No absolute value or sign operation appears in the polynomial graph; those operations are proof-only parameters.

## 6. Scope and audit cautions

- W and k_i positivity/bounds and the scale A-1>9W^3 must be established independently of the seed indices being decoded. Otherwise a circular bootstrap is possible.
- The aggregate congruence is a sum of the actual `(y_i-k_i)^2`, not a sum with arbitrary mixed cross-terms or coefficients of unknown sign.
- Canonical completion requires one common cap at index2W, not an unindexed Pell ordinate asserted merely to be large.
- All seed x_i signs remain free after this theorem. Any later power-extraction step that needs positive x_i must prove or enforce that orientation separately. This theorem concludes only |x_i|.
- The complete arithmetic proof is Sections1–4. Finite tests support implementation but are not a substitute for the unbounded argument.

## 7. Review of the complete 355-variable manuscript and odd-quotient delta

I read the full `/workspace/shared/diophantine_wave16/alternative/PROOF.md` supplied on 24 October 2026. I found no critical mathematical issue in its signed-cap argument, prerequisite ordering, or nineteen-power orientation argument. In particular the base-1 negative-root exception is correctly handled before claiming all power meanings. This is a mathematical review of the supplied text, not a fresh coefficient/row audit of that complete artifact.

The old manuscript must be updated consistently when applying the odd-quotient optimization: replace its auxiliary product by `J=V^2(2e+1)`, remove only the e>=0 guard and its three representation variables, use |J| rather than J in the auxiliary nonzero/bound argument, and replace its completeness paragraph by the even-index construction in Section4 above. References to two new nonnegative guards become one. The claimed complete count is then reduced by three, conditional on the emitter and projection audit confirming that no other change occurs. The local quadratic graph loses one residual. No global 352-variable coefficient/support/height claim is made by this review before regeneration.
