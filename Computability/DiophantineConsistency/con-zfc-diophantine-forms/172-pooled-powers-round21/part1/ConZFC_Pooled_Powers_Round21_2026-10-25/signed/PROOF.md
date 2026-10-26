# Strict-horizon pooled certificates with an odd beta multiplier

This is the complete ordinary proof of the new semantic and algebraic changes. The source is the literal 239-coordinate Strict Horizons source, `inherited_strict/direct/source/equation.json`, together with its retained ordinary source proof `inherited_strict/report/main.tex` and the retained factorial-free/C222 calibration closure. These are not inferred from numerical sampling. The final equations are quartics over unrestricted integers. We do not assert a newly compiled Lean/Rocq theorem, absolute minimality, or the truth of consistency.

## 1. Exact source interface and independent order

The source has t=16+h², F=t^t, CRT radius F, proposed B=binom(F+t,t), affine q=4z+1, and original beta spacing y=F(2v+1)². Actual CRT representatives are C and eight A_j; H=2+C+sum A_j. The source keeps the integer endpoints

    x=F+1+(y+1)u0,    x=1+[1+(t+1)y]ut,

and the raw index row BhB=C+F+1. All these displayed powers and binomials are semantic notation for the retained literal quadratic graph, not extra operations in the final polynomial.

The source proof establishes, before using signs of these arithmetic registers, the squared semantic anchor, the deterministic comparison center and all fourteen canonical signed Pell pairs. Its actual-atom frame is exactly W=2+sum of 34 squares. The actual atoms are t,F+t,x,y+1,F,B; the eight A_j and C; N=B^x and J(A_j,C); q and q+1; BH; and the fourteen retained outputs of requests 3,4,5,7,...,17. Thus every base, index and output of all seventeen requests has square strictly below W; t² is present and t≥16 gives W≥258. The frame's center A satisfies |A|>W^W. Repeated atoms need not be listed twice. In the literal source the variable named y stores actual y+1, the variable for A_a stores A_a+1, actual q=4z+1 and q+1=4z+2. The finite checker reconstructs all squares with these offsets, rather than assuming a meaning from a name.

## 2. Two quadratic equations for a fixed nonzero base

Let n≠0 be a shared base of r≤15 requests, with n²,m_i²,k_i²<W. Let (X_i,Y_i)=(X_{k_i}(A),Y_{k_i}(A)) be the already canonical signed Pell pair and Z_i=AY_i the retained multiplication wire. Put

    T=2An-n²-1, H0=sum Y_i(m_i-X_i),
    S0=sum [(m_i-X_i+Z_i)²-Y_i²].

Introduce exactly two unrestricted integer coordinates K,L and impose

    K-2H0-(2A-n)L=0,    S0-nK+L=0.                 (P)

Every expression in (P) is quadratic because Z_i is an existing coordinate. No modulus or aggregate coordinate is added. Eliminating K gives S0-2nH0=TL. Direct expansion using Z_i=AY_i gives

    sum [m_i-X_i+(A-n)Y_i]²
       = S0-2nH0-T sum Y_i²
       = T(L-sum Y_i²).

Modulo T, n is a unit because T=-1 modulo n. The Pell recurrence sends X_k(A)+(n-A)Y_k(A) to n^k for every signed k, interpreting negative exponents in this residue ring. Let b=floor(sqrt(W-1)); then b≥16 and |n|,|m_i|,|k_i|≤b. Multiplying by n^{2b} proves that T divides the ordinary nonnegative integer

    E=sum [m_i*n^b-n^{b+k_i}]².

All b+k_i are nonnegative. Each inner absolute value is at most b^{b+1}+b^{2b}≤2b^{2b}. Hence

    0≤E≤4r*b^{4b}<W^{2b+1}≤W^W.

Here 4r≤60<W, b²<W and 2b+1≤b²+1≤W. Meanwhile |T|≥2|A|-W>|A|>W^W. Consequently E=0 and every summand is zero. If |n|≥2, a negative k_i would give m_i*n^{-k_i}=1, impossible; therefore k_i≥0 and m_i=n^{k_i}. For n=±1 the exact signed-index unit value is recovered, without inferring an index sign.

Conversely, for genuine powers with canonical Pell pairs every individual error is divisible by T. Put L=sum Y_i²+(sum error_i²)/T and K=2H0+(2A-n)L. They are integers and both rows (P) vanish. Thus the pooled certificate is sound and complete for this finite family under the independently retained frame/canonical-pair interface.

We apply it to eleven requests at q+1 and three at q, keeping the separate requests at t, B and BH. Each group replaces r private congruence quotients and one modulus coordinate by K,L, saving r-1 coordinates and rows: ten plus two. All retained AY rows, norm rows, source congruences, affine offsets, and group memberships are authenticated literally.

## 3. Odd beta spacing and the widened remainder sphere

Replace the original multiplier s=(2v+1)² by s=2v+1, retaining y=Fs. This affine relation permits exact elimination of s. In the centered source it is the replacement of -1+s-4v-4v² by -1+s-2v. This is a semantic extension followed by a monic integral projection, not a claim that every new v is an old square.

The common eleven-remainder row originally is

    M²=1+4 sum rho_j²+G(a,b,c),    G=a²+b²+c(c+1).

Replace coefficient 4 by 2 and KEEP constant 1:

    M²=1+2 sum rho_j²+G(a,b,c).                  (S)

G is nonnegative for all integers and represents every nonnegative integer. Indeed the three-square theorem represents 4n+1; its three squares have exactly one odd entry modulo 4, giving (2c+1)²+(2a)²+(2b)²=4n+1. Equation (S) implies M≠0 and |rho_j|<|M|/sqrt(2)<3|M|/4. The constant 1 must not be silently removed: this branch does not use the different signed-factorial nonzeroness proof from Round 20.

For a normalized row Dv=M, vU=MQ+rho, nonzero D,M imply nonzero v. The identity gives v|rho, so r=rho/v is an integer, U=DQ+r, and |r|<3|D|/4. No sign of D, v, M or rho was assumed.

## 4. Noncircular signed bootstrap

The unpooled t request and t≥16 first give F=t^t>2^32. The odd beta spacing then gives |y|≥F>1; DO NOT yet assert y>0. Since q=4z+1, q≠0 and |q+1|≥2. Apply the q+1 pool immediately: every actual representative and derived-label index is nonnegative and every corresponding numerator is exact. In particular C,A_j≥0 and H≥2. The index row BhB=C+F+1 makes B≠0. Thus |BH|≥2, and its unpooled request gives x≥0 and q=(BH)^x.

If x=0, the last beta endpoint says 0=1+[1+(t+1)y]ut. But |1+(t+1)y|≥(t+1)F-1>1, so it cannot divide -1. Hence x≥1 and |q|≥2. The q pool now forces exact q^t,q^{y+1},q^x and nonnegative indices. In particular y+1≥0. Combining y≥-1 with |y|≥F>1 proves y≥F>0. This is the first justified use of its positive sign. The ratio q^t*v=q^x also gives x≥t.

If u0≤-1, the first endpoint would give x≤F-y≤0. Thus x≥F+1>1, ut≥1, and x≥2+(t+1)y≥2+(t+1)F. Every denominator exponent is at most x. Writing Q=|q| and b=|B|, Q=|BH|^x≥2^x and b<Q/2. Neither B nor q has yet been assumed positive.

For n=F+t and 0≤j≤t, C_j=binom(n,j)≤(F+t)^t≤(2F)^t≤2^{t(F-1)} because 2F≤2^{F-1} for F≥4. Since Q≥2^{2+(t+1)F}, C_t<Q/32 and max C_j/(Q-1)<1/32. The signed low tail r0=sum_{j<t} C_j q^j satisfies |r0|<Q^t/32 even if q<0. Its congruence and the restored factorial-carrier digit row imply r-r0 divisible by q^t and

    |r-r0|<(3/4+1/32)Q^t<Q^t.

Therefore r=r0. Subtract, divide by q^t, and reduce modulo q to get B=C_t modulo q. Since |B-C_t|<Q/2+Q/32<Q, B=binom(F+t,t)>0. Now H≥2,x≥1 give q=(BH)^x>0. All formerly signed power meanings have their ordinary positive interpretation.

For every remaining true low digit the unchanged source bound is 0≤r0<D/32. The same divisible-difference argument with radius 3D/4 recovers the exact low tail. It restores all earlier interval witnesses (0≤r<D), not just necessary congruences. The strict binomial ranges decode the original bounded rows exactly.

## 5. What the retained arithmetic proves thereafter

No later source hypothesis has been weakened. The above reestablishes t≥16,F=t^t,y≥F,x≥2+(t+1)y, B=binom(F+t,t)>0,q>0 and every exact digit/range. The source's lcm bound Lambda_t≤4^{t-1} yields Lambda_t²<F, so the linear CRT radius is valid. Its every-prime compatibility and every-row large-selector lemmas apply unchanged. The fixed majorants E=8388608 and ell=4194304 still give (2+t+x+y+F)^E<2^x and the derived-label bounds; positivity was proved before invoking them.

After decoding, y=F is impossible: its first accumulator would be zero, positive weights propagate zero, and the last endpoint has accumulator one. Hence y>F, and the multiplicative Horn balance follows. At F=t^t, the retained self-power separation lemma recovers label multiplicities (its coefficient differences are strictly below F even when an individual coefficient equals F). Single-conclusion closure gives a finite C222 refutation. The retained ordinary calibrations `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation` give a finite ZFC refutation. The entire retained proof/source closure is shipped, not replaced by this paragraph or by the finite Python checks.

## 6. Constructive completeness

Begin with any finite calibrated C222 refutation. The retained Strict Horizons construction chooses a cofinal t=16+h² strictly beyond all finitely many local parameters, derived labels and the tree length, with h even for the source's B-odd CRT/Pell completeness. It builds F=t^t, B, positive y=F(2v_old+1)², sufficiently large beta code x, CRT representatives and canonical Pell/frame data in the stated source order. These are the original source witnesses.

Set v_new=((2v_old+1)²-1)/2, an integer. Then y=F(2v_new+1), so the new beta relation preserves the actual y and every frame atom. Keep every source arithmetic value, power and normalized remainder. The source has |rho_j|<M/32 for all eleven rows. Thus 2 sum rho_j²<22M²/1024<M². The integer M²-2sum rho_j² is positive and at least 1; hence M²-1-2sum rho_j²≥0 and a G representation fills (S). The converse part of the pool theorem supplies its four new integers. No unit-base or sign obstacle occurs in these positive witnesses. The exact transformations below then give the final coordinates. This proves completeness without assuming the truth of Con(ZFC).

## 7. Exact algebraic simplifications and inverse maps

Private-wire aggregation first replaces U=s0²,V=g², with only their common consumer coefficient, by J0=s0²+g². Backward restore U=s0²,V=J0-s0²; forward J0=U+V. It replaces three private factors 1+Fb,1+F(a-1),1+Fd, d=6a+8b+2p, by one common product J=FS while keeping K=FS'. The consumer rows become -S'-Kb+vw+w0, -S-J(a-1)+w1, and S+Jb-S'-Kd+w2. Restore each removed factor by its polynomial. Their source residuals are respectively new69+b*(K-FS'), new72+(a-1)*(J-FS), and new74-b*(J-FS)+d*(K-FS'). The corresponding forward residual identities are old69+S'*old68-b*old54, old72+S*old70 and old74-S*old68+S'*old73-d*old54. The literal general certificate checks every affected and unaffected row in both directions, with actual source indices rather than these historical labels. This saves three variables/rows.

For each canonical pair replace X by D=X-Z with inverse X=D+Z, respecting all stored offsets. Subtract the fourteen retained Pell norm rows from the orientation row. The pooled norm becomes sum[(m-D)²-Y²], and every old row is recovered by the inverse shear and inverse row operation. This changes support, not the number of witnesses.

Every transported core operation is either an integer coordinate shear x_j(old)=x_j(new)+k*x_i(new), an invertible row operation R_i←R_i+kR_j, or a monic projection v=f with integral degree≤2 restoration. A quadratic f is used only when every other occurrence of v is linear. The stored finite operation list verifies the defining row and every degree bound at application time; no operation is accepted merely because it existed in Round 20.

For a common Hessian-kernel direction d, each quadratic row satisfies R_i(x+sd)=R_i(x)+s lambda_i. If d_p=1 and lambda_r=±1, choose coordinates x_j=z_j+d_j s (j≠p),x_p=s. Row r uniquely gives s=-R_r(z)/lambda_r, an integer quadratic polynomial. Every other row is exactly R_i(z)-lambda_i R_r(z)/lambda_r, still quadratic. These formulas give the inverse lift and the projection in both directions. The final low-height core exposes two further such directions; exact Hessian equations and unit slopes are checked, not just numerical tests.

One optional dimension projection uses an exact integer linear combination of residuals whose affine result has a unit coefficient on one coordinate. Substitute its integral affine solution and omit any row with nonzero combination coefficient. The omitted row follows because that nonzero integer times the residual is zero in Z. This requires no division of a witness by a nonunit. Finally integral row-basis operations change the sum-of-squares polynomial but preserve the simultaneous zero set.

## 8. Conclusion and delivered scope

All algebraic transformations above preserve existence of an integer zero exactly. Sections 2--6 give soundness and completeness of the semantic delta against the calibrated strict source. A sum of squares over the integers vanishes exactly when all its residuals vanish. Therefore ZFC proves for each delivered literal polynomial P:

    (exists integer tuple x, P(x)=0) iff a finite ZFC refutation exists.

Negating proves the requested equivalence between integer unsolvability and syntactic Con(ZFC). Full coefficients, exact source pins, forward/reverse finite identities, deterministic reconstruction and independent optimized/nonoptimized checks accompany the ordinary proof. These finite audits neither prove consistency nor replace the quantified arithmetic and retained syntax calibration.
