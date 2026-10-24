# Independent review: centered-budget12 and bounded-guard absorption15

## Verdict and exact scope

**PASS for the new local mathematical reductions and the supplied literal polynomials. No blocking defect found.** The final reviewed guard construction is the early-rational-projection version, not the superseded v-squared/Lambda version:

- Twelve unrestricted integers, exact total degree **1000**, **180** live binary arithmetic gates.
- Twelve-integer auxiliary-only companion, exact degree **1024**, **179** gates.
- Fifteen unrestricted integers with bounded-guard absorption, exact degree **176**, **125** gates.

The degree/gate figures are exact for these literal circuits with the six supplied fixed coefficient payloads. They are not lower bounds on every possible representation. All files reviewed are pinned in the two receipts. Neither this review nor the finite checks reprove the inherited source34 native/compiler and finite-syntactic-refutation calibration, provide an end-to-end kernel certificate, prove consistency, or establish a worldwide optimum. The conclusion is the ordinary mathematical composition with those explicitly identified inherited theorems.

## 1. Universal guard12 proof audit

### Exceptional inputs and the reality bootstrap

The fixed beta and the restriction Jold=6j+1 imply q even, q=2 modulo 3, and |q|>=16 on every integer input. W=12w+4 is nonzero, |X|>=64, and X=2 modulo 3. If v=0, a=0, Delta=3 and H=3; otherwise |a|>=1008. Thus Delta is positive and odd and H is nonzero without any Pell decoding. Also a=0 modulo 3, H=0 modulo 3, b0=2 modulo 3. Since H=3 modulo q and H is odd, gcd(H,2q^2)=1.

For c=0, Q=0, delta=-1 and Dy=1. For c!=0, Q>1, Df>|c|+1, and the integer b=cT-R makes V=Df*b-c nonzero. Hence Dy=V^2+(V^2-1)/(Q-1)>=1. Df and Dm are positive; Dt=1+t(t+1)k^2 is positive for integer t=XY^2. Consequently the guard radical is the only possible nonreal term of a vanishing norm factor. Ag<0 is impossible. Thus B=Ag+1+p2^2+p3(p3+1)>0 before any individual root is assumed rational. This establishes k!=0 and |eta/k|<1/2 without excluding v=0 by assumption.

### Early rational projection is valid

In a rational sum of radicals with rational squares, independence of the distinct squarefree radical classes forces the result to equal its squareclass-1 part. An integer-radicand term contributes either zero or an integer to this projection. The auxiliary term has the same property: if its root is rational, it is integral by the adjacent-coefficient lemma, including the globally available Q=0 case above.

For Q>1, writing y=a/s in lowest terms gives s^2|(Q-1), so (Q-1)y is integral. The stated transformation preserves QV^2-(Q-1)y^2, keeps V integral, and preserves reduced denominator s because 2Q-1=1 modulo s. When |V|>1, y>|V| and (Q-1)y<Q|V| give -|V|<V'<|V|. The norm excludes V'=0. Induction ends at |V|=1, where |y|=1. This is a genuine universal descent, not an inference from tested Pell solutions.

After division of the vanishing factor by M, every coefficient of a radical is an integer. Its rational projection shows Z/M is an integer even if some irrational terms cancel. Thus M|H(v-q^2), and coprimality restores v=q^2(2v_old+1). This obtains the full cubic Y scale and v!=0 before extracting the roots.

Project the undivided factor next. Were the main root irrational, its projection would vanish, implying H|Z. But Z=M*b0 modulo H and M*b0=1 modulo 3, whereas H=0 modulo 3. This is impossible. The actual signed main root is therefore an integer; projection modulo H then gives H|M(d_s-b0), hence gamma=(d_s-b0)/H is integral. The proof does not incorrectly conclude that every other root is already rational.

### Four-root separation and signs

After scale recovery, x=|X|>=64, m=|Y|>=4096, K=|k|>=1, and K(m-1/2)<|c|<K(m+1/2). The stated inequalities are valid for K=1. In particular t>3|c|, d>(3/4)t, f>(|c|-1)d>2t, and f>3|c|^2. The unmultiplied guard gives g<|q|K and g<|c|/255.

When b=0, V=-c and Q>|c|^2 give |c|<y<|c|+1. Therefore y>g and t>y+g, and f>t+y+g. The order f,t,y,g is genuinely superincreasing, omitting a zero g. When b!=0, |V|>=f^2-|c|>2f and y>=|V|, giving the order y,f,t,g. A largest term in any nontrivial squareclass cannot cancel all smaller terms in that class. Thus all four roots are rational; the integer radicands and adjacent descent make them integral. This works with arbitrary factor signs and negative original coordinates.

The earlier v-squared construction used a valid two-root terminal-block argument: after the three large roots are extracted, nonintegral y^2 versus integral g^2 forbids irrational terminal cancellation. The final construction no longer needs that special argument, because the early scale projection makes g much smaller than y.

### Exact source restoration and completeness

The pointwise restoration is to the actual copied centered-budget17 packet: J3=2j, v_scale=v_old, w3=w, f=f_s, tau=t_s-L, y=y_s-V, with the recovered gamma and unchanged h,r,T,c,z. The native F and alpha restore transport and R exactly. The first and auxiliary source rows are precisely the stated integral translations; the signed main root gives the main row; the normalized strong row gives the same Q and V; and B=1+p1_s^2+p2^2+p3(p3+1) gives the source positivity row directly. No stronger determinant inequality is assumed.

Completeness uses the same canonical source34 family and its prescribed Y. The odd, 1-modulo-3 repunit permits j=(Jold-1)/6, and the normalized strong/auxiliary completion leaves the native coordinates and centered budget unchanged. The universal Pos representation follows from the three-square theorem applied to 4B-3, which is positive and 1 or 5 modulo 8. The single carrier n=gamma+f+t+p1+y-V-S-v_old is integral and makes the displayed factor zero. S independent of n is a genuine integral fiberwise shear, with inverse subtraction. No freely adjustable Y, sign branch, or missing congruence is inserted.

## 2. Universal absorption15 proof audit

The completed-square identities give G<=q^2/3 and Zeta<=k^2/4. They do not alone justify multiplying inequalities when G or Zeta is negative; the proof correctly treats all sign cases. If GZeta<=0 the pre-positivity expression is nonpositive. If both are negative, writing them as -g,-z gives t^2+g+z+1, whose square exceeds gz. If both are nonnegative, their product is bounded by q^2*k^2/12. Therefore B<=q^2*k^2/12-1 universally.

The exact parity norm forces B_guard to be an odd integer square even before the residuals vanish. The signed-squareclass argument works with negative radicands and with Caux=0: the A coefficient is odd, the B coefficient is twice an odd integer, and the C coefficient is divisible by four. In each nontrivial squareclass, its first present level cannot cancel. A zero C term is simply absent. Hence B_abs>=0.

If qk=0, the universal bound makes B_abs negative. Otherwise any nonzero integer residual gives S=r_main^2+r_strong^2>=1, and B_abs<=q^2*k^2(1/12-S)-1<0. Thus both retained residuals vanish before any use of the strong row to exclude Q=1. Only now is the parent's Delta>1 and strong-row divisibility invoked. The auxiliary rational root then becomes integral by the same adjacent lemma, with Q=0 covered separately. The three private coordinates restore all five literal parent rows. Conversely, every parent zero has penalty zero and supplies the incoming parity carrier. This is an equivalence for every parent zero, not merely canonical witnesses.

## 3. Independent executable evidence

Run from the package root:

    python review/budget/audit_budget.py
    python -O review/budget/audit_budget.py

The auditor imports no author builder or auditor. It uses SymPy's integer sparse polynomial ring (tested with SymPy 1.14.0) and explicit exceptions, not removable assertions.

It independently multiplies all 32 formal sign factors and reduces even root powers, obtaining 20,349 monomials. Both literal guard DAGs match this full generic polynomial at their seven-input norm cuts, including exact delta^16 denominator clearance. Each guard's 43 outer-register cuts is separately verified. A separate eight-factor expansion verifies the parity identity as a 98-monomial polynomial, including degenerate radicands. The absorption packet and its DAG match at 36 exact local cuts. All live inputs, fixed ports, gate syntax, topology and operation counts are checked.

For guard degrees, actual register weights are checked, and independent exact expansion in the inner rank-four algebra gives weighted component degrees (250,240,247,243) for the centered case and (256,238,245,243) for the companion. Strict scalar dominance proves the respective 1000 and 1024 upper bounds after taking the four-conjugate product. The absorption max-plus upper bound is 176. Independent finite differences on a different fixed-coefficient line give the nonzero leading coefficients 268095725, 907282306 and 215929316 modulo 1000000007, respectively. Together with the upper bounds, these are exact degree certificates, not probabilistic identity tests. The slopes and payload hashes are in the receipts.

The auditor also checks generic translation, CRT-carrier, Pell-descent and guard-bound identities, authenticates every retained source pin, and checks exact equality of the six active payloads with both centered source copies and the absorption binding.

## 4. Negative controls and limits

The receipts retain deliberately invalid relaxed examples, not claimed source-polynomial zeros:

- Leading magnitude separation alone allows a terminal sqrt(2)-sqrt(2) cancellation.
- Two negative radicands can cancel, showing why unique-imaginary-root reasoning requires all other radicands positive.
- Without the modulo-3 obstruction an irrational main root can survive projection.
- Dropping the absorption penalty admits an odd square guard with a nonzero retained residual.
- A=1,B=1,Caux=0,t=1 is a genuine parity-norm zero, showing why early exclusion of Caux=0 would be circular.
- Replacing adjacent coefficients by arbitrary ones allows a nonintegral rational Pell ordinate: 5*1^2-16*(1/2)^2=1.

These controls detect tempting false shortcuts. The unbounded arguments above, not finite sampling or these controls, justify soundness and completeness. The substantial inherited compiler/calibration theorem remains the explicit semantic boundary.
