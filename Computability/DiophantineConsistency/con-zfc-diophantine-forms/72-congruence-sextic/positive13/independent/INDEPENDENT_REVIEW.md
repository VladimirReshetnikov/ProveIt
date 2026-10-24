# Independent adversarial review of the thirteen-positive degree-28 equation

## Verdict and scope

The current literal circuit `pell_research/p13_degree28.json` and ordinary mathematical proof `pell_research/PROOF13.md` pass this review. No new arithmetic gap was found. The assertion is conditional on the identified authentic native-compiler and finite-refutation calibration theorems already used in the repository. This review does not produce a Lean/Rocq certificate, an encoded object-language ZFC derivation, or a proof that ZFC is consistent.

The checked circuit SHA-256 is:

    1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49

`check_independent.py` imports neither the candidate builder nor its verifier. It interprets the literal DAG using an independently implemented sparse Laurent-polynomial algebra over rational coefficients, compares its four residuals with separately stated rational-normalized formulas, checks that all denominators and negative exponents cancel, measures degrees with coefficient ports assigned degree zero, and verifies the sum-of-squares suffix and liveness. It uses only the Python standard library. Its complete receipt is `independent_algebra.json`.

The verified numbers are thirteen positive unknowns; four residual degrees `(13,13,13,14)`; exactly 98 live arithmetic gates (25 additions, 16 subtractions, 57 multiplications); and exact degree 28. These are arithmetic counts with fixed numeral creation free, not bit-operation counts.

## 1. The congruence concealed in the strong root is valid

Write beta = 2^590069 - 1 and b = 3 beta. At a positive input, q = F+alpha+C >= 3 and

    Nf = b f0 + q - beta - 1 >= 2 beta + 2 > 0.

The strong residual says Nf^2 = b^2(1+Delta I^2). Prime valuations, or the reduced-fraction argument for a rational square root of an integer, therefore give b | Nf. Thus

    f = Nf/b is a positive integer,
    q = beta(3j+1)+1,
    J = (q-1)/beta = 3j+1.

If j <= -1, q <= 1-2 beta < 0, contradicting q >= 3; hence j >= 0. Because 590069 is odd, beta = 1 modulo 3 and q = 2 modulo 3. This yields both the authentic radix congruence and gcd(q,3)=1 before any native decoding. There is no premise that a rational J was already integral.

The canonical converse requires J = 1 modulo 3. The actual compact source gives q = B^N with B = 2^590069 = -1 modulo 3 and N odd, so its geometric-sum J has precisely this residue. Its strong root f is larger than q, ensuring f0 = f-(J-1)/3 > 0. This residue promise must remain tied to the whole compact coefficient tuple.

## 2. The first carrier recovers both divisibilities without a positivity assumption

Let M0=q^3(q-1). Its equation is

    Z^2 = M0^2 [ell(ell+k)+1].

The bracket is an integer, so M0 divides Z. Since

    Z = M0(ell+r)+(q-1)Y-q^3 Bt

and gcd(q^3,q-1)=1, reduction separately modulo q^3 and q-1 gives

    q^3 | Y,       q-1 | Bt.

The quotient Bt/(q-1) can have either sign in this argument. Using a signed tau=Z/M0 and subsequently its absolute value is legitimate because the first Pell equation contains tau only through its square. Premature positivity of the transport quotient is unnecessary and would incorrectly narrow the proof.

The supplied positive F,alpha,C already give the packing bounds: q=F+alpha+C and q=beta J+1 imply, with the actual mask inequalities, 3q < R < q^4-2. Thus the old circular dependence on transport positivity has been removed.

## 3. The main carrier's order of use is sound

Set S=4qY and M=qS. Its rational-normalized numerator is

    Dstar=M(X+ac)+H(M gamma+SX-v),  v=k-R-1.

Its norm equation first gives an integer root Dstar/M. This root is positive independently of q|X: since v<k, c>kY, H<5a and MY>5,

    Dstar > Mac-Hk > ak(MY-5) > 0.

The equation therefore gives M | H(SX-v). Here q^3|Y and gcd(q,3)=1 imply gcd(q,H)=1, because H=4(X+1)Y+3. Also H is odd and gcd(Y,H) divides 3. Consequently

    d0=gcd(S,H) divides 3,
    mu=S/d0 >= 4qY/3 >= 4q^4/3 > q^4 > R+1.

Reducing the divisibility modulo S yields mu|v. The necessary modulus is S=4qY, not merely Y: using Y alone would leave a genuine bootstrap problem, since Y is only initially bounded below by q^3 while R can approach q^4.

Both S and M divide 4XY^2 before q|X is known. For M, the quotient is XY/q^2, an integer because q^3|Y. Thus the later first-Pell congruence is compatible with both moduli without circularity.

## 4. Exact main-index recovery uses the normalized strong norm

First Pell classification gives k=2 psi_P(n), P=2XY^2+1. The doubled coefficient is justified by the fundamental integer-coefficient unit for t(t+1): coefficient one is impossible and coefficient two has root 2t+1. No parity of q, X or Y is silently assumed.

The positive main root gives c=psi_A(p), A=a+2. Monotonicity and P>A, c>k give p>n. The case n=1 is impossible because then k=2, eta=zeta=1, c=2Y+1, while p>=2 forces c>=2A>=4Y+4. Hence n>=2, so

    c>kY>=4PY>8XY^3>=8q^9>2R,
    c>2p.

The normalized strong equation is f^2-Delta(ic^2)^2=1. It supplies f=chi_A(m) and psi_A(m)=ic^2. Strong divisibility gives p|m. Writing m=pv0, composition gives psi_A(m)/c=psi_g(v0), where g=chi_A(p). Reducing modulo c gives v0 g^(v0-1). Since gcd(g,c)=1, c|v0, hence pc|m and m>2p.

These are precisely the hypotheses needed by the signed auxiliary-index lemma in package 61. That lemma was read in full: its odd Chebyshev quotient identities, abscissa congruence step-down, and strict intervals yield p=R. It requires no prior q|X, recovered index quotient, positive gamma_old, or large-c hypothesis of the different ordinary-strong lemma.

The auxiliary root V may be signed. The current equation yields the signed norm with y=V+u; the lemma explicitly permits both signs. Both y and V are nonzero because its square coefficient exceeds one. The congruences V=-c modulo f and V=-R modulo c follow exactly from V=f^2(cT-R)-c and f^2=1 modulo c.

## 5. The deferred quotients and signs are recovered correctly

The first Pell recurrence gives k=2n modulo 4XY^2. With p=R and mu|v, it follows that mu divides 2n-R-1. But 1<=n<R<mu, so |2n-R-1|<R<mu; hence 2n=R+1.

Therefore v=k-2n is a positive multiple of 4XY^2, and thus of M. Substitution in M|H(SX-v) gives q|HX, then q|X. The reconstructed w=X/q and h=v/(XY) are positive integers. Also gamma_old=gamma+w-v/M is integral. The positive main norm gives g>(a+1)c and c>X; hence

    H gamma_old = g-ac-X > c-X > 0.

For transport, Bt=q[(K0+w)C-F]. Since q-1 divides Bt and is coprime to q, the quantity

    z_old=((K0+w)C+q-F-1)/(q-1)

is integral. Its numerator is positive because q-F=alpha+C>=2. Thus z_old>=1, which is exactly the required positive source coordinate. The proof correctly allows z_old-1=0; it does not impose a stronger condition on arbitrary zeros.

Taking T_old=fT, tau_old=|Z/M0| and y_old=|V+u| supplies the remaining positive normalized source coordinates.

## 6. Completeness and a simplification of its first-gap dependency

The canonical source yields q=B^N with N odd, R=3 modulo 4, c=psi_A(R), and n=(R+1)/2. The squared-modulus auxiliary reconstruction is valid: for Maux=Delta I, the odd quotient polynomial gives V*=chi_Maux(R)/Maux, y*=psi_Maux(R), and

    V*=-c modulo f^2,     V*=-R modulo c.

As gcd(c,f)=1 and f^2=1 modulo c, T=(V*+c+Rf^2)/(cf^2) is a positive integer. The norm and R>=3 give y*>V*, so u=y*-V*>0.

For the carrier offset r, no separate inherited gap theorem is necessary. Put d=XY^2 and s=Y/q^3<=Y. Since n>=2, k>=8d+4>=8Y^2+4. Writing ell=dk,

    tau^2-(ell+s)^2=ell(k-2s)+1-s^2>0.

For example k-2s>=8Y^2+4-2Y>Y, ell>=Y^2 and Y>=1 make the strict inequality immediate. Thus tau-ell>s. Since the old source already has z_old>=1, t=q(z_old-1)>=0; consequently r=tau-ell-s+t>0. This avoids needing the stronger canonical claim z_old>=2 or w>q>F for this part of completeness.

The gamma offset is also positive by a direct argument: v is a positive multiple of 4XY^2, and therefore

    v/M >= XY/q^2 = wY/q >= wq^2 > w.

So gamma=gamma_old+v/M-w>0 without an additional lower bound on the canonical gamma_old. These improvements reduce the list of genuinely inherited completeness promises.

## 7. Exact degree and literal polynomial

The independent algebra checker verified all four rational-clearing identities exactly over symbolic beta,K0,MC,MF. The residuals have respectively 1921, 5565, 26877 and 81 symbolic monomials, and degrees 13,13,13,14 in the supplied witnesses.

Only As has degree 14, with leading homogeneous part

    -9 beta^2 i^2(eta+zeta)^4 X^2Y^6.

The sum of squares thus has exact degree 28 and leading homogeneous part

    81 beta^4 i^4(eta+zeta)^8 X^4Y^12.

The coefficient of i^4 eta^8 X^4Y^12 is 81 beta^4>0 for the authentic fixed coefficient. No cancellation on that fixed slice can invalidate the degree claim. All thirteen inputs occur in the live circuit. The complete output is the sum of the four checked residual squares.

## 8. Remaining inherited boundary

The reduction itself has been checked as ordinary mathematics. The final consistency equivalence still uses:

1. The complete source-44 compact coefficient adapter, including carry/mask soundness, alignment, actual-rank control, canonical parity, and finite tableau semantics.
2. The normalized source kernel's arithmetic-to-blank-halting soundness and canonical completeness. Its elementary Pell steps are described and audited in source 36's `INHERITED_PELL_AUDIT.md`; the present reduction does not require a conjectural new Pell lemma.
3. The stated calibration from a literal K215 blank halt to a finite refutation in the specified ZFC proof calculus, and conversely.

These are not established by circuit evaluations or finite sample checks. Their complete fixed data and exact source pins must be preserved in the delivered package. The coefficient tuple must remain whole, and MF must remain the already shifted high-mask port.

No numerical check was interpreted as searching for a contradiction or as proving the unbounded equivalence. This internal independent review is not external peer review.
