# Independent audit: even-main-rank free83 nonextension

Date: 2026-10-04 UTC
Verdict: **PASS for the stated arithmetic theorem**, including nonsquarefree Delta.

## Exact proposition audited

Let A>=4 be even, Delta=A^2-1, p>=2 be even, c=psi_A(p), and R be odd. Let the five retained source factors have product P5=1. Then no positive integers f,S,T,y satisfy

    V=c(Tf-1)-Rf^2,
    Na=S^2 V^2-(S^2-1)y^2,
    Ns=Delta f^2-S^2,
    Na Ns=Delta.

V is an unrestricted-sign integer, not a separately positive witness. The theorem checks both signs of V and both signs of Na and Ns. It requires no squarefreeness hypothesis on Delta, no hypothesis that the strong Pell unit is a power of A+sqrt(Delta), and no generic unit normalization of the five outer factors.

The theorem is slightly stronger than a claim about one counterfamily: it applies to every outer tuple with the displayed invariants. It does not classify generic free83 zeros, prove their ordinary-input soundness, or exclude completions obtained by changing the retained outer tuple so that these invariants fail.

## Independent checks of the mathematical argument

1. **S=1 boundary.** If S=1, Ns=Delta f^2-1 is positive, exceeds 1, divides Delta, and is coprime to Delta. This is impossible. Thus the small-norm lemma is applied only with H=S^2>=4.

2. **Small-norm import and signs.** I read the recovered, immutable Report43 early auxiliary norm proof rather than execute its scripts. Its only product input is |Na Ns|<=Delta, which is satisfied here with equality. Its descent applies to v=|V|>=0 and y>0. If Na>0, then Na<S^2 and is a positive square z^2. If Na<0, the argument forces f=1, S=A, Ns=-1 and Na=-Delta. The equality orbit has V=+/-2Delta psi_(2A^2-1)(r), including r=0. There is no unhandled V=0 or small-S case.

3. **Correct nonsquarefree Pell lattice.** Write Delta=d b0^2 with d squarefree. Since Delta=3 mod4, d=3 mod4 and b0 is odd. If a+b sqrt(d) is the least positive integer Pell unit, every positive unit is its integer power, so A+b0 sqrt(d)=(a+b sqrt(d))^e. If a were odd then b would be even, and every power would have odd first coordinate. Therefore a is even, b is odd, and e is odd. Setting C=psi_a(e) and delta=a^2-1=d b^2 gives b0=bC, Delta=delta C^2, and C psi_A(t)=psi_a(et).

4. **Normalization, with no squarefree shortcut.** For every m>=0, gcd(chi_a(m),b0)=1. Coprimality with b follows directly from the norm. If an odd prime l divided chi_a(m) and C, then u=a+s in F_l[s]/(s^2-delta) would satisfy u^(2m)=-1 and u^(2e)=1. Exponentiating by e and m gives a contradiction because e is odd. This argument only needs a ring, and remains valid when its quadratic polynomial is reducible or repeated modulo l. The prime 2 is excluded by b0 odd. If Na=z^2>0, then z^2|Delta implies z|b0. Multiplication of the strong equation by z^2 makes (zf,zS) a strong-Delta solution, whose first coordinate is chi_a(m). Thus z=1. This is the needed proof that all positive divisor branches collapse to Na=1,Ns=Delta in this interface.

5. **Opposite-parity residues.** For F=chi_a(m), m>=1, the coefficientwise identity u^(2m)=-1 modulo F reduces every psi_a(t) to +/-psi_a(j), with 0<=j<=m and j congruent to t modulo2. Reflection about 2m preserves both parity and the psi residue. The endpoint bounds are sufficient: for m>=2, psi_a(m)+psi_a(m-1)<F. Consequently representatives at distinct-parity indices have a nonzero difference of magnitude <F, and their sum is positive and <F. They cannot agree up to sign. For m=1 the residues are 0 and 1 modulo a>=2, also distinct up to sign. Zero representatives are covered.

6. **Literal auxiliary congruence.** From Na=1 and y>0 one has V=epsilon chi_S(t)/S for t>=1 odd, epsilon=+/-1. Here S+sqrt(S^2-1) really is the least positive integer Pell unit: any solution with positive second coordinate has first coordinate at least S. The odd quotient identity and S^2 congruent to -Delta modulo f imply psi_A(t)=+/-psi_A(p) modulo f. Strong-Delta solutions have f=chi_a(m), m>=1; multiplying by C gives psi_a(et)=+/-psi_a(ep) modulo chi_a(m). The two indices have opposite parity since e,t are odd and p is even, contradicting item 5. Neither gcd(C,f)=1 nor division by C modulo f is needed. The actual proof only multiplies by C. R disappears in this reduction.

7. **Negative branch.** Its equality orbit makes V even. The literal formula with f=1 instead makes V=c(T-1)-R odd, since psi_A(p) is even for every even p and R is odd. This excludes the entire negative branch, including V=0.

These cases exhaust Na Ns=Delta>0. I found no counterexample or logical gap.

## New82 application and source boundary

The original /workspace/shared/square-product82-counterfamily-20261004 directory was absent in this executor during the audit. Therefore this audit independently certifies the arithmetic theorem and its conditional application to any new82 member having A even, c=psi_A(p) with p even, R odd, and P5=1. It does not independently certify the construction of those outer tuples from an unavailable original counterfamily artifact. The author and parent report that the fixed family has the stronger invariants p=0 mod4 and R=3 mod4. Once those source invariants are checked in the recovered/reconstructed counterfamily packet, the nonextension conclusion is immediate and requires no additional mathematical argument.

The free83 definitions and product were checked against the recovered Report43 source and explanatory text. This audit did not execute any upstream Python, saved arithmetic schedule, compiler builder, or historical verifier. It used direct proof review and filesystem reads only; no finite numerical test is being substituted for the theorem.

## Reviewed artifact identities

- Author proof: /workspace/shared/free83-even-rank-obstruction-20261004/PROOF.md
  SHA256: 25c0bd3727df1478cbae46cb64b40b871cf05512d2def4387802404773c77d95
- Recovered Report43 early small-norm proof: /workspace/shared/recovered-delivered-packages/free83-report43/source/structure/early_auxiliary_norm_lemma.md
  SHA256: 84c5c68411514717e6f2643c9d225bf529675c7123bcbbeef65fd1a8b2f44ea1
- Recovered literal free83 source JSON: /workspace/shared/recovered-delivered-packages/free83-report43/source/immutable/complete83_free_coefficient_scout.json
  SHA256: 682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016
