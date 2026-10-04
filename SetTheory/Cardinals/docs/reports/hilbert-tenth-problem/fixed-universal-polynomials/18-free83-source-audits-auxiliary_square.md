# Independent audit: the free83 auxiliary factor is a positive square

**PASS for the stated auxiliary-factor theorem, on every genuine fixed-compiler slice and the strictly positive supplied domain.** The proof does not normalize the other six factors. It does not establish an 83-operation universal bound or ordinary-input soundness.

For the exact source at commit `0d9d1e0174df30d82d80d758e9ba8e793203126e`, every full positive zero satisfies

\[
 N_a=z^2>0,\qquad z^2\mid\Delta,\qquad z=\gcd(|V|,y)
\]

for a positive integer z. In particular z divides V and y. The equality with the gcd is a small strengthening of the submitted claim.

The reviewed author notes are frozen in `source/early_auxiliary_norm_lemma.md` and `source/exceptional_negative_aux_exclusion.md`. This audit is independent; it executed no upstream Python and no saved arithmetic schedule.

## 1. Exact source and hypotheses

The scout JSON was freshly fetched through the read-only GitHub connector at its immutable commit, then compared byte-for-byte with the existing local copy. The immutable URL and Git blob identifier are recorded in `source/FETCHED.json`.

- Git blob SHA-1: `71edcd445eb45561613d40fbf8908d586f5a782c`
- JSON SHA-256: `682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016`
- Compact saved source-array SHA-256: `7834fa4ab4baa9faba720f572301d7f2ef5782a077c5e5adee931c89f46d240c`
- Parent85 mathematical review SHA-256: `77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d`, matching the scout's declared dependency pin

The checker independently fixes 71 literal rows, including every auxiliary/strong/finalizer row and all source ports used in the bootstrap. It also compares the entire dependency cones of all five retained factors with the saved parent85 source. Cone sizes are respectively 14, 24, 29, 21 and 12 for first, main, input, index and transport. These are structural comparisons, not source evaluation.

Write, using mathematical names rather than ambiguous register names,

\[
 q=(B-1)J+1,\quad X=wq,\quad Y=sq^3,\quad E=XY,
\]
\[
 a=Y(X+1),\quad A=a+2,\quad\Delta=A^2-1,
\]
\[
 k=\eta+\zeta,\quad c=kY+\eta,\quad
 D=X+ac+(\rho+\sigma)(4a+3).
\]

The source register named `A` holds Delta, not the Pell parameter A. All supplied coordinates and ordinary input are positive integers. In particular A>=3, Delta>=8, c>0, and D>0. Set S=`aux_coefficient_root`, T=`auxiliary_quotient`, y=`y_aux`, and

\[
 V=c(Tf-1)-Rf^2,\quad d=\Delta f^2-S^2,\quad
 N=S^2V^2-(S^2-1)y^2.
\]

The actual finalizer says that the product of d, N, and the five retained integer factors equals Delta. Thus every factor is nonzero, divides Delta, and has absolute value at most Delta; also |dN|<=Delta.

The genuine fixed-compiler recipe supplies B>=16, Kconstant>0, positive input scale, 0<MC<B-1, and MF=MF_native+B-1 with 0<MF_native<B-1. These necessary consequences suffice for the elementary packing bounds used here. No claim is made that replacing the full compiler recipe by just these inequalities preserves its ordinary-input theorem.

## 2. The general small-norm descent is valid

For integer H>=2, v>=0, y>0 and N=Hv^2-(H-1)y^2:

1. Negative N satisfies N<=-(H-1)
2. If 0<N<H, then N is a square z^2 and gcd(v,y)=z
3. N=-(H-1) has precisely the solutions
   v=2(H-1)psi_(2H-1)(r), y=chi_(2H-1)(r), r>=0

Here chi_C(r)+psi_C(r)sqrt(C^2-1)=(C+sqrt(C^2-1))^r.

To verify all three assertions, when y>v put t=y-v. Then

\[
 -N=(H-1)t^2+v\bigl(2(H-1)t-v\bigr).
\]

If N<0 and v<=2(H-1)t, the right side is at least H-1. Otherwise N<0 bounds v<(2H-1)t, so the integral norm-preserving map

\[
 (v,y)\mapsto((2H-1)v-2(H-1)y,\;(2H-1)y-2Hv)
\]

has positive coordinates and strictly smaller first coordinate. Descent proves the negative gap.

For 0<N<H, v>y would already give N>=H. If y=v the claim is immediate. Otherwise N>0 gives v>2(H-1)t, while N<H gives v<(2H-1)t. The same descent terminates at (z,z), proving N=z^2. The matrix has determinant 1, so it preserves the gcd in both directions. This proves the exact gcd assertion, also for a signed original V after replacing it by |V|.

At N=-(H-1), the terminal equation forces t=1 and v either 0 or 2(H-1). The latter maps to (0,1). The inverse matrix is

\[
 \begin{pmatrix}2H-1&2(H-1)\\2H&2H-1\end{pmatrix},
\]

whose iterates of (0,1) give the displayed Pell formula. This includes V=0 and both signs of any nonzero V. No classification of arbitrary ramified norm equations is used.

## 3. The product forces either a positive small norm or one exact negative branch

S=1 would give d=Delta f^2-1>=7 with gcd(d,Delta)=1 and d dividing Delta, a contradiction. Thus S>=2; take H=S^2>=4.

If N<0, the preceding gap yields |d|(H-1)<=Delta. For f>=2, H=Delta f^2-d>=3Delta, impossible. Hence f=1.

If d<0, put b=-d>=1. Then H=Delta+b and b(Delta+b-1)<=Delta forces b=1. Consequently S=A, d=-1 and N=-Delta.

If d>0, then Delta=H+d and the same inequality is (d-1)(H-2)<=2. The case d=1 would give A^2-S^2=2, impossible. For d>=2 and square H>=4, the only numerical case is H=4,d=2, yielding A^2=7, also impossible.

Therefore the only possible negative branch is

\[
 f=1,\quad S=A,\quad d=-1,\quad N=-\Delta.
\]

For positive N one always has N<H:

- f>=2: H>=3Delta>Delta/|d|
- f=1,d<0: H>Delta>=Delta/|d|
- f=1,d>0: d=1 is impossible, and d>=2,H>=4 give dH>H+d=Delta

Since N<=Delta/|d|, the bound follows in every case, including f=1 of either sign. The small-norm lemma already proves that every positive auxiliary factor is a square.

## 4. The retained-five-unit bootstrap is legitimate in the negative branch

Only now assume the exceptional negative branch. Since dN=Delta, the five untouched factors have product 1 and are each units. This is the sole point where unit hypotheses are introduced.

The first factor is tau^2-u(u+1)k^2 with u=XY^2>1. If it were -1, the standard integral inverse-unit map with coefficients 2u+1 and 2 would produce a strictly smaller positive k; the root can be replaced by its nonzero absolute value. Indeed uk<tau<(u+1/2)k, so 0<(2u+1)k-2tau<k. Thus this factor is +1. Main and input factors cannot equal -1 modulo 4 because Delta is 0 or 3 modulo 4. The input root need not be positive for this argument. Hence these two factors are +1 too, while

\[
 N_k=N_t=\epsilon,\qquad\epsilon\in\{-1,1\}.
\]

Both signs are retained throughout what follows.

Write C=q-F-Z-alpha-ell*x and t for the positive transport quotient. The transport factor is

\[
 (Kconstant+w)C+1-F-(t-1)(q-1).
\]

Its last three terms are nonpositive and Kconstant+w>=2. Unit magnitude therefore forces C>=0, hence F+Z<q. For

\[
 G=q^2-qF-Z,\quad M=(MC+qMF)J,\quad R=G(q^2-1)+M,
\]

positivity and F+Z<q give

\[
 2q-1\le G\le q^2-q-1,\qquad 0<M<(q-1)(1+2q).
\]

Consequently

\[
 (2q-1)(q^2-1)<R<q^4-q^3,
\]
\[
 0<R<a<\Delta,\qquad R+2<E,
\]

because E=wsq^4>=q^4 and a=E+Y. These estimates allow odd as well as even q and do not type q as a power of B.

Let P=2XY^2+1. The first positive norm has fundamental pair (P,2), giving k=2psi_P(n), n>=1. This can also be proved by the same inverse-unit descent: coefficient 1 is impossible, coefficient 2 gives P, and every larger coefficient descends. Since P=1 modulo E, psi_P(n)=n modulo E. The index unit implies

\[
 2n=R+\epsilon+vE,\qquad v\ge0.
\]

The nonnegativity uses 0<R+epsilon<E, valid for both signs. Thus n>=(R-1)/2>=24. Since D>0, the main positive norm gives D=chi_A(p), c=psi_A(p) for p>=1. Also P>A and c>k, so monotonicity gives p>n and p>=25.

The extra bound c>A Delta^2 follows without any strong-rank theorem: for A>=2,

\[
 \psi_A(6)-A\Delta^2=A(31A^4-30A^2+5)>0.
\]

This explicit step has now been added to the author's note. It yields c>2R as well. No assumption A even, q even, p=R, a normalized strong factor, or a pre-existing full parent85 zero is present.

## 5. The exceptional Pell congruence is impossible

The classification in Section 2, with B=2A^2-1, gives

\[
 V=\pm2\Delta\psi_B(r),\qquad r\ge0.
\]

The actual source formula at f=1 requires V=-R modulo c.

For any C>=2, m>=1, write t=qm+j, 0<=j<m. Pell addition and chi_C(m)^2=1 modulo psi_C(m) show that psi_C(t) is congruent to 0 or to a signed psi_C(i), 1<=i<m. For odd m and even t, i can be chosen even: if q is odd use i=m-j with the subtraction identity. This parity refinement is valid; it does not assume C even.

If p is odd, gcd(A,c)=1 and A divides psi_A(i) for every even i. The exact identity 2A psi_B(r)=psi_A(2r) and the parity-refined lemma therefore give

\[
 V\equiv0\quad\text{or}\quad\pm\Delta\psi_A(i)/A\pmod c,
 \qquad 2\le i\le p-1,\; i\text{ even}.
\]

Every displayed nonzero magnitude is at least 2Delta and strictly less than c/2. The latter follows at i=p-1 from

\[
 Ac=A^2\psi_A(p-1)+A\chi_A(p-1)>2\Delta\psi_A(p-1).
\]

Thus none can equal the residue -R with 0<R<Delta<c/2. The zero residue is also excluded.

If p=2m is even, put b=psi_B(m), so c=2Ab. The congruence first forces R even. Dividing by 2 and reducing modulo b yields

\[
 \pm\Delta\psi_B(r)\equiv-R/2\pmod b.
\]

The residue lemma makes the left side 0 or a signed Delta psi_B(i), 1<=i<m. These nonzero magnitudes are at least Delta and strictly less than b/2, since

\[
 b=2B\psi_B(m-1)-\psi_B(m-2)>(2B-1)\psi_B(m-1)>2\Delta\psi_B(m-1).
\]

Also b=c/(2A)>Delta^2/2>R. Therefore 0<R/2<min(Delta,b/2), again impossible. This handles r=0, both signs of V, and both parities of p.

## 6. Conclusion and exact limitations

N cannot be zero because the full product equals positive Delta. Section 5 excludes negative N. Sections 2 and 3 give N=z^2 and gcd(|V|,y)=z. Finally N divides Delta, hence z^2 divides Delta.

If Delta is squarefree, this proves N=1. Otherwise a positive nonunit square remains possible from this theorem alone. The theorem neither proves nor assumes that the other factors are units on a general full83 zero; the temporary main rank p was introduced only inside the discarded negative branch. It does not show p=R, A even, V positive on every general branch, integrality of the deleted coefficient, language soundness, or a full false-accepted-input witness. Optional subsequent squarefree/swapped-norm claims are outside this audit.

## 7. Independent probes and replay

`audit_auxiliary_square.py` is independent standard-library code. It reads the frozen source as inert JSON, verifies literal rows and dependency cones, and evaluates only newly written elementary formulas and Pell recurrences.

`CHECKS.json` records:

- 11,091,600 complete rectangle tuples with H=2..80, v=0..350, y=1..400; 586 positive-small solutions and 165 negative-boundary solutions all match descent/classification
- All eligible S with 0<|Delta f^2-S^2|<=Delta for A=3..200 and f=1..50, then the exact divisor filter: 940 cases cover all four f/sign branches; 198 negative candidates are precisely f=1,S=A,d=-1
- 323,400 exact residue checks for C=2..50, m=1..40, t=0..8m, including the parity refinement
- 1,092 complete observed modular recurrence cycles for A=2..40, p=3..30, covering 203,658 states, both V signs, and every 0<R<Delta
- 240 shifted-packing checks deliberately including odd and even q

The probes found no counterexample. They supplement, rather than replace, the unbounded proof above. They are not evaluations of full compiler zeros or evidence of ordinary-input acceptance.

Replay from any directory:

```
python3 /workspace/shared/free83-auxiliary-square-audit-20261003/audit_auxiliary_square.py
```

The checker uses explicit exceptions rather than assertions, so optimization does not disable its checks.
