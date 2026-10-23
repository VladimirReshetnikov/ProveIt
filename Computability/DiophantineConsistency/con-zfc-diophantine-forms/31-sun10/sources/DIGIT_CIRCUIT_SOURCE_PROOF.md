# Nine-variable circuit and natural-domain majorant improvements

Source pin: VladimirReshetnikov/ProveIt@ae3007ca4467011e0e051c84acb4a1dd13971b0e.
Source package: SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/18-jones9.

This is a mathematical derivation with reproducible finite algebraic audits, not a newly compiled Lean/Rocq endpoint. Its consistency conclusion imports the same ordinary quartic32 compiler and K215 calibration as package18. The original formal source theorem is the parameterized Jones1982.Nine.wset_iff_nine, specialized at nu=32 and positive dummy input x=1, not the public theorem whose automatic quartic normalization uses nu=58.

## 1. Exactly the same polynomial with far fewer gates

Let B=b^5, nu=32, T=5^nu, L=5T. The upstream digit polynomial is

e(B)=sum_{|alpha|<=4}(z+c_alpha)B^(L-expo(alpha)),
expo(alpha)=sum_{j=0}^nu alpha_j 5^j.

Introduce only circuit registers, not new Diophantine unknowns:

t_j=B^(5^j), 0<=j<=nu+1;
v_j=B^(T-5^j), 0<=j<=nu.

Generate t_{j+1}=t_j^4*t_j, v_nu=1, v_j=t_j^4*v_{j+1}. Thus both arrays need O(nu) gates. Put w=(t_nu,v_0,...,v_nu). The integer-exponent identity

B^(L-expo(alpha))=t_nu*t_nu^(4-|alpha|)*product_j v_j^alpha_j

holds because T+(4-|alpha|)T+sum alpha_j(T-5^j)=5T-expo(alpha). The two sides are polynomials, including B=0; no division has been introduced.

Consequently

e(B)=t_nu [ z h_4(w) + sum_alpha c_alpha t_nu^(4-|alpha|) product_j v_j^alpha_j ].

The baseline h_4 uses the standard ascending complete-homogeneous recurrence. The 346 correction terms use a recursive multivariate Horner circuit. The recursion only applies distributivity and removes one exponent at a time. Coefficients remain the same fixed leaves, with no evaluation or implicit new parameters.

Likewise

lambda=sum_{r=0}^{4L-1}B^r
      = product_{j=0}^nu (1+t_j+t_j^2+t_j^3+t_j^4) * (1+q)*(1+q^2),
q=t_{nu+1}.

Here 1+t+t^2+t^3+t^4=1+t(1+t)(1+t^2). This uses no divisions. All Jones arithmetic blocks after e,ell,lambda,q are unchanged.

With the exact upstream nine-variable polynomial and the same gate model (each binary addition, subtraction and multiplication charged, constants free), the literal weights take 1609 live gates instead of20524; paper18's weights take1616 instead of20531. Their degrees are unchanged. These are constructed counts, not lower bounds on circuit complexity.

## 2. Natural-domain sign-erased majorants

The nine inputs epsilon,g0,h0,s0,w0,phi,i0,j0,n are nonnegative integers. The six variables g,h,s,w,i,j are shifted by1 as in package18. The fixed index has z>0,y>=0 and z+c_alpha>0 for all digit positions, so b,B,q,ell,lambda,e,N,G are nonnegative. In particular e>=0 is proved using its full digit sum, not by assuming its sparse coefficient corrections are positive.

For every subtraction in the formula for packed R, change minus to plus. Call the resulting expression Rbar. All its inputs are nonnegative, and repeated triangle inequalities give Rbar>=|R|. Explicitly:

Rlbar=g+e*q^3+ell*q^5+(2*(e+z*lambda)*(1+B+g)^4+lambda*B+lambda*B*q^4)*q^7;
Rrbar=q^3+b*ell+ell+(B+2z)*lambda*q^3+(B+2)*q^8;
Rbar=Rlbar*(N^2+N)+Rrbar*(N^2+1).

Retain U=N^2 w and Y=N^2 s. Build:

Mbar=Rbar*Y;
Pbar=2*Mbar^2*U;
Kbar=Rbar+1+h*(Pbar+1);
Abar=Mbar*(U+1);
Bbar=2*Rbar+1;
Cbar=Bbar+b*w+phi;
Jbar=4*Abar+5;
Dbar=(Abar^2+1)*Cbar^2+1;
Ebar=i*Jbar*Dbar*Cbar^2;
Fbar=(Abar^2+1)*Ebar^2+1;
Gpbar=Abar+Fbar*(Cbar*Dbar+1+Abar);
Hbar=Bbar+j*Cbar.

Every bar quantity is nonnegative and bounds the absolute value of its corresponding unbarred Jones quantity. This is an induction using triangle inequalities and multiplication of nonnegative majorants. It does not assume that R is positive, the radicands are squares, or the margin is positive.

For a,b real and abar>=|a|,bbar>=|b|, with both bars nonnegative,

|(a^2-1)b^2+1| <= (abar^2+1)bbar^2+1
                 <= ((abar+1)bbar+1)^2.

The second inequality has the explicitly nonnegative difference
2*abar*bbar^2+2*(abar+1)*bbar.

Set

V0=(Pbar+1)Kbar+2;
V1=2[((Abar+1)Cbar+1)((Abar+1)Ebar+1)((Gpbar+1)Hbar+1)]+1.

Then V0,V1>=2, sqrt(|a0|)<=V0-1 and sqrt(|a1|)<=V1-1, where
a0=(P^2-1)K^2+1 and a1=DFI.

The factor2 is optional for validity, but provides a simple noncancelling degree certificate. No additional existential unknown is introduced.

## 3. Finalizer and equivalence

Keep d=(JF)^2, c=(QF+J(H-C))^2, m=K^2G-4(C-KY)^2G-8gK^2. Let

Omega=d(2m-1);
Theta=dn+c-Omega(c+V0V1);
F9=(Theta^2-Omega^2(a0+V0^2 a1))^2-4Omega^4 V0^2 a0a1.

The upstream finalizer proof uses only d>0,c>=0 and the root bounds just established. Its proof works unchanged:

- J=4A-5 is nonzero for integer A. F=0 would force A=0,E=±1, impossible because E=iJDC^2 would be divisible by5. Thus d>0.
- F9 is the product of four signed radical factors over C. A zero gives r0+V0*r1=Theta/Omega rational. If that rational is nonzero, squaring isolates r0 and then r1 as rationals, hence integers. If it is zero, |r1|=|r0|/V0<1 implies a1=a0=0. This covers negative radicands and dependent square classes without additional assumptions.
- Once the roots are integers, Z=c+V0V1+r0+V0*r1>=c+1>0. The identity dn+c=d(2m-1)Z forces d|c and m>0 because n>=0.
- Conversely, if a0,a1 are squares, d|c and m>0, the integer n=(2m-1)Z-c/d is >=1 and gives a zero.
- Since d=u^2 and c=v^2, d|c iff u|v.

Thus existential zeros of F9 are precisely the same four ratio conditions as package18. The parameterized Jones reduction, positive-shifted quartic32 compiler and K215 calibration give

ZFC proves: [no zero of F9 in N^9] iff Con(ZFC).

This asserts a ZFC-provable equivalence, not Con(ZFC), and not a newly kernel-checked formalization of that equivalence.

## 4. Exact degree and count

Write L=5^33. Sign erasure preserves each listed leading degree; all-nine-inputs=t gives a scalar leading coefficient independent of all fixed constants. The new weights have

deg(V0)=1900L+7, leader=4;
deg(V1)=12320L+34, leader=2^24;
deg(Omega)=15971L+51, leader=-2^38;
deg(Theta)=30191L+92, leader=2^64.

In Theta^2-Omega^2(a0+V0^2a1), the top two terms have equal degree60382L+184, but leaders2^128 and2^126. Their difference is3*2^126, nonzero. The final subtracted term has smaller degree96124L+300. Hence

deg(F9)=120764L+368
       =14058779925107955932617187868,
leading diagonal coefficient=9*2^252.

The new circuit has1673live binary operations (679additions,22subtractions,972multiplications). The original paper18 degree is161844L+484; its original circuit has20531operations. The gain is in representation and a sharper root majorant, not a lower-variable theorem.

## 5. Positive-domain variants

Shift each of the nine natural unknowns by1 to obtain an equivalent equation over strictly positive integers. In the circuit, use g,h,s,w,i,j directly, b=y+epsilon_plus, phi=phi_plus-1, n=n_plus-1. This reduces five gates overall. The resulting counts are1604(literal),1611(paper18majorant),1668(new natural-domain majorant), with the same respective degrees. It is not an unrestricted-integer result.

## 6. Rebinding smaller authentic compiler coefficients

All constructions depend on one complete authentic nonnegative fixed port tuple. The 346 coefficient leaves and index z,y must all be recomputed together when rebinding. The same sparse support, degree and gate counts apply to any tuple for which the existing positive quartic32 compiler theorem is valid. No mixed tuple from different compilers is permitted. A new tuple is a semantic dependency to be validated separately; this note does not certify one from operation counts or modular residues.

## 7. Exact coefficient-recipe folding

The preceding gate counts deliberately retain all 346 named coefficient leaves independently. The actual quartic recipe has only 98 distinct coefficient polynomials, and 260 of the 346 records are literal integers. Replacing a literal recipe by that integer and identical recipes by the same fixed leaf is an exact polynomial identity in the four compiler ports, not a sampled numerical coincidence. Hash-consing and Horner evaluation then save 131 gates in each variant:

- Literal finalizer: 1478 gates over N, or 1473 over positive integers.
- Paper18 finalizer: 1485 gates over N, or 1480 over positive integers.
- New natural-majorant finalizer: 1542 gates over N, or 1537 over positive integers.

Degrees and final leading coefficients are unchanged. Each specialized DAG has 66 fixed leaves: z, y, and 64 distinct nonliteral coefficient recipes. The 346 original coefficient records remain the canonical index specification, and COEFFICIENT_ALIASES.json states every replacement exactly. The verifier checks all 346 alias identities and the complete digit-polynomial identity again after folding. The word specialized here refers to these known coefficient-recipe equalities; the optimization still works for every authentic compiler tuple.
