# First-norm auxiliary correction: thirteen positive variables,84 operations,degree92

This packet retains the complete current2011 four fixed coefficients and all
thirteen positive coordinates of `thirteen-unit-sphere96`. It changes the
polynomial, while preserving its entire positive integer zero set by the
identity map in both directions. It is a degree/operation tradeoff; it does
not claim global minimality or an internal HA, PA, or ZFC derivation.

## Exact complete formula

The fixed positive integer ports are beta,K0,MC,MF, where MF is shifted once
by beta as in the current2011 native source. The positive unknowns, in order,
are J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma. Put

```
b=beta*J, q=b+1, X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
kY=k*Y, ell=E*kY, c=kY+eta, a=E+Y, H=4*a+3,
delta=a^2+H, D=X+a*c+gamma*H,
C=q-F-alpha, G=(K0+w)*C-F,
R=(b*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
tau=E*n+k-R,
P=tau^2-ell*(ell+k), Q=D^2-delta*c^2,
L=c*T-R, V=f^2*L-c,
y=1+4*(b*(m-L*V*G)-G),
U=delta*(f^2-1)*(V^2-y^2)+y^2,
Z=f^2-delta*(b*i*c^2)^2,
A=16*b^2*f^2*T^2*V^2*G^2,
Uc=U-A*(P-1),
p84=(P*Q)^2+Uc^2+Z^2-3.
```

All coefficients and exponents in these expressions are integers. The actual
complete84-row graph, rather than these abbreviations, determines the paid
operation count. The parent is p75=(P*Q)^2+U^2+Z^2-3.

## Entire positive-zero equivalence

For integers u,v,z, the equality u^2+v^2+z^2=3 forces each square to be1:
each square is at most3, hence is either0 or1, and all three must be1.
The accepted actual first and main norms satisfy P != -1 and Q != -1 for
every positive assignment (the latter exclusion even holds without
positivity). These are the exact existing Lean lemmas
`ThirteenCorrectedStrong.first_ne_neg_one` and
`ThirteenUnitSphere96.main_ne_neg_one`.

For either p84=0 or p75=0, the sphere lemma gives (P*Q)^2=1. A product of
integers neither of which is-1 cannot be-1: either factor of a unit is1 or-1.
Thus P*Q=1, and the same unit argument yields P=1 and Q=1. Consequently
A*(P-1)=0 and Uc=U. The two equations are therefore equivalent on every
positive assignment, with all thirteen coordinates unchanged. This argument
actually works for any integer A and arbitrary integer U,Z, given only
P,Q != -1. It does not assume Uc has a norm sign property, does not recover
P from a desired target zero, and does not need the conditional U != -1
lemma. The prior whole positive-zero equivalence with the accepted mixed
carrier and the actual external Lean ConZFC endpoint now transfers.

The polynomials are generally unequal; their exact difference is
A^2*(P-1)^2-2*U*A*(P-1). The auditor verifies this complete cut-ring identity
and an unequal actual fixed-port positive assignment. This is a zero-set
argument, not a polynomial identity with the parent.

## Paid operations and complete data

Keep every75 parent row, changing only `sqU` to square Uc. Before the old
seven-row sphere tail insert exactly these nine binary operations:

```
bT=b*T; bTG=bT*G; bTGV=bTG*V; bTGV2=bTGV*bTGV;
corr0=bTGV2*f^2; corrCoefficient=16*corr0;
Pminus1=P-1; correction=corrCoefficient*Pminus1;
correctedU=U-correction.
```

The existing f^2 producer is reused. Multiplication by16 is paid. The total
is49 multiplications,18 additions,17 subtractions:84. Every producer,
positive coordinate, and fixed port remains reachable from the output.
The auditor additionally gives unequal modular evaluation witnesses for
actual polynomial dependence on every coordinate and every fixed port.
Whole current coefficients remain47,313 raw bytes and4,230 gzip bytes.

## Exact degree, with fixed ports of degree zero

Use B=beta*J and k0=eta+zeta for the homogeneous leading forms. The parent
factor degrees are P22,Q18,U48,Z36. Its main norm Q has a genuine leading
cancellation; its complete323-term expansion and degree18 are checked.
The new correction cancels both degrees48 and47 of U. The exact degree46
homogeneous part of Uc is

```
16*B^21*k0^3*f^4*T^3*s^5*w^3*(B-F-alpha)^2
 * (B*k0*T*s*w - 2*k0*f^2*T*s + 2*B*f^2*w*(B-F)).
```

This expression has96 terms when expanded. In particular, the coefficient
of J^21*alpha^2*f^6*T^4*s^6*w^3*zeta^4 is -32*beta^21.
The square Uc^2 is degree92, while (PQ)^2 and Z^2 have degrees80 and72.
The complete degree92 homogeneous output is the square of the displayed
form, with900 terms. Its lexicographically first exponent has coefficient
1024*beta^42, for J^42*alpha^4*f^12*T^8*s^12*w^6*zeta^8. This is nonzero for
the actual beta>0, so specialization of the four ports retains degree92.

A structural explanation for the cancellation is obtained by writing
y=u-4*b*L*V*G, u=1+4*(b*m-G). The highest auxiliary contribution combines
with the correction through delta*L^2+T^2*(P-1). Expand this bracket as

```
T^2*(delta*c^2+P-1)-2*delta*c*T*R+delta*R^2.
```

The degree22 terms in delta*c^2 and P cancel, since c=kY+eta,
ell=E*kY, and delta-E^2=2*E*Y+Y^2+4*E+4*Y+3. The bracket has degree at most22
rather than24. The bounded sparse auditor retains the exact highest three
homogeneous layers at each preceding gate, verifies both cancellations,
and then computes the exact degree46 and degree92 leaders. It does not
claim that those retained layers constitute the complete expanded p84.
All gate degrees and complete leaders are recorded, and all71 unchanged
parent leaders outside the affected sphere branch are checked exactly.

## Proof and verification boundary

`ThirteenFirstNormCorrection92.lean` proves the generic arbitrary-correction
integer lemma, whole positive zero equivalence, polynomial evaluation,
identity witness maps, and the actual current external ConZFC equivalence.
The finite auditor separately binds the complete graph, the exact formula,
all leaders, every whole coefficient, and corruption controls. It imports
no project or incoming Python code. There is no new machine calibration,
internal HA derivation, or assertion that84/92 is globally optimal. Relative
to the accepted13/75/96 it trades nine operations for four degrees; the
accepted fourteen-variable frontiers have fewer operations but more
variables, so they do not dominate this point in the three stated metrics.
