# Adaptive saturation in twelve positive variables

The literal equation p12_degree78.json uses twelve strictly positive integers and the complete compact44 coefficient tuple of source69. Its exact degree is78 and it has101 live binary operations (56 multiplications,26 additions,19 subtractions), improving source69's82/102. This is an incremental synthesis, not global minimality or a new kernel certificate.

Retain all definitions and the final polynomial of source69 positive/PROOF.md, except replace U=q^5 by U=q^2 Y and replace q^4 X in Dstar by qXY. Thus Dstar=U(X+ac)+H(U gamma+qXY-(k-R-1)). All other residuals A0,N and their polynomial definitions are identical; A1=Dstar^2-U^2(1+Delta c^2). P=(1+A0)(1+A1)(1+N)-1. Inputs j,F,alpha,t,T,X,Y,r,eta,zeta,n,gamma are positive, f=t+1, J=6j+1. There are no new unknowns.

## Soundness

The parity finalizer argument is unchanged: q is even, so both M and the new U are even. Each residual is a square modulo4. A product of three units1+residual equal1 forces each residual zero, since a negative unit would require residual=-2, impossible modulo4.

A0 recovers q^3|Y, q-1|Bt, C>0, 3q<R<q^4-2. Hence U>=q^5 and the original positivity estimate for Dstar remains valid. A1 supplies a positive integral main Pell root. The first/main Pell classification yields n_first>=2 and c>8XY^3>2R, exactly as69. This step does not use the strong or auxiliary equation or q|X. Therefore V=f^2(cT-R)-c>1.

Source69's rational-integrality descent and norm elimination now apply without any modification to N. They recover positive integral i,u satisfying the normalized strong and auxiliary Pell equations. We now have precisely the thirteen-positive equation of source73 positive/PROOF.md, with its j-coordinate2j and its strong-root coordinate f=t+1. Source73's soundness theorem recovers the remaining divisibilities and all deleted positive source witnesses. In particular its adaptive carrier uses only q^3|Y to prove U divides4XY^2, avoiding any circular assumption q|X. Its identified native calibration yields a finite ZFC refutation.

## Completeness

A refutation supplies canonical normalized witnesses. The canonical J is1 modulo6, so choose positive j=(J-1)/6 as in69. The source73 constructive lift chooses gamma=gamma_old-w+(k-R-1)/U. This is positive because (k-R-1)/U>=4XY/q^2>w. The other carrier coordinates are unchanged and vanish. Strong f>1 gives t=f-1>0; choose n=i+u>0. Source69's exact identity N|rho=d i^2=d^2 h(n-i)h(n+i) gives N=0. Thus P=0.

Consequently ZFC proves absence of positive zeros equivalent to Con(ZFC), relative to the same explicitly inherited source/compiler theorems as69 and73. This is a mathematical existential reduction and does not assert that finite tests establish the unbounded calibration.

## Exact degree

Write q0=6 beta j, k0=eta+zeta, R0=q0^3(q0-F), B0=(K0 q0+X)(q0-F-alpha)-q0F. The exact leading forms already established independently in69 and73 are

[A0]15=-2q0^8 k0^2 X Y^2 B0,
[A1]13=8q0^2 k0 X^2 Y^4(q0^2Y gamma+R0),
[N]50=4k0^8 X^8Y^16 t^8R0^2 n^2.

Only their product reaches degree78. Its leader is
-64q0^10 k0^11 X^11Y^22 t^8 n^2 B0(q0^2Y gamma+R0)R0^2.
The coefficient of j^18 eta^11 X^12 Y^23 t^8 n^2 gamma alpha F^2 is64(6 beta)^18>0, independently of the other three ports. Hence the exact degree is78 on the actual coefficient slice. Literal liveness confirms101 operations.

## Provenance and reproducibility

Sources: ProveIt main2605669a532342f153b13eb6b4a0af4b54f5fa37, packages69-cones-pell and73-guard-reanchoring. The new literal graph differs from69 only by the two stated carrier substitutions and deletion of dead q4. build.py reconstructs it; check.py independently evaluates all named residuals and liveness on deterministic examples. These regressions test transcription, not consistency. A self-contained final packet must retain the complete unchanged coefficient binding from69 or73, never mix ports.
