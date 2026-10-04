# Two further obstructions on a squarefree discriminant slice

These are conditional branch exclusions, not a full classification of83 zeros.

Assume the genuine fixed-compiler slice and squarefree Delta=A²-1. Then A is necessarily even, so `even_parameter_divisor_classification.md` and the auxiliary-square theorem give main/input norm in {1,-Delta}, strong in {-1,Delta}, and auxiliary norm 1. If either main or input is -Delta, the full product forces strong=-1 and all remaining factors to be units; the other Pell norm is +1, first is +1, and index/transport have the same sign epsilon in {±1}. Hence the packing bounds give 1<R<a<Delta, and C>=0.

## The input factor cannot be -Delta

The exact input norm is mu²-Delta*kappa², with kappa=I+delta*Delta and I=twice_cell_bits*x+inner_bits. If that norm is -Delta, squarefreeness forces Delta|mu; writing mu=Delta*b gives

  kappa²-Delta*b²=1.

Thus kappa=chi_A(t) for some t>=0. Reducing the Pell first coordinate modulo Delta gives chi_A(t)=A^t modDelta, so kappa=1 or A modDelta. But the genuine compiler recipe has twice_cell_bits=2d, 1<=inner_bits<=d and q>=2^d>d. The transportunit C>=0 gives 2dx<q, hence

  1<I<q+d<2q<A<Delta.

This is incompatible with I=1 or A modDelta. Therefore the input -Delta branch is impossible.

The recipe was read directly in complete75_half_binomial_compiler.md Section1 and FIXED_RAW_UNIVERSAL_76_PROOF.md Section1, in the preserved first-index-attack provenance directory. The independent retained-unit investigator also cross-checked the loader bound. No claim uses this C bound outside the transportunit branch.

## A divisibility lemma for Pell first coordinates

For A>=2 and m>=3,

  psi_A(m) | chi_A(p)+epsilon, epsilon in {+1,-1}

forces 2m|p and chi_A(p)=1 modulo psi_A(m).

Proof: put f=psi_A(m), D=chi_A(m), and write p=qm+j, 0<=j<m. Since D²=1 modf, Pell addition gives chi_A(p)=chi_A(j) modf for q even, and chi_A(p)=D chi_A(j)=chi_A(m-j) modf for q odd. The interior values chi_A(j), 1<=j<m, lie strictly between 1 and f-1: chi_A(j)>=A>=2 and f-chi_A(m-1)=A psi_A(m-1)>=2. The endpoint chi_A(m)=A f-psi_A(m-1) has residue f-psi_A(m-1), also strictly between 1 and f-1 because m>=3. The only possible ±1 residue is therefore +1 at j=0,q even. QED.

For m=2, the weaker implication is that p is even, since psi_A(2)=2A and chi_A(p)=0 modA when p is odd.

## A small-target quotient obstruction

Let S>=2, k>=6, c=chi_S(k), and 1<L<S²-1. There is no odd positive t and either sign epsilon for which

  epsilon*chi_S(t)/S=-L modc.

Proof: Pell identities give chi_S(2k)=-1 and psi_S(2k)=0 modc. Reducing the odd t by period/reflection therefore gives chi_S(t)=±chi_S(j) modc for an odd j with 1<=j<=k.

If k is even, gcd(S,c)=1. Division modulo c gives integer representatives ±chi_S(j)/S, j<k odd, all with magnitude <c/2. If k is odd, divide the congruences by S modulo c/S; the j=k case gives 0, and the remaining magnitudes are <(c/S)/2. In both cases the smallest nonzero magnitude is 1, and the next is chi_S(3)/S=4(S²-1)+1>L. Also c>S(S²-1)²>2SL, using k>=6 and the explicit psi_S(6) bound. Hence -L is too small to coincide with any representative except possibly ±1, which L>1 excludes. QED.

## The main factor cannot be -Delta, for any f

If main=-Delta, squarefreeness gives

  c=chi_A(p), D=Delta*psi_A(p).

The retained first/index units imply n>=24 and k_first=2psi_P(n), P>A. Since c>k_first*Y>psi_A(n) and chi_A(n-1)<psi_A(n), p>=n>=24.

The strong=-1 equation gives S=chi_A(m), f=psi_A(m), m>=1. Auxiliary=1 gives V=epsilon*chi_S(t)/S for t positive odd and epsilon=sign(V). The quotient polynomial identity Q_h(1)=1, together with S²=1+Delta*f², yields V=epsilon modf (in fact modf²). The literal V=-c modf therefore gives

  f | c+epsilon.

If m>=3, the divisibility lemma forces 2m|p and c=1 modf. Also c>=chi_A(2m)=1+2Delta*f². Since R<Delta and T>=1,

  V=c(Tf-1)-R*f²>c(f-1)-c/2>0.

Thus epsilon=+1, which would require c=-1 modf as well as c=1 modf. But f=psi_A(m)>2, contradiction.

If m=2, the divisibility condition forces p even. Write p=2k, k>=12. If m=1 put k=p>=24. In either case c=chi_S(k). Set L=R*f². Since R>1 and R<Delta,

  1<L<Delta*f²=S²-1.

The literal congruence V=-R*f² modc is exactly the impossible small-target quotient congruence. This excludes m=1 and m=2 too.

Therefore the full main=-Delta branch is impossible on squarefree Delta.

## Remaining squarefree cases

Every full positive83 zero on a squarefree-Delta genuine slice consequently has

  norm_main=norm_input=norm_aux=1.

Either norm_strong=Delta, in which case first/index/transport are units (first is +1, index/transport share a sign), or norm_strong=-1, in which case

  norm_first * norm_index * norm_transport = -Delta.

The latter remaining divisor/sign equation is not settled here. The first branch still has the free-coefficient rank problem and is not automatically a parent zero.
