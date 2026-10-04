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

## The main -Delta branch cannot use f=1

This statement does not exclude all f>1 main -Delta branches.

If main=-Delta, squarefreeness similarly gives

  c=chi_A(p), D=Delta*psi_A(p).

The retained first/index units imply n>=24 and k=2psi_P(n), P>A. Since c>kY>psi_A(n) and chi_A(n-1)<psi_A(n), p>=n>=24. Consequently c>A Delta² (the same explicit psi_A(6) bound more than suffices).

At f=1, strong=-1 forces S=A. Auxiliary=1 classifies

  V=±chi_A(t)/A, t positive odd,

and the literal quotient gives V=-R modc. The Pell identities chi_A(2p)=-1 and psi_A(2p)=0 modc reduce chi_A(t) to ±chi_A(j), where j is odd and 1<=j<=p.

- If p is even, gcd(A,c)=1. Division modulo c gives representatives ±chi_A(j)/A for odd j<p. Their magnitudes are <c/2. The smallest is 1; every other one is >=chi_A(3)/A=4Delta+1.
- If p is odd, divide the congruence by A modulo c/A instead. The j=p representative is 0; the others have magnitude <(c/A)/2. Again their only magnitude below 4Delta+1 is 1.

Since 1<R<Delta and c/A>Delta²>2R, neither residue list can contain -R. This excludes the proposed f=1 main=-Delta/strong=-1/aux=1 branch. The f>1 case remains open here.
