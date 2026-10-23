# Twelve guarded coordinates suffice for the quadratic source

## Statement and scope

Let the 31 variables, four fixed ports and 22 residuals be exactly those of
`diophantine_zfc_round7/nine/data/source_system60.json`, whose SHA-256 is
`ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48`.
Assume beta and K0 are positive integers; MC and MF may be arbitrary integers.
Only the following twelve old positive coordinates are shifted by one:

F, alpha, z, h, i, j, s, w, eta, zeta, gamma, g.

All other old coordinates are represented directly by natural integers,
including zero a priori. This gives a bijection between the old system's
strictly positive zero set and the new system's natural zero set. In
particular it does not merely give a one-way existence reduction. No
compiler consequence, Pell rank lemma, consistency assumption or numerical
specialization is needed for the new positivity recovery below.

The transformed source still has 31 variables and 22 quadratic residuals.
It has 109 symbolic coefficient records and 62 distinct active monomials:
39 quadratic, 22 linear, and the constant. The prior all-coordinate shift
had 136 records and 71 active monomials. This is a reduction in the source
encoding burden, not a decrease in the source's variable count.

## Elementary positivity recovery

Start with any natural tuple satisfying the new residuals and reconstruct
the old coordinates by the declared twelve shifts. The twelve guarded
coordinates are strictly positive by construction. Define only abbreviations

q = 1 + beta J, k = eta + zeta, C = q - F - alpha,
U = L + 1, Y = a - E, Q = c - eta, T = P - k,
H = 4a + 3.

The equations quoted here are literal rearrangements of the pinned source.
All unguarded old coordinates are nonnegative at this stage.

1. Transport says (K0+w)C = F + z beta J. Its right side is positive
   because F>0, z>0, beta>0 and J>=0. Its left multiplier is positive.
   Hence C>0. Therefore q=F+alpha+C>=3, so J>0.

2. U=q^2 gives L=q^2-1>0. N=qU then gives N>0, and X=wq gives X>0.

3. Y=sN>0 and E=XY>0. Thus a=E+Y>0.

4. k=eta+zeta>0. Q=kY>0 and c=Q+eta>0. T=EQ>0 and
   P=T+k>0. The equation tau^2=PT+1 makes tau>0.

5. H=4a+3>0. The equations D=X+ac+gamma H,
   Delta=a^2+H, and C2=c^2 give D>0, Delta>0 and C2>0.

6. I=i C2>0 and Baux=I^2>0. Then
   Baux=Delta(F2-1) implies F2>1. Since F2=f^2, we have f>=2.

7. The last equation is y^2=Baux g+1. Thus y^2>1 and y>=2.
   Together with g=y^2-V^2 this yields

       V^2 = (Baux-1)g + 1 >= 1.

   Because V>=0, V>0. Finally V=of-c implies of=V+c>0,
   and hence o>0.

This covers all nineteen initially unguarded coordinates:
J,f,o,tau,y,N,E,P,c,a,X,D,C2,L,F2,V,I,Baux,Delta.
There is no unproved positivity premise hiding in the argument.

## Reverse map and nonzero-source guard

Given any positive zero of the old system, subtract one from exactly the
twelve guarded coordinates and leave the other nineteen unchanged. The
new tuple is natural, and the residual identities show it is a zero.
The two coordinate maps are literal inverses. Thus the zero sets are
bijective.

The all-zero natural tuple is not a simultaneous zero. For example,
row 2 is N-(1+beta J)(L+1), whose value at zero is -1. This nonzero-source
condition is needed by the inherited nine-/ten-variable source bridge;
it survives without shifting J, L, N or every auxiliary coordinate.

## Fixed tuple and semantic boundary

The coherent four-port compiler tuple and the old positive system's
refutation equivalence must be inherited unchanged. In particular all four
ports are selected together, and MF is the already-shifted MF_source.
Composing the bijection above with the inherited compiler/calibration
therefore gives the same ZFC-provable equivalence to Con(ZFC).
The new argument does not repair or replace the inherited compiler proof.

`build_selective_source.py` reads the old JSON only as inert data. It
reconstructs every residual, applies the affine substitution, and emits
literal terms, weighted coefficients, and positional pair lists. The
factorial convention is unchanged: a monomial of degree d and exponent
vector alpha receives weight (2-d)! product(alpha_i!). Consequently all
existing sparse quadratic coefficient-extraction and carry arguments
apply to this new source, once a suitable positional certificate is
independently verified. Lower numerical packing values are not asserted
merely from the smaller support count.
