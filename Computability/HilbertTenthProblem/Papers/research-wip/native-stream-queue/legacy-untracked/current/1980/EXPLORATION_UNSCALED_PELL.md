# Reserved exploration: using M=Y in the shifted base-four Pell system

This is an unimplemented independent candidate, not an additional verified
certificate or a claimed improvement over the index-multiple construction.
It records a possible alternative 105-operation route from the frozen
106-operation base-four system. No frozen checker is modified.

Retain U=wN^2, Y=sN^2, but set M=Y instead of RY. Then A0=Y(U+1),
A=A0+4 and Q=UY^2; retain the old index equation K=R+1+hQ. Aliasing
the existing Y register as M removes the multiplication RY. All other
arithmetic instructions appear to retain their old costs. This does
not immediately combine with the index-multiple saving, since Q is
not known to be divisible by R+1.

There is enough preliminary growth to try the same proof. The packing
has 0<S<N and 0<=T<N, whence N<=R<2N^3. Since U,Y>=N^2,
Q>=N^6>R+1 and A>N^4>2R+1. Thus the old modulo-Q index argument
still isolates R+1. Also 2A/(2P-1)<1/2. The lower shifted-ratio
estimate remains xi<C/K because 14Q>A0 still holds.

The upper ratio bound now requires checking

    8R/A0<16/N<1/2,

which follows from the actual N=q^8 and q>8. It yields

    C/K<xi*(1+16R/[Y(U+1)]).

The interval still implies Y>=U^R. Hence

    A>A0=Y(U+1)>U^(R+1),

which suffices for both exponent tests: N>=64 and U>=N^2 imply
4^(3J)=64*4096^R<U^(R+1), while W^3<=U^R and
B^(3L),q^3<=N^N<=U^R. Thus bw=4^J can be recovered before the
improved error estimate is needed. It gives U>=N*4^J and therefore

    0<C/K-xi<32R/(U+1)<1/2.

The direct integral rounding in MAIN_PELL_BASE_FOUR_PROOF.md would
then apply. Necessity would use the same new w=4^J/b and Y=floor(xi),
with M=Y, and the same positive quotient arguments.

Outstanding work before claiming a certificate: encode the changed
source residuals and primitive list, verify them exactly, write full
inequalities at every use, and independently audit all positive witness
maps. The current published/baseline certificates do not depend on
this exploratory note.
