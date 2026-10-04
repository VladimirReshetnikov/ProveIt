# Addendum audit: the separate power-of-17 family

PASS, again only for the inner/intended-factor theorem and stated necessary outer restrictions. This is a separately reviewed addendum; it does not alter the original power-of-11 proof audit.

The parameterization u=17^(2j),p=35u,n=30u,R=60u-1,Y exponent7u-1 has35*5=7*25, giving the exact resonance. The ratio bound is4pY/X=70u*2^(-28u)<1 for u>=1. P=1 modE and2n=R+1 give positive retained h. The previous projection/input argument applies unchanged.

For every j, u=1 mod24. The expression A=2^(42u-1)+2^(7u-1)+2 gives A=3 mod5,0 mod7,0 mod17. For5, p=5 mod6 and the psi recurrence coefficient2A=1 has period-six values0,1,1,0,-1,-1. For7 and17, coefficient2A=0 and p=3 mod4 give c=-1. Since p's only possible prime divisors are5,7,17, gcd(c,p)=1 universally (17 need not divide p when j=0, which causes no problem).

Because p=3 mod4, f=D,S=Delta*c give Ns=Delta, f^2=1 modc and gcd(c,f)=1. CRT z=p mod4p, z=R modc is compatible and positive, with z=3 mod4. The Pell pair at2p is(-1,0) modf and at4p is(1,0). Therefore psi_A(z)=c modf, and the same odd-quotient proof yields V=-c modf,V=-R modc and positive integral T. The inverse is1/c, nonintegral.

Necessary outer restrictions were checked exactly. For N even, q=1,J=0 mod3 and Q=0 mod3 force R=0 mod3, contrary to R=2. For N odd, q=2,J=1 mod3 gives the necessary genuine-mask condition MC+2MF_source=2 mod3. This cannot be treated as automatic. If3|N then7|J, requiring60u-1=4*2^j-1=0 mod7, equivalent to j=1 mod3.

Independent code audit_simple.py uses an MSB double/add Pell recurrence, with no upstream Python or schedule execution. SIMPLE_INDEPENDENT_CHECKS.json records64 modular family checks, exact j=0 norms/ratio/index/projection, positive loading at every odd rank I=3..33, and modular auxiliary quotient/CRT checks. The exact c has1429 bits and auxiliary index1433 bits, agreeing with the author's receipt; the huge final auxiliary tuple is not materialized.

A particularly simple overclaim guard exists here: j=0 gives Y exponent6, so the required scale3t<=6 implies t<=2, while any genuine compiler has t=dN>=5. Thus even the smallest exact inner fixture is immediately excluded from the proposed genuine completion, without needing its outer packing equations.

No genuine-compiler solution of the full residual interface, accepted-input language separation, or generic-zero normalization is established by this addendum.
