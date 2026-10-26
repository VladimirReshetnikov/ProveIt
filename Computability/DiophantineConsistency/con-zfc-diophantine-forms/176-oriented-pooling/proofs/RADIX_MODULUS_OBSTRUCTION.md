# A precise obstruction to identifying the CRT modulus with the radix

In the retained source, N=B^x is the CRT range modulus, whereas
q=(BH)^x is the digit radix. Replacing N by q would superficially remove
the separate B^x request. It destroys completeness.

After the existing sign and first-binomial bootstrap, all representatives
are nonnegative and

    B=binom(F+t,t)>F+t,   H>C,   x>=t,   q=(BH)^x,

where C is the actual index representative. The retained index condition is

    B divides C+F+1.

The strict index range N|binom(C,t), after the proposed replacement,
would become q|binom(C,t). However

    0<=binom(C,t)<=max(1,C)^t < H^x < (BH)^x=q.

The strict bound holds because H>=2+4C and B>=2. Divisibility therefore
forces binom(C,t)=0, so 0<=C<t. Now

    0<C+F+1<=F+t<B,

contradicting B|(C+F+1). Thus the changed system has no solutions at all,
regardless of whether the proof calculus has a refutation. The extra
prime components of H are not a harmless padding issue: using the large
digit radix as the range modulus forces a GLOBAL CRT representative to
be an actually small integer, defeating the simultaneous row encoding.

Replacing the exact-power condition on N merely by N|q is also insufficient
for the old soundness proof. It gives no lower bound v_p(N)>=x*v_p(B) at
the selected row primes. That depth is what turns a local congruence into
the exact local ledger equality using L_local<2^x. No replacement depth
certificate with fewer coordinates has been proved here.
