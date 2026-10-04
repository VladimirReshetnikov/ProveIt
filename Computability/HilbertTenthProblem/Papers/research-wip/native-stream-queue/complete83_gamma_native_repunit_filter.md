# Fixed repunit divisors extend the genuine-history prime filter

The actual packed index has a useful divisor beyond its controlled powers of three and five. Fix a parity-normalized compiler, an accepted positive input, an adequate spatial power of five h, a finite u>=2, and a **reference length N0 which is a power of five**. Define

    B=2^d, E=dh, J0=(B^N0-1)/(B-1).

Choose any fixed positive divisor D0 of J0 and put

    n=3^u*E*D0.

These choices precede the actual time padding. There are genuine accepting histories with fresh positive witnesses for the unchanged84 parent and its independent-gamma83 forward chart such that

    n divides the actual packed index R,
    gcd(Delta,2^(2n)-1)=3,
    gcd(Delta,(2^(2n)-1)/3^(u+1))=1,
    v3(Delta)=1 and v3(m)<=1.

The reference length is an arithmetic divisor parameter; it is not claimed to be the length of an accepting history. Later actual lengths are sufficiently large powers of five divisible by N0. This strictly extends the order class 2*3^u*5^j for **every** actual fixed compiler. It does not control all prime factors of the alias modulus or settle independent-gamma83.

No source row, coordinate or operation count changes. The [fresh helper](complete83_gamma_native_repunit_filter.py) checks the exact common packing cone of the saved84 and83 sources as inert data. All witness changes use the already allowed dummy-bit geometry.

## 1. The divisor is in the actual source

The complete [84 source](complete84_scaled_strong_output.json) and [independent-gamma83 source](complete83_independent_gamma_scout.json) have the same thirteen-row ancestor cone for r_lhs. Its literal ports satisfy

    repunit=Bm1*Jrep, q=repunit+1,
    gap=repunit*(q-F)+(q-F-Z)=q*q-Z-q*F,
    Lm1=q*q-1,
    r_lhs=gap*Lm1+(MC+q*MF)*Jrep.

MF is the **already shifted source coefficient**, not the native mask. Since q*q-1=Bm1*Jrep*(q+1), there is an all-ring identity

    r_lhs=Jrep*[Bm1*(q+1)*(q*q-Z-q*F)+MC+q*MF].       (1)

This follows from the paid producers without a zero equation or an integer division operation. The helper independently expands the complete thirteen-row cone in its six free ports and checks all twelve resulting coefficients against (1). At a native constructed history, Jrep=J=(B^N-1)/(B-1) and R=r_lhs, so J divides R.

If N=N0*v, the integer geometric identity gives

    J=J0*(1+B^N0+...+B^((v-1)*N0)).                  (2)

Thus **J0, and hence D0, divides R for every later history with N0|N**, regardless of its dummy bits or convolution values. It also divides each change of R: the literal switch coefficient Gamma contains q^2-1, which is divisible by J0. No new divisibility equation is introduced.

The reference repunit satisfies

    J0 is odd, J0=1 mod3, J0=1 mod5.                 (3)

Indeed B is even, B=-1 modulo3, and N0 is odd. Modulo5, B=2 and N0=1 mod4, so B^N0=2, while B-1 is invertible. Consequently J0 and D0 are coprime to30 and in particular to E and3. Also **17 does not divide J0**: J0 divides 2^(dN0)-1, and the order8 of2 modulo17 cannot divide the odd exponent dN0.

## 2. The reference divisor does not make padding circular

The [three-power history theorem](complete83_gamma_native_three_power_control.md) proves two actual source facts:

* Gamma is a unit modulo dN and has exact3-adic valuation1, including either value of the optional high-field correction.
* For N>75d the Boolean lower dummy slots realize every residue modulo3dN. Hence the baseline can satisfy Rbase=dh mod dN and Rbase=0 mod9 simultaneously.

The parity-normalized compiler has R=0 modulo3 before any new choices, as required for the second fact. This fixed recipe is available for every c.e. language by the separately proved [window padding](gamma_parity_padding_scout.md). For a previously fixed compiler outside this parity class, the hypothesis is not silently removed.

Choose h, u, N0 and D0 first. This fixes n and the finite quantities

    Aminus=2^n-1,
    Q=3^(u-2)*Aminus,
    spacing=2*3^u*h*D0=2n/d.

Only then choose the temporal power of five Htime so that N=h Htime is divisible by N0, accommodates the original accepting computation, and satisfies all old padding bounds together with

    N>75d, N>2x, Htime>=25,
    Htime>5*((spacing/h)*(Q-2)+1).                   (4)

This is possible because the reference dimensions are finite powers of five and Htime can grow through arbitrarily large such powers. Enlarging Htime changes q, Gamma and the actual baseline, but **does not change D0 or any modulus used to size the grid**. Formula (2) preserves the reference divisor at every later length.

## 3. The same physical switches impose the needed residues

Preset upper dummy bits at i_j=spacing*j for 0<=j<=Q-2, with their target upper bits initially zero. Apply the lower-bit Boolean lemma to set Rbase=dh mod dN and 9|Rbase. Lower and upper bit coordinates are independent even if they share a cell; the permitted digit remains between0 and3.

Put L=4N/5 and G=Gamma*(B^L-1). Condition (4) keeps every source, destination and field shift by1 orh strictly inside the word:

    i_max+h<N/5, i_max+L+h<N.

The exact packed index after moving a prefix of k upper bits is

    R_k=Rbase-2G*S_k,
    S_k=sum_(j<k) B^(spacing*j), 0<=k<Q.             (5)

As before, v5(B^L-1)=v5(dN), so every move preserves the temporal congruence. The actual Gamma theorem gives v3(G)=2. Because D0 is a ternary unit,

    v3(B^spacing-1)=v3(2^(2n)-1)=u+1.

Thus S_k=k mod3^(u-2). After computing the baseline, the residue

    k=(Rbase/9)*(2G/9)^(-1) mod3^(u-2)              (6)

makes R_k=0 mod3^u. For u=2 the modulus is1 and this condition is empty.

For every prime p dividing Aminus, B^spacing=2^(2n)=1 modp. Such p is odd and is not3. Set s_p=v_p(G) after the actual time choice; no upper bound on this valuation is needed. With r_base=(Rbase-1)/2, equation (5) gives

    (R_k-1)/2 = r_base-G*k modp^(s_p+1).            (7)

The geometric sum is reduced only modulo p; multiplication by G supplies the higher modulus. One residue of k modulo p makes the s_p-th base-p digit equal to p-1 and hence forces a central-binomial carry.

The joint CRT modulus is 3^(u-2)*rad(Aminus)<=Q, so one representative 0<=k<Q satisfies (6) and all carry conditions. The primes, their moduli and Q were fixed before Htime; only the required residues are determined afterward. This is the same noncircular prefix argument as the preceding theorem.

The final R is divisible by3^u and E. It remains divisible by D0, either directly from (1)–(2) or because D0 divides Rbase and G. These three divisors are pairwise coprime, so n divides R. Both are odd, and R/n is odd.

## 4. Native discriminant and positive-witness consequences

At the resulting native history,

    X=2^R,
    2Y=sum_(j=0)^((R-1)/2) binom(R-1,(R-1)/2+j)*X^j,
    a=Y(X+1), Delta=(a+1)(a+3), H=4a+3.

Oddness of R/n gives 2^n+1 | a. Hence Delta=3 mod(2^n+1) and gcd(Delta,2^n+1)=3. The factor 2^n+1 has exact3-adic valuation u+1 because v3(n)=u. Therefore a is divisible by9 and v3(Delta)=1.

At every prime p dividing Aminus, the genuine divisibility n|R fixes X=1 modulo p. The imposed carry makes the central binomial coefficient zero modulo p. Binomial symmetry gives a=1/4 and Delta=65/16 modulo p. Neither5 nor13 divides Aminus: their orders4 and12 cannot divide the odd exponent n. Thus gcd(Delta,Aminus)=1.

The coprime plus and minus factors prove gcd(Delta,2^(2n)-1)=3. Their product has exact3-adic valuation u+1; dividing by 3^(u+1) removes its whole3-part and gives the stated coprime quotient. Since m divides2Delta, m is coprime to that odd quotient and v3(m)<=1.

The positive-history transfer is unchanged from the pinned three-power theorem. Every change is an allowed bit of the existing ignored digit; local clauses, masks, Start and End, and the ordinary external input remain intact. The same nonwrapping identities and digitwise 2C+F<q/2 estimate give the original positive slack. The actual population, low bits, index bounds and temporal congruence persist. The inherited converse supplies fresh positive84 witnesses at this actual modified R, followed by the positive independent-gamma forward map. No old Pell tuple or fictitious independent native parameter is substituted.

Several fixed divisors can be combined: finitely many reference powers of five divide their largest one, their repunits all divide its repunit by (2), and the least common multiple of the chosen divisors is a divisor of that single repunit. After fixing this finite D0, the same construction applies. This does not infer simultaneous control of infinitely many primes on one finite history.

## 5. Strict extension for every actual compiler

Write its actual fixed d as 5^a0 and take N0=5. Then

    J0=1+2^d+2^(2d)+2^(3d)+2^(4d).

Let ell be any prime divisor of J0. It is odd and different from3 and5. Since (2^d-1)J0=2^(5d)-1, the order of2 modulo ell divides 5^(a0+1). A proper divisor would divide d, giving 2^d=1 mod ell and J0=5 mod ell, forcing ell=5. Consequently

    ord_ell(2)=5^(a0+1).                             (8)

Choose any prime p dividing 2^ell-1. Its order divides the prime ell and cannot be1, because no prime divides2-1. Thus ord_p(2)=ell. This is outside every previous class 2*3^u*5^j, since ell is a prime other than3 or5. But choose D0=ell; then ell divides n, p divides Aminus, and the new genuine-history construction excludes p.

Only prime factorization of finite integers is used. No primitive-divisor or prime-distribution theorem is needed. This is a strict extension for each actual compiler even when its d is enormous.

A small illustration, **not an instantiated universal compiler**, is

    d=5, N0=5, J0=(2^25-1)/(2^5-1)=601*1801,
    ord_601(2)=ord_1801(2)=25,
    ord_3607(2)=601, ord_28817(2)=1801.

Taking D0=601 or1801 would suffice for the corresponding new prime and avoids the larger exponent using all of J0. The helper checks each displayed prime and exact order afresh. It does not assert that the real compiler has d=5 or that these particular primes are excluded for every fixed coefficient instance. The all-compiler statement is (8) and the subsequent existence proof.

## 6. The remaining boundary at17 and in the full order

This construction still uses X=1 or X=-1 in the native formula. The retained native condition R=3 mod4 makes X either8 or9 modulo17 throughout these actual histories; neither value is1 or-1. The order8 at17 cannot divide2R, so enlarging odd divisors of R cannot reach those two values there. The new reference repunit also has no factor17.

The [residual-order obstruction](gamma83_residual_order_obstruction.md) remains consistent with this extension. Its CRT proof also applies to the present odd exponent n: 17 does not divide n, and the order8 at17 cannot divide2n. Its free arithmetic hosts can therefore retain these stronger finite residues while forcing large17-power divisors of m. This is still a nonnative relaxation, not a realization by the native formula or history controller.

A different native argument is needed to control Delta at17 or the full intersection with ord_H(2). The finite-digit rule does not turn arbitrary formula indices into histories. No full bound on m, sufficient power-test occurrence or ordinary-input language conclusion follows. Increasing N0, h oru constructs different finite histories; there is no infinite diagonal or compactness step.

## 7. Bounded fresh evidence and replay

The [helper](complete83_gamma_native_repunit_filter.py) authenticates seven predecessor files as inert bytes. Its [receipt](complete83_gamma_native_repunit_filter.json) saves the common thirteen-row source cone and its twelve complete polynomial coefficients, thirty-six exact nested-repunit identities, five trial-prime/exact-order certificates, and ten synthetic prefix/CRT models checking thirty-four prime-digit lifts.

The geometry models deliberately use small parameters. Nontrivial reference examples have d=1, which is not a compiled-program width; one also uses a proper divisor D0=31 of the reference repunit for N0=25. Models with d=5 use N0=1. The named d=5,N0=5 illustration checks its reference factor and prime orders only. No enormous time grid or native binomial/Pell value is materialized. CRT models use synthetic Gamma and baseline residues, not claimed compiler coefficients. The genuine-history assertion is the unrestricted proof above using the pinned actual compiler interfaces.

No predecessor Python or archived code is executed or imported. No old artifact, source circuit or repository file changes. Checks use explicit exceptions and recursive type-exact receipt comparison, rejecting duplicate keys and nonfinite JSON. From any directory:

    python3 complete83_gamma_native_repunit_filter.py --root ABS_WIP --expect ABS_JSON
    python3 -O complete83_gamma_native_repunit_filter.py --root ABS_WIP --expect ABS_JSON

Use --output FILE to emit the deterministic receipt. Fresh normal and -O exact receipt replays from / both passed. No new paid arithmetic bound is claimed.
