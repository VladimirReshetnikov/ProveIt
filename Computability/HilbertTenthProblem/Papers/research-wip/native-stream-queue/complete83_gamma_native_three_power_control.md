# Every finite ternary power can be imposed on a genuine native history

Fix a compiler in the even-selector, odd-tile-alphabet class, an accepted positive input, and an adequate canonical spatial padding h. Put E=dh, where d and h are powers of five. For **every fixed integer u>=2**, there are genuine accepting histories with fresh positive witnesses for the unchanged 84-operation parent and its independent-gamma83 forward chart such that

```
3^u*E divides the actual packed index R,
gcd(Delta, 2^(2*3^u*E)-1)=3,
gcd(Delta, (2^(2*3^u*E)-1)/3^(u+1))=1,
v3(Delta)=1 and v3(m)<=1.
```

Thus any finite set of odd primes other than 3 whose orders of 2 divide some `2*3^u*5^j` can be excluded from Delta and the alias modulus m on one genuine history. New examples include 19, 73 and 262657, whose orders are 18, 9 and 27. By the separately proved [harmless parity padding](gamma_parity_padding_scout.md), this compiler class is available for every c.e. language through newly compiled fixed numerals. The theorem does not silently change a previously fixed compiler instance.

The construction uses two independent bits of the existing ignored digit. A new Boolean subset lemma first sets R modulo 9 and dN simultaneously. A later prefix of upper-bit moves controls the higher ternary digits and the finite binomial-carry conditions together. All moduli and grid sizes are fixed before time padding is chosen.

No source row, supplied coordinate, operation count or ordinary-input interface changes. The [independent-gamma83 language](complete83_independent_gamma_scout.md) remains unresolved; these finite filters give no bound on the remaining factors of m.

## 1. The actual switch coefficient has exact valuation one

Use the actual layout in [the 76 compiler source](../../verification/explore_fixed_raw_universal_76.py), lines 94–148, and [the modified wrapper](complete75_half_binomial_compiler.py), lines 21–57. Write a_T for its tile-alphabet size, to distinguish it from the later Pell parameter a. The clause/copy count m_layout is even, and its anchor unit and bands have the literal forms

```
M0=m_layout+6*a_T-3, Emax=27*M0,
H=Emax+24*M0+3*a_T+1,
T1=H+2*Emax+a_T+1, T2=T1+2*Emax+1,
g_high=T2+Emax+1.
```

The center-field polynomial and the right-field coefficient are

```
DC=r0^(3a_T)+r0^(H+a_T)+r0^(8M0)+r0^(24M0)
   +sum_e c_e*(r0^(T1-e)+r0^(T2-e)) + chi*r0^g_high,
DR=r0^H,
chi in {0,1}.
```

Here chi is the **actual** optional high correction selected to make the five-adic coefficient a unit. It is not an extra free choice in this construction. Since b is an odd power of five, r0=2^b=-1 modulo 3. The anchor unit and Emax are odd, H has the parity of a_T, T1 is odd, T2 is even, and g_high is even. Each paired center-band term cancels modulo 3, regardless of its coefficient. The four explicit monomials contribute `(-1)^a_T+3`, while DR contributes `(-1)^a_T`. Therefore

```
DC-DR=chi mod3.                                        (1)
```

With B=2^d, N=h Htime, q=B^N and all these exponents powers of five, B, q and B^h are -1 modulo 3. For the exact switch coefficient

```
Dfield=DC+B*DR+B^h,
Gamma=r0^e_*(q^2-1)*(1+q*Dfield)
```

we obtain

```
1+q*Dfield=2-chi !=0 mod3.
```

Also `v3(q^2-1)=v3(4^(dN)-1)=1`, because 3 does not divide dN. Hence

```
v3(Gamma)=1,
Gamma/3=(-1)^e_* *dN*(2-chi) mod3.                     (2)
```

This applies to both choices of the optional high correction and to all the compiler parity classes. Independently, the compiler's existing correction guarantees that Gamma is a unit modulo dN. No arbitrary coefficient model replaces these two source facts.

Turning on a lower dummy bit at an internal cell i changes the actual packed index by `-Gamma*B^i`. Moving an upper bit from i to i+L, where L=4N/5, changes it by `-2Gamma*B^i*(B^L-1)`. Since dL=4dN/5 has no factor 3,

```
v3(B^L-1)=1,
G=Gamma*(B^L-1) has v3(G)=2.                           (3)
```

Every upper move therefore preserves R modulo 9. Upper moves alone could not change an incorrectly initialized next ternary digit. The lower-bit construction below supplies the missing control.

## 2. A Boolean subset lemma modulo 3dN

Let d,N be positive powers of five with N>75d. Put

```
M=dN, T=N/5, B=2^d.
```

Every residue modulo **3M** is a Boolean subset sum of the distinct weights

```
{B^(4j):0<=j<T} union {B}.                             (4)
```

The original [five-adic proof](../../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md) gives a bijection

```
{B^(4j) mod M:0<=j<T}={1+5d*t mod M:0<=t<T}.
```

In addition all B^(4j) equal 1 modulo 3, while B equals -1 modulo 3. To construct a subset for a target with residues z modulo M and v modulo 3, choose epsilon in {0,1} so that z-epsilon*B is a unit modulo 5. Select the unique k modulo 15d satisfying

```
k=z-epsilon*B mod5d,
k-epsilon=v mod3.
```

Its representative satisfies `1<=k<15d<T` and 5 does not divide k. The numerator below is integral, so put

```
sigma=(z-epsilon*B-k)/(5d) modT,
t0=(sigma-k*(k-1)/2)/k modT.
```

Division by k is permitted because T is a power of five. Choose the k distinct cyclic residues `t0,...,t0+k-1` modulo T. Their associated weights `1+5d*t`, plus the optional epsilon*B, have sum z modulo M. Their sum modulo 3 is k-epsilon=v. The original bijection gives distinct actual cell indices 4j, with the optional index 1 distinct from them. Thus this is a Boolean subset, not a signed combination or unrestricted multiplicity argument.

All indices still lie at most 4N/5-4. With Htime>=25 their shifts by 1 and h are internal, exactly as in the original lemma. The stronger condition N>75d changes only how much independent time padding is selected.

## 3. Initialize the actual index modulo 9

In the parity-normalized compiler the literal mask table gives R=0 modulo 3 for every canonical odd-N history, independently of its data and dummy choices. This is the table proved in [the small-prime note](complete83_gamma_small_prime_digit_rules.md), not a newly assumed residue.

Start with any genuine word and any desired preset pattern of upper dummy bits. Leave the lower bits initially zero. Write its actual packed index as R0. Both Gamma and its valuation are fixed after the word's dimensions and coefficients have been fixed. For a Boolean lower subset with weight sum K, the exact source identity is

```
Rbase=R0-Gamma*K.
```

To force `Rbase=dh mod M` and `Rbase=0 mod9`, require

```
K=(R0-dh)*Gamma^(-1) modM,
K=(R0/3)*(Gamma/3)^(-1) mod3.                         (5)
```

These residues are meaningful by (2) and the compiler's five-adic unit property. The new lemma realizes them simultaneously, preserving every allowed digit, marker and local predicate. Thus

```
Rbase=dh mod dN, 9 divides Rbase.                      (6)
```

More generally this argument can prescribe any of the three residues modulo 9 congruent to R0 modulo 3. Therefore, within each actual fixed compiler's permitted class modulo 3, there is no additional fixed packing obstruction modulo 9. Only the zero class is used below. Other compiler classes cannot change R modulo 3 by these dummy operations; harmless parity padding changes the fixed recipe when that is desired.

## 4. The simultaneous higher-power and finite-prime construction

Choose in this order:

1. Fix an accepted positive input and an adequate spatial power of five h; E=dh is now fixed.
2. Fix the finite target u>=2 and define

```
Aminus=2^(3^u*E)-1,
Q=3^(u-2)*Aminus,
spacing=2*3^u*h.
```

3. Choose the temporal power of five Htime large enough for the original accepting history, N=h Htime>75d, N>2x, Htime>=25, and

```
Htime>5*((spacing/h)*(Q-2)+1).                         (7)
```

The prime divisors of Aminus and the bound Q are fixed **before** this time choice. The later q, Gamma and actual baseline are not assumed fixed earlier.

Preset upper dummy bits at `i_j=spacing*j` for `0<=j<=Q-2`; all their eventual target upper bits are zero. Align the independent lower bits using (5). Let L=4N/5. If i_max=spacing*(Q-2), condition (7) gives

```
i_max+h<N/5,
i_max+L+h<N.
```

The sources, destinations and their field contributions are nonwrapping. Lower and upper bits may share a cell but are independent bit coordinates; the permitted digit is then 3. Move exactly a prefix of k upper bits to their targets i_j+L. The actual new index is

```
R_k=Rbase-2G*S_k,
S_k=sum_(j=0)^(k-1) B^(spacing*j), 0<=k<Q,
G=Gamma*(B^L-1).                                     (8)
```

Every move preserves `R=dh mod dN`: the exact five-adic valuation is `v5(B^L-1)=v5(dN)`, as in the preceding genuine-history construction. Equation (3) also says G/9 is a ternary unit.

The chosen spacing has the stronger property

```
v3(B^spacing-1)=v3(2^(2*3^u*E)-1)=u+1.
```

Hence `S_k=k mod3^(u-2)`. Since 9 divides Rbase, condition `R_k=0 mod3^u` is equivalent to the single residue

```
k=(Rbase/9)*(2G/9)^(-1) mod3^(u-2).                  (9)
```

For u=2 this modulus is 1 and there is no additional ternary condition. There is no division by G modulo 3^u; the common factor 9 has first been removed.

For every prime p dividing Aminus, `B^spacing=2^(2*3^u*E)=1 modp`. This prime is odd and is not 3. After the actual baseline has been computed, set s_p=v_p(G), a finite valuation of a positive integer. With r_k=(R_k-1)/2 and r_base=(Rbase-1)/2, equation (8) gives

```
r_k=r_base-G*k modp^(s_p+1).                         (10)
```

Only `S_k=k modp` is needed for (10); multiplication by G supplies the additional p^s_p. Because G/p^s_p is a unit, one residue of k modulo p makes the s_p-th digit of r_k equal to p-1. That digit forces a carry in r_k+r_k and thus p divides the central binomial coefficient.

The Chinese remainder theorem combines (9) with all these prime residues. Its modulus is

```
3^(u-2)*rad(Aminus) <= Q.
```

It therefore has a representative `0<=k<Q`, within the preset prefix capacity. Squarefreeness of Aminus is unnecessary. The valuations s_p and the residue in (9) are computed only after q and the baseline are fixed, but their moduli and the prefix capacity were fixed in advance. This resolves the possible circularity.

The resulting actual index satisfies `E|R_k` from its preserved congruence modulo dN and `3^u|R_k` from (9). As E is a power of five, their product divides R_k. Its quotient by this odd product is odd, because the source's low-bit condition R=3 modulo 4 is preserved.

## 5. Native residues, positive extension and remaining scope

Use the exact native formula

```
r=(R-1)/2, X=2^R,
C_R=binom(2r,r), 2Y=sum_(j=0)^r binom(2r,r+j)*X^j,
a=Y(X+1), Delta=(a+1)(a+3), H=4a+3.
```

Since `R/(3^u E)` is an odd integer, `2^(3^u E)+1` divides a. Therefore

```
Delta=3 mod (2^(3^u E)+1),
gcd(Delta,2^(3^u E)+1)=3,
v3(2^(3^u E)+1)=u+1.
```

In particular a is divisible by 9, so v3(Delta)=1. This already follows from the parity class's initial 3|R; no carry is required at the prime 3.

For each p dividing Aminus, the actual divisibility `3^u E|R` fixes X=1 modulo p. The carry in Section 4 gives C_R=0 modulo p. Symmetry of the binomial row yields

```
a=1/4 modp, Delta=65/16 modp.
```

The primes 5 and 13 cannot divide Aminus, since their orders 4 and 12 cannot divide the odd exponent 3^u E. Thus all these discriminant residues are nonzero and `gcd(Delta,Aminus)=1`. The coprime plus and minus factors give the headline gcd equal to 3. Their product has exact 3-adic valuation u+1, so division by **3^(u+1)** removes the whole 3-part. Since m divides 2Delta, it is coprime to this odd quotient and v3(m)<=1.

All changes above occur at the existing ignored digit. They preserve the actual old accepting computation, Start and End, original fixed masks, and exact convolution. At every cell the permitted digit is still between 0 and 3. The authenticated [finite-prime history proof, Section 4](complete83_gamma_native_finite_prime_avoidance.md#4-the-full-genuine-history-and-positive-witness-interface) gives the same digitwise `2C+F<q/2` estimate and, using N>2x, the original positive slack. The population identity, q^2<R<q^4, R=3 modulo 4 and `R=dh mod dN` are retained. Its kernel converse and complete positive composition therefore construct fresh positive witnesses at the modified actual R. This is a fresh extension, not a presumed tuple map or an appeal to soundness of the 83 chart.

Every fixed finite set of odd primes whose orders divide some `2*3^u*5^j`, apart from 3, is covered by choosing adequate h and u first and then Htime. This includes the previous order classes and the newly checked examples `ord_19(2)=18`, `ord_73(2)=9` and `ord_262657(2)=27`. It still excludes neither all primes nor the order class with 2-adic valuation at least two, such as the orders 4, 12 and 8 at 5, 13 and 17. The native R is odd, so those primes cannot acquire X=1 or -1 merely through divisibility of R.

For each requested finite u the construction uses a potentially much larger, but finite, history. It supplies no one history with an infinite ternary valuation, no diagonal/compactness argument, and no control of all remaining prime factors entering ord_H(2). Witness construction may factor finite integers and perform finite CRT searches; these are not newly paid circuit operations.

## 6. Bounded fresh evidence

The [fresh helper](complete83_gamma_native_three_power_control.py) authenticates nine predecessor files as inert bytes and executes none of them. Its [receipt](complete83_gamma_native_three_power_control.json) records:

* sixteen exact layout-parity models, with arbitrary paired center coefficients and both values of the high correction;
* 144 small coefficient models checking the exact Gamma valuation and its divided residue;
* constructed Boolean subsets for all 375 targets modulo 3*125 and all 9,375 targets modulo 3*3125, with independent bitset subset-coverage checks; a further 162 target samples at d=25,N=3125;
* thirty-six synthetic simultaneous CRT models at four tower/grid geometries, checking 162 minus-prime digit lifts;
* 960 independent geometric-sum checks and six exact prime/order checks.

The subset stream hashes authenticate the selected finite index lists; the receipt does not store a claimed full compiler history. The tower models use synthetic Gamma and baseline residues. They verify the required modular identities and genuine grid inequalities but do not assert their coefficient values came from an actual compiler. Full q, native a, H, histories and Pell tuples are not materialized. The unrestricted source valuation, Boolean lemma and genuine-history theorem are the proofs above, with their explicitly authenticated compiler interfaces.

The helper uses explicit exceptions under Python -O and recursive type-exact JSON comparison, rejecting duplicate keys and nonfinite values. From any working directory:

```
python3 complete83_gamma_native_three_power_control.py --root ABS_WIP --expect ABS_JSON
python3 -O complete83_gamma_native_three_power_control.py --root ABS_WIP --expect ABS_JSON
```

Use --output FILE to emit the deterministic receipt. Fresh normal and optimized exact receipt replays from / passed. No predecessor artifact, source circuit or repository file is changed.
