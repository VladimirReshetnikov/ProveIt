# Genuine accepting histories can avoid the native ternary exclusion

For every accepted positive input of every inherited fixed compiler, there are genuine positive parent witnesses whose exact native half-binomial parameter satisfies **a=0 modulo9**. For the unchanged [independent-gamma83 chart](complete83_independent_gamma_scout.md), their fixed-history alias modulus therefore satisfies **v3(m)<=1**. This is a construction on genuine accepting histories, not a freely chosen half-binomial index or diagnostic modulus.

It shows that the earlier [v3(m)=2 exclusion class](complete83_gamma_native_ternary_exclusion.md) cannot contain all accepting histories of any accepted input. It does not prove a false-input alias, either power test, or the soundness of independent-gamma83. Other prime factors of the native Pell order remain uncontrolled. No source row, operation count, witness domain or fixed-program numeral changes.

## 1. Actual compiler hypotheses and the unused upper bit

Fix an accepted positive ordinary input x and its genuine padded computation. Use the existing canonical padding: b,d,h,Htime,N are powers of five, d=b*L_layout, N=h*Htime, Htime>=25, N>25d and N>2x. Write

```
r0=2^b, B=2^d, q=B^N, t=dN, M=dN.
```

These are witness choices allowed by the existing compiler, not a claim that every arbitrary positive tuple has a five-power duration. Since its fixed radix satisfies 2^b>=16 and b is a power of five, b>=5 and r0>=32.

The [modified compiler, Sections1–5](complete75_half_binomial_compiler.md) explicitly permits its selected ignored digit e_* to be any of0,1,2,3. Its lower and upper binary bits have weights r0^e_* and 2*r0^e_*. Both are ignored by every computation clause, selector and anchor. The extra upper bit need not vanish for mask soundness or the carry bounds; it was simply left zero by the older canonical completeness construction. We use it here while leaving all lower bits available for the existing five-adic adjustment.

Let C be the actual content word, W=2^(2dx+b) its fixed End marker and Z=C-W. Let F be the actual field with the intended temporal rotation B^h. Put

```
D=DC+B*DR+B^h,
Gamma=r0^e_* (q²-1)(1+qD).
```

This Gamma is positive and is a unit modulo M by the same fixed compiler condition 2DC-DR!=0 modulo5. For any changed ignored digit of weight z at a cell i with i+1<N and i+h<N, the actual integer changes are

```
Delta C=Delta Z=z B^i,   Delta F=D z B^i,
Delta R=-(q²-1)(1+qD) z B^i.                 (1)
```

Here R is the actual shifted packed index, with the source's MF_source=MF_native+B-1. Equation(1) follows by subtracting its literal packing formula; no independently supplied R is introduced.

## 2. Align the lower bits, then switch two upper bits

Initially set the UPPER dummy bit at cells0 and2, and set every other upper dummy bit and every lower dummy bit to zero. These changes preserve the same genuine computation. Compute its actual baseline R. Apply the unchanged [Boolean five-adic subset theorem](../../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md) to the LOWER dummy bits in cells

```
{4j:0<=j<N/5} union {1}
```

to arrange R=dh modulo dN. This theorem works for every baseline residue, so the preset upper bits cause no restriction. A digit carrying both a selected low bit and the preset upper bit is3, still allowed. There is no collision of bit coordinates.

Put L_swap=4N/5. There are now two independent switches: move the upper bit from cell0 to L_swap, or from cell2 to L_swap+2. The target upper bits are zero; all low bits stay unchanged. Both source and target cells lie below N-h and N-1, because

```
L_swap+2+h <=21N/25+2 < N,
```

and N>25d with d>=5 implies N>=625. The old low-control cells end at L_swap-4, so the two target cells are also outside that set. Nonwrapping temporal and spatial contributions in(1) are valid for both switches.

The exact elementary five-adic valuation is

```
v5(B^L_swap-1)=1+v5(dN/5)=v5(dN).
```

Thus B^L_swap=1 modulo M. By(1), the two changes in R are

```
Delta R_0=-2Gamma(B^L_swap-1),
Delta R_2=-2Gamma B²(B^L_swap-1).             (2)
```

Each preserves R=dh modulo dN, and consequently preserves the required temporal equality 2^R=B^h modulo q-1. The computation, ordinary input and fixed program have not changed.

## 3. Three choices force a ternary digit2

Since d and N/5 are powers of five,

```
v3(B^L_swap-1)=v3(2^(4dN/5)-1)=1.
```

The absence of a factor3 in d is essential here. Let s3=v3(Gamma)+1 and G=Gamma(B^L_swap-1). Then v3(G)=s3, and B²=1 modulo3. The index stays3 modulo4: all dummy changes contain the factor r0^e_* and preserve the existing low bits. In particular r=(R-1)/2 remains an odd integer.

Consider precisely three words: use neither switch, only the first switch, or both switches. Their corresponding half-indices are

```
r_base,   r_base-G,   r_base-G(1+B²).
```

Modulo3^(s3+1) these are r_base, r_base-G and r_base-2G. Their digits below position s3 agree, and their digit at position s3 takes all three values0,1,2 because G/3^s3 is a unit modulo3. Choose the word for which that digit is2. This reasoning uses exact integer congruences and remains valid if Gamma has arbitrarily large finite3-adic valuation. It does not assume the valuation is small or require factoring the native H.

At the chosen genuine word use the exact native formula

```
X=2^R,  r=(R-1)/2,
2Y=sum_(j=0)^r binom(2r,r+j) X^j,
a=Y(X+1), Delta=(a+1)(a+3), H=4a+3.
```

The pinned ternary theorem states a=6 modulo9 precisely when every ternary digit of r is0 or1 and r=0 modulo3; otherwise a=0 modulo9. Our forced digit2 proves the latter. Hence

```
v3(Delta)=1,  v3(H)=1,
v3(g)<=1,  v3(m)<=1,
g=gcd(2Delta,ord_H(2)), m=g/gcd(g,2d).        (3)
```

Because d is a power of five, the last division removes no factor3. No exact value0 or1 for v3(g) is asserted: orders at other prime divisors of H can still contribute a factor3.

## 4. All original positive-source conditions survive

All three switch choices retain every native mask and genuine computation clause. The modified compiler's no-carry bound includes arbitrary allowed digits0..3: every raw coefficient of DC*C+DR*Rword is at most r0/4-2. Adding the intended whole-cell temporal word contributes at most3, so every F coefficient is at most r0/4+1. Each C coefficient is at most3. Thus every coefficient of2C+F is at most r0/4+7, and

```
2*(r0/4+7)<r0-1  for r0>=32,
2C+F <=(r0/4+7)*(q-1)/(r0-1)<q/2.            (4)
```

All coefficients are nonnegative and below the radix, so this is an integer positional bound. Z=C-W remains strictly between0 and C because the unchanged Start remains and W is the distinct End marker. Padding gives 2dx<t<q/2. Consequently the actual retained original slack is strictly positive:

```
alpha=q-C-Z-F-2dx > q-2C-F-2dx > q/2-t >0.   (5)
```

This replaces the older q/3 margin, which had assumed zero upper bits. It uses the already chosen fixed radix; no new numeral recipe or enlargement is introduced.

The field's low origin conditions remain valid for arbitrary upper bits: e_*>1, every changed bit is an ignored dummy, the genuine Start is unchanged, and its temporal predecessor is not Start. The same exact inverse-population identity therefore gives popcount(R)=3dN+2. From F<q/2 and Z<C<q/4, the shifted S'=(Z-1)+qF has S'<q²/2+q/4, so the positive packed index lies between q² and q^4. It remains3 modulo4 as already noted. These are stronger than the kernel converse's lower bound3q+1<=R.

The [positive half-binomial converse, Section6](pell_kernel_half_binomial42.md) consequently supplies fresh first/main/strong witnesses at this actual R and exact Y. The restored alignment supplies the positive transport quotient for the actual field. The input marker is unchanged, and u=2dx+b<R; the input Pell construction and increasing quotient recurrence give positive input slacks and positive gamma-rho. These are precisely the hypotheses used in [the full positive completeness composition](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md#6-full-positive-completeness-composition). Its subsequent normalized-strong, asymmetric-scale and auxiliary-quotient changes rebuild the established positive84 witnesses on the same outer history. Finally the positive forward map gamma=rho+sigma gives the unchanged independent-gamma83 zero.

This invokes the positive converse on newly verified native data. It does not infer the conditions from presumed83 soundness, or assert that arbitrary upper-bit changes preserve every old Pell witness numerically. The Pell witnesses are freshly constructed; the accepted computation and ordinary input remain the same.

## 5. What the factorial counterfamily cannot transfer

The [first-index-deletion counterfamily](complete80_first_index_deletion_collapse.md) uses p=R=55u and n=40u for positive u. Its rank discrepancy is

```
2n-R-1=25u-1>0.
```

The retained normalized gamma83 kernel instead forces exactly2n=R+1. Thus that specific factorial/CRT family cannot become a gamma83 zero by choosing a different independent gamma. Its freely selected dyadic Y also ceases to be free once this index relation and the strong rank conditions are restored. This excludes that direct transfer, not every conceivable factorial construction. The genuine upper-bit switches above respect the rank theorem by constructing the exact native Y and fresh witnesses after their final R is known.

## 6. Evidence and unresolved language

The [fresh helper](complete83_gamma_native_ternary_escape.py) authenticates nine frozen source/proof files as inert data. The [receipt](complete83_gamma_native_ternary_escape.json) records24 exact packing-difference assignments,24 independent reconstructions of Boolean five-adic subsets,432 ternary three-choice orbits,129 exact half-binomial tails modulo9, three radix-margin checks and five factorial-rank discrepancies. The subset parameter d=1 is included only as an arithmetic lemma test, not as an actual compiler radix. Every finite assignment here is bounded arithmetic corroboration. No real compiler mask layout, gigantic full Pell zero or full accepting history is claimed to have been materialized by the helper.

The genuine-history assertion is the unrestricted construction in Sections1–4, using the authenticated compiler and converse proofs. Its remaining limitation is precise: the factor3² obstruction is avoidable, but no useful bound on the other prime-power factors of m follows. In particular neither 2^[2^e(H-1)]=1 nor 2^[2^e(H-3)]=1 is proved to occur. Even at accepted input4, the new histories do not yet yield a downward false input1 or3 without controlling those remaining factors. Independent-gamma83 remains unresolved as an ordinary-input representation.

Run from any directory with `--root` pointing to the installed native-stream-queue directory and `--expect` to this receipt. The helper uses explicit exceptions under normal and optimized Python, rejects duplicate/nonfinite JSON and compares receipt types recursively. No predecessor Python is imported or executed, no historical suite runs, and no frozen source changes.

Fresh exact receipt replays from `/` passed with both normal Python and `python3 -O`.
