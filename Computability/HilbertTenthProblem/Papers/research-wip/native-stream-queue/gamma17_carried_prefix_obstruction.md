# The modulo-17 residue and a conditional obstruction for physical dummy grids

The actual canonical compiler fixes `R=-1 mod2^b`, with b>=5, so its evaluation base modulo17 is **X=2^R=9**, not a freely selectable eighth root. The native half-binomial parameter can be computed by the explicit normalized digit rule below. For an actual upper-prefix dummy grid, its exact endpoint interval gives a sufficient, checkable condition under which **every move preserves a modulo17**. If that common residue is -1 or -3, the grid cannot remove17 from Delta.

This is a conditional statement about a genuine grid once its baseline exists. No bad genuine history, successful universal17-avoidance construction, new source count, or false ordinary input is established. The earlier [small-prime digit theorem](complete83_gamma_small_prime_digit_rules.md) already proves all seventeen formula residues with arbitrary prescribed lower digits; that result is not claimed as new. The additions here are the closed normalized transition table, a short analytic block proving its full residue range, and exact interval accounting for the existing physical move formulas.

The [fresh component checker](gamma17_carried_prefix_obstruction.py) and [receipt](gamma17_carried_prefix_obstruction.json) authenticate the relevant sources as data and execute no predecessor code.

## 1. Actual base and normalized state

Use

```
r=(R-1)/2,
C(r)=binom(2r,r) mod17,
G(r)=sum_(j=0)^r binom(2r,r+j)*9^j mod17,
a=5G(r) mod17, Delta=(a+1)(a+3).
```

The origin Start gives Z=1 modulo the inner radix2^b. The literal native mask has MC=-2 in that ring, while q=0 and J=1 there. The actual packing formula consequently gives R=Z+MC=-1 modulo2^b. This is the same source fact used in the prior small-prime theorem; all permitted dummy switches preserve it. Therefore R=7 modulo8, r=3 modulo4 and X=9 modulo17.

Put

```
z=(1+9)^2/9=13 mod17,
T(r)=13^(-r)G(r), U(r)=13^(-r)C(r).
```

The order of13 is4. Since r=3 modulo4 and13^3=4,

```
a=3T(r) mod17,
17 divides Delta  iff  T(r) is11 or16.                 (1)
```

These two bad states correspond respectively to a=-1 and a=-3.

For a general odd prime p and x different from0 and-1, the Lucas split already proved in the cited note gives, on appending a low digit d to k,

```
T(pk+d)=T(k)+beta_d U(k),
U(pk+d)=alpha_d U(k),
```

with z=(1+x)^2/x. If 2d<p, then

```
alpha_d=binom(2d,d)*z^(-d),
beta_d=(sum_(j=d)^(2d)binom(2d,j)x^j-(1+x)^(2d))
       /(1+x)^(2d).
```

If 2d>=p, then `alpha_d=0` and `beta_d=-(1+x)^(-1)`, independent of the particular carry digit. To obtain these formulas, divide the earlier G recurrence by z^(pk+d), use z^p=z, and in the carry case use `(1+x)^p=1+x`. Thus this is an exact normalized form of the inherited recurrence, not a sampled transition rule.

At p=17,x=9 the complete table is:

| Appended digit d | alpha_d | beta_d |
|---|---:|---:|
| 0 |1|0|
| 1 |8|9|
| 2 |11|12|
| 3 |5|10|
| 4 |2|2|
| 5 |5|6|
| 6 |11|11|
| 7 |8|2|
| 8 |1|0|
| any9 through16 |0|5|

Start at (T,U)=(1,1) and read base17 digits from most significant to least significant. At the first digit9 through16, the state becomes `(T+5U,0)`. Every subsequent lower digit preserves T. Equivalently a prefix has zero central binomial coefficient exactly when it contains a digit at least9; prior carry propagation does not invalidate this criterion.

## 2. An analytic all-state block, with the old scope boundary

Let Bword be the eight-digit base17 word `77777771`. Seven7 digits have transformation `(T,U)->(T+4U,15U)`. Appending1 gives

```
Bword: (T,U)->(T+3U,U).                               (2)
```

This follows directly from8 having order8 modulo17, or by multiplying the displayed two-by-two triangular matrices. Therefore the high prefix consisting of k copies of Bword followed by9 has

```
T=6+3k, U=0.                                         (3)
```

For k=0 through16, these are all seventeen normalized states. Append one digit `s=(15-t) mod16`, where t is the integer represented by the prefix. Since17=1 modulo16 and0<=s<=15, the resulting r=17t+s has r=15 modulo16 and hence R=31 modulo32. Its carried state is unchanged, and

```
a=1+9k mod17.                                        (4)
```

The bad choices are k=9 and13. Larger compatible suffix prescriptions can be handled by the already established prefix/CRT extension theorem; no new realization assertion is needed here.

Small direct formula examples are R=63 with a=14 and R=639 with a=16, both R=31 modulo32. Additional formula indices R=1,014,751 and R=916,447 give respectively a=16 and14; with q=32 they satisfy q^2<R<q^4 and popcount(R)=17=3log2(q)+2. These are only scalar diagnostics. They do not satisfy a certified program recipe, masks, convolution, temporal alignment or input bridge. In the B=q=32 interpretation N=1 already prevents a positive ordinary input. None is described as a native accepting history or a complete polynomial zero.

## 3. Exact interval of the existing physical upper-prefix moves

Fix a genuine baseline history and one of the existing nonwrapping upper-prefix constructions. Write r0_inner=2^b for the inner radix, B=2^d, q=B^N, h for its temporal stride and e_star for the ignored digit. These symbols are fixed during the moves. Let

```
Dfield=DC+B*DR+B^h,
Gamma=r0_inner^e_star*(q^2-1)*(1+q*Dfield),
Lswap=S*N/F0, 0<S<F0,
Gswitch=Gamma*(B^Lswap-1)>0.
```

The old five-power filter has S=4,F0=5. The [general odd-prime filter](complete84_odd_prime_compiler_transfer.md) uses its proved S and F0=ell^lambda. In both constructions the source cells are

```
i_j=spacing*j, 0<=j<=Q-2,
i_max=spacing*(Q-2),
i_max+h<min(Lswap,N-Lswap).
```

The source upper bits are initially1 and their destination upper bits initially0, as in the inherited construction; lower bits are independent. The allowed move transfers one upper dummy bit from i_j to i_j+Lswap. In actual word values its changes are

```
delta C=delta Z=2*r0_inner^e_star*(B^Lswap-1)*B^i_j,
delta F=Dfield*delta C.
```

Substitute these into the literal source packing polynomial

```
R=(q^2-Z-qF)*(q^2-1)+(MC+q*MF_source)*J.
```

The mask term is unchanged. Thus `delta R=-2Gswitch*B^i_j`. Starting from the actual baseline Rbase and rbase=(Rbase-1)/2, moving the first k bits gives exactly

```
r_k=rbase-Gswitch*sum_(j=0)^(k-1) B^(spacing*j),
0<=k<Q.                                               (5)
```

There is no wrap or hidden carry correction in (5): the existing source/destination margin is precisely what permits the literal changes above. The physical validity and positivity of every resulting history remain the inherited dummy-move theorem's hypotheses. They are not inferred from arbitrary values of the displayed symbols.

Because Gswitch is positive, all half-indices lie in the exact endpoint interval

```
r_min=rbase-Dwidth, r_max=rbase,
Dwidth=Gswitch*(B^(spacing*(Q-1))-1)/(B^spacing-1).       (6)
```

The quotient in (6) denotes its finite geometric sum, so Dwidth is an integer. Both endpoints occur, at k=Q-1 and0. The interval includes points not produced by a prefix; this does not weaken the sufficient criterion below. The source formula also preserves r modulo4: Gswitch contains2^(b*e_star), with b>=5 and e_star>1.

For an explicit width estimate, put P=r0_inner^e_star. Then

```
Gamma<P*(Dfield+1)*q^3,
Dwidth<(Q-1)*P*(Dfield+1)*q^3*B^(Lswap+i_max),
Dwidth/q^4<(Q-1)*P*(Dfield+1)
             *B^(-(N-Lswap-i_max)).                    (7)
```

For a fixed finite request and fixed h, the coefficient in (7) and i_max are fixed before increasing time. Since S<F0,

```
N-Lswap-i_max >= N/F0-i_max.
```

The relative interval width therefore tends to zero as the admissible time is enlarged. This alone does not imply a shared carried prefix: a shrinking relative interval can cross a base17 boundary, and its common prefix might contain no carry. No unconditional conclusion is drawn from the width estimate.

## 4. A checkable obstruction for a genuine grid

Suppose there is L>=0 such that

```
floor(r_min/17^L)=floor(r_max/17^L)=t,
binom(2t,t)=0 mod17.                                  (8)
```

For example, compute the longest common base17 prefix of the two endpoints; (8) holds if that prefix contains a digit9 through16. Every r_k then begins with the same carried prefix t. Section1 proves that all its lower digits leave T unchanged. Since actual moves preserve r=3 modulo4,

```
a(r_k)=3T(t) mod17 for every0<=k<Q.                   (9)
```

This is the promised exact physical-grid obstruction. If T(t) is11 or16, no member of this particular genuine grid avoids17 in Delta. If it is any other value, the whole grid is already safe at17. The condition is sufficient; it does not classify grids whose endpoint prefixes differ or have no carry.

The existing finite-prime filters control a carry digit at a chosen low17-adic place only when their order hypotheses permit it. At X=9, even a newly forced low carry cannot erase a previously carried high state. Formula (8), with the actual interval (6), states that limitation without replacing the genuine baseline by a freely chosen integer.

No theorem here shows that a bad genuine baseline satisfying (8) exists, that every genuine grid satisfies (8), or that some alternative history/dummy construction cannot enforce safety. Those are the remaining history-level obligations. In particular none of the noncompiler examples in Section2 settles them.

## 5. Fresh evidence and limits

The helper authenticates six source/proof dependencies as inert data. It derives every transition from small exact binomial sums and verifies the block identity by coefficient composition. A separate Lucas digit-product algorithm sums the entire upper binomial tail using a three-state comparison with the midpoint; it does not call the normalized recurrence. The two methods agree on257 small indices, with65 additional direct whole-binomial-row checks.

The receipt saves all seventeen analytic prefixes and their one-digit suffixes, the four stated noncompiler examples, and1,232 synthetic carried-cylinder suffix checks. It also extracts the literal `r_lhs` ancestor cone from the actual84 JSON and evaluates twenty packing tuples in four positive arithmetic models. The models independently check every prefix change, both endpoints, the geometric width formula, the inequality (7), and the shared-prefix invariant. They use the two displacement patterns S/F0=4/5 and6/7. Full endpoint values are saved in hexadecimal, avoiding ambiguous approximate magnitudes.

Those four models use diagnostic DC,DR and masks, not compiled programs. Their invariant residues are0,1,0,12, all safe. Thus even the examples with the exact packing/move formulas do not supply a bad genuine grid or a full positive zero. Their purpose is to check literal interval accounting, not to replace the hypotheses of Section4.

No historical builder, predecessor helper, archived code or full compiler suite runs. No repository source is changed. Run the bounded component CLI with `--root ABS_WIP --expect ABS_JSON`; `--output FILE` writes the deterministic receipt. Explicit exception checks and recursive type-exact comparison operate under normal and optimized Python. All dependency hashes are retained in the helper and receipt.

Fresh normal and optimized (`python3 -O`) exact receipt replays from working directory `/` both passed after final generation.
