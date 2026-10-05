# Binary population on the growing resonant PLUS family

Fix an authentic original powers-of-five compiler for the unchanged shared-projection83 source. In the PLUS family put `Q=B^n=2^D`, `q=Q(Q+1)/2`, and retain the exact resonance `Q+1 | R+1`. Write its positive selectors in the residue form derived below, with quotient h. If `h -> infinity` and `log2(h)=o(D)`, then every sufficiently large member satisfies

```
popcount(R)>=3D+1 > 3(D-1)+2.                    (1)
```

Thus these members pass the binary cubed-scale condition whenever they also lie in the inherited source-coupled positive domain. The growth hypotheses are hypotheses of this note: a separate shifted-search result is needed to supply selectors satisfying them while retaining the odd-scale construction. No entire source zero is constructed here. No result for the MINUS shape, prescribed or rejected ordinary input, or universal83 theorem is asserted.

The key restriction is the actual resonance, which fixes the low selector limb as a repeated sparse mask. Treating that limb as unconstrained loses this information. The argument uses literal compiler sparsity, not merely an upper bound on the magnitude of arbitrary positive compiler ports.

## 1. Literal compiler counts and a positive fixed margin

To distinguish the symbols, use a for tile-alphabet size, k>=2 for the number of allowed windows, M for the original layout M0, and N=|E| for the number of native positions. Write the clause radix as 2^w, w>=2, and let t>=0 count appended zero-expression clauses. The complete78 clauses consist of one occupancy clause,9a tile-copy clauses, four anchor clauses and t zero clauses. Therefore

```
pc(mu)=w+9a+3+t,
N=2pc(mu)+12a+3=2w+30a+9+2t.
```

The native count is the retained one-marker complete77/76 count. At least one ignored dummy is required. Selectors end at k-1, tile copies end at k+12a-1, and the N-k-9a-4 dummies are consecutive above them. Hence

```
E0=N+3a-5,
M=E0+3a+1=N+6a-4=2w+36a+5+2t,
M>=k+15a,       M>=45,       N<=M-2.              (2)
```

Every selector coefficient contains14 distinct bits: one occupancy, nine tile-copy and four anchor occurrences. Each of the9a copy and four anchor coefficients contains one bit. Thus `sum_e pc(c_e)=14k+9a+4`. The literal `K=DC+B*DR` has two copies of the clause coefficients, four explicit DC monomials, at most one optional high monomial, and one B*DR monomial. Binary population is subadditive under addition, including carries, so

```
pc(K)<=2(14k+9a+4)+6
     =28k+18a+14
     <=28M-402a+14 <28M.                         (3)
```

For the original modified75 recipe, write `Vinner=2^b`, `B=Vinner^L=2^d`. The actual radix condition implies `b>w(9a+4+t)`, since the highest clause-mask bit has that exponent. Moreover

`3w(9a+4+t)-M >= 18a+15+4t >0`,

so M<3b. The retained layout has `L>213M+4a+4`. Consequently

```
d=bL>213bM>71M^2.                               (4)
```

Put `m=B-1`, and use the literal modified native mask

```
Dmask=m-MC=sum_(e in E,e!=1) Vinner^e+2Vinner^e_*.
```

Its dummy coefficient3 contributes two bits instead of one, so `pc(Dmask)=N` exactly. Its low bits are those of1, giving MC=2 modulo4. Define

```
H=(m+Dmask)/2=m-MC/2.
```

Then H is even, `0<H<m`, and

```
pc(H)=pc(Dmask)=N,       pc(MC)=d-N.              (5)
```

For the first identity, `H=2^(d-1)+(Dmask-1)/2`; the two bit ranges are disjoint. The unchanged K is even, as is also immediate from its least monomial `Vinner^(3a)`.

All these are fixed compiler facts, independent of n and h. In particular they are not additional unpaid computations in a circuit.

## 2. Exact resonance fixes the repeated low limbs

Put `P=(Q-1)/m`. It is the sum of n consecutive powers of B. The source index is exactly

```
J=(q-1)/m,
S=(MC+q*MF)J,
R=(q^2-z-qF)(q^2-1)+S,       F=Kz,               (6)
```

The guarded source rows compute `gap=(q-1)(q-F)+(q-F-z)=q^2-qF-z`, then multiply it by q^2-1 and add S, so(6) is bound to the literal index producer. Here MF is the source coefficient, which is odd and satisfies `0<MF<2m`. Thus `0<S<2q^2`.

Let A=Q+1. Since q=0 modulo A, `G0=(1+qK)(q^2-1)=-1 modulo A`, and `mJ=-1 modulo A`. The condition A|(R+1) becomes

```
mz=-Dmask modulo A.                              (7)
```

Here gcd(m,A)=1, because Q=1 modulo m and m is odd. The unique positive representative below A is

```
z_A=1+H*P=Q-(MC/2)*P,       0<z_A<Q.
```

Indeed `m*z_A=m+H(Q-1)=-Dmask modulo A`. Every positive resonant selector is therefore uniquely

```
z=z_A+(Q+1)h,       h>=0.                         (8)
```

This h is a derived selector quotient, not the source's separately supplied kernel coordinate of the same letter.

Divide the fixed integer KH by m:

```
KH=C*m+V,       0<=V<m,       0<=C<K.
```

Define

```
U=C+Kh,       a0=K-C+Kh,       c0=h+1,
f0=V*P+a0,    z0=H*P+c0.
```

Then the exact limb identities are

```
F=U*Q+f0,       z=h*Q+z0.                         (9)
```

Under the theorem's growth hypotheses, U,a0,c0,h all have logarithmic size o(D). Since V,H<m are fixed, eventually

```
Q>=64,    U,h<=Q/64,    0<f0,z0<Q.                (10)
```

The last bounds use the fixed gap of at least about Q/m between V*P or H*P and Q; a subpower correction is smaller than that gap. No assumption z<=4d or z<Q is used.

## 3. Fresh expansion and the bounded lower carry

Multiplying(6) by16 and using q=Q(Q+1)/2 gives the exact identity

```
16R = Q^8+4Q^7+(6-2F)Q^6+(4-6F)Q^5
      -(6F+4z+3)Q^4-(2F+8z+8)Q^3
      +(8F-4z-4)Q^2+8FQ+16z+16S.                 (11)
```

The constant term includes16z. Substituting(9), separate the terms below Q^4 as

```
Tlow = 16S+(-2f0-8z0-8+8U-4h)Q^3
       +(8f0-4z0-4+8U)Q^2
       +(8f0+16h)Q+16z0.
```

The remaining coefficients at Q^4,...,Q^8 are respectively

```
-6f0-4z0-3-2U-8h,
4-6f0-6U-4h,
6-2f0-6U,
4-2U,
1.                                                (12)
```

Let `epsilon=floor(Tlow/Q^4)`. Equations(10), `0<S<2q^2`, and `16S<8Q^4+16Q^3+8Q^2` give

```
-11<=epsilon<=8.                                 (13)
```

For detail, the lower bound follows from

`Tlow/Q^4 > -10-(12+4h)/Q-4/Q^2 > -11`.

For the upper bound, discard all negative summands to obtain

`Tlow/Q^4 < 8+8U/Q+24/Q+8U/Q^2+16/Q^2+16h/Q^3+16/Q^3 <9`.

The last comparisons hold at Q>=64 and U,h<=Q/64 and improve thereafter. The floor is the ordinary Euclidean carry even when Tlow is negative; its remainder lies in[0,Q^4).

## 4. Four complete high complement digits

Write the three fixed divisions

```
6V+4H=s4*m+v4,
6V=s5*m+v5,
2V=s6*m+v6,       0<=v4,v5,v6<m.
```

In particular `0<=s4<=9`, `0<=s5<=5`, `0<=s6<=1`. Define

```
beta4=6a0+2U+12h+7-epsilon-s4,
beta5=6a0+6U+4h+s4-3-s5,
beta6=2a0+6U+s5-5-s6,
delta7=2U+s6-3.
```

All four are positive eventually, because h tends to infinity; all have logarithmic size o(D). The exact base-Q digits of16R at positions4,5,6,7 are

```
Q-(v4*P+beta4),
Q-(v5*P+beta5),
Q-(v6*P+beta6),
Q-delta7.                                        (14)
```

Each displayed deficit lies strictly between0 and Q eventually. If a residue v_i is zero this follows directly from positivity and subpower size; otherwise its repeated word has a fixed positive fractional gap below Q. Normalization at position4 sends carry `-s4-1` to position5; position5 sends `-s5-1`; position6 sends `-s6-1`; position7 borrows one unit from the original coefficient1 at Q^8. That top coefficient becomes0. These facts follow by substituting `v_i*P+s_i(Q-1)` in(12), and justify all borrow signs without assuming absent carries.

For `0<a<Q=2^D`, `pc(Q-a)=D-pc(a-1)`. The n copies of a fixed v<m in vP occupy disjoint d-bit blocks. Binary subadditivity therefore gives the high-block bound

```
High >= 4D-n[pc(v4)+pc(v5)+pc(v6)]-Ehigh,
Ehigh=pc(beta4-1)+pc(beta5-1)+pc(beta6-1)
      +pc(delta7-1)=o(D).                         (15)
```

Cyclic reduction modulo m=2^d-1 never increases binary population: repeatedly replace an integer B*a+b by a+b, using subadditivity, until it is at most m, and replace terminal m by0. Thus

```
pc(V)<=pc(KH)<=pc(K)*pc(H),
pc(v4)+pc(v5)+pc(v6)<=5pc(V)+pc(H).               (16)
```

Here multiplication's population bound follows by writing one factor as a sum of powers of two. For example `pc(6V)<=2pc(V)` and `pc(4H)=pc(H)`; applying cyclic reduction proves the three residue bounds even when some residues vanish.

## 5. A disjoint dense low block region survives

Modulo Q, q=Q/2, `q^2=0`, and `qK=0` because K is even. Also

```
J=P*(Q/2+1)=P+Q/2 modulo Q.
```

MC is even, MF and P are odd. Equations(6),(8) therefore give the exact congruence

```
R=(MC/2)*P+h+Q/2 modulo Q.                        (17)
```

The positive expression on the right is less than Q eventually: `(MC/2)P` has a fixed gap below Q/2, and h is subpower. Thus it is the actual low Q-digit of R.

Let `t_h=ceil(bitlength(h)/d)`, so h<B^t_h; for sufficiently large n, t_h+1<n. Adding h to `(MC/2)P` may affect its first t_h blocks and send one carry to the next block. That next block is initially MC/2<B/2, so adding one cannot carry farther in base B. Every block above it remains MC/2. The separate Q/2 term sets the previously zero highest bit. Consequently

```
Low >= (n-t_h-1)pc(MC)+1.                         (18)
```

This loses only o(D) bits because t_h=o(n) and the compiler is fixed. These low D bits of R shift to positions4,...,D+3 in16R; they are disjoint from the high blocks beginning at4D. We may therefore add(15) and(18).

## 6. Positive margin and the binary conclusion

Set the fixed integer

```
mu_margin=2d-2N-5pc(V).
```

Equations(2)-(5),(16) show

```
mu_margin > 142M^2-2N-140MN
          >=2M^2-2M>0.                            (19)
```

We used only N<=M in the second line; the actual stronger N<=M-2 is available. Combining(5),(15),(16),(18) gives the explicit finite bound

```
pc(R) >= 3D+n*mu_margin
         -Ehigh-(t_h+1)pc(MC)+1.                 (20)
```

The error after n*mu_margin is o(D)=o(n), since d is fixed. Hence eventually `n*mu_margin>=Ehigh+(t_h+1)pc(MC)`, proving(1). This is an all-size asymptotic argument, not an extrapolation from the finite checks.

For members also satisfying the original z residue class and the positive source-coupled interval, R=3 modulo4 and the accepted input-invariant binary criterion is exactly `pc(R)>=3v2(q)+2=3D-1`. Equation(1) supplies it. The theorem does not itself produce the growing h representatives, reprove their odd-scale divisibility, or evaluate their full Pell completion.

## 7. Correction, dependencies and fresh evidence

**Correction1 (pre-proof scope omission).** An earlier exploratory assessment treated the low Q-limb as uncontrolled after enlarging z, and on that basis could not transfer the old complement proof. That assessment omitted the already imposed resonance A|(R+1). The exact constraint(7) and representative(8) show why it cannot describe arbitrary low limbs on the actual forced class. Its warning against simply reusing z<=4d remains valid; Sections2-6 provide the new argument. No counterexample to the inherited small-selector theorem was obtained or is asserted.

The fresh helper pins the following inert dependencies. Original compiler claims are read in complete78 Sections1-3, complete77 Section1, complete76 Section1, and modified75 Section1. The sparse and uniform notes supply the earlier census/density context; the relevant sharpened population margin is explicitly rederived above.

| File under Computability/HilbertTenthProblem/Papers/ | SHA256 |
|---|---|
| 1980/FIXED_RAW_UNIVERSAL_78_PROOF.md | b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39 |
| 1980/FIXED_RAW_UNIVERSAL_77_PROOF.md | 292acdfe5ff598201c3dd9cd7defff07b45d743637c1f3836a21065888053a41 |
| 1980/FIXED_RAW_UNIVERSAL_76_PROOF.md | 75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87 |
| research-wip/native-stream-queue/complete75_half_binomial_compiler.md | 68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117 |
| research-wip/native-stream-queue/complete83_shared_projection_scout.json | dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c |
| research-wip/native-stream-queue/complete83_outer_family_sparse_two_primary.md | bda0275af08ceaf1637b6bfa3ba8a8347205f5a674783cec7105ca263bf3fb97 |
| research-wip/native-stream-queue/complete83_outer_family_uniform_two_primary.md | 3ad273d152dbb7a6acc2d312c9963e373adc0e194f6f9c8e685b2cebcb548e12 |
| research-wip/native-stream-queue/complete83_source_coupled_input_lifting.md | 822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f |
| research-wip/native-stream-queue/complete83_fixed_prime_quotient_carries.md | 53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46 |
| research-wip/native-stream-queue/complete83_subpower_selector_bound.md | 3c52050218676fa59fdd83f60699e0d884b1e885e16cc3864146d6dd66010eb4 |

The helper guards13 literal outer-index rows of the actual83 JSON without evaluating the saved source. Its own exact rational sparse algebra proves both(11) and the limb expansion(12) with the full lower tail. It checks20,456 cyclic reductions,96 relaxed clause/layout census assignments, and144 explicitly synthetic resonant indices. The latter verify all four exact complement digits, the terminal borrow, the bounded tail carry, every asserted unchanged low block and the complete finite lower bound(20). They include vanishing coefficient residues. Their constants are synthetic and do not instantiate authentic universal machines; their role is corroboration of identities and carry bounds, not evidence of actual source zeros. No X, Y, half-binomial value or Pell witness is constructed.

Only this newly authored helper is run before freeze. No supplied, archived, committed, frozen, or copied predecessor helper/compiler is executed or imported. The existing source operation count, degree and complete compiler/Pell semantics are inherited; they are not newly certified or improved. Root co-developed the resonance and compiler-margin argument; the complete new formulas and proof remain subject to a separately pinned independent review.

Fresh writer and exact normal/-O receipt replays passed before freeze; the final two replays also ran from `/`. Final helper SHA256: `bd93b5773847eb1a48e32c63d37ef45d8be4a3c4ad78ed5fbe15c6b1e2fea3e0`. Final receipt SHA256: `04bdee149b217bc12dd2b1e0e924412cc9dc61e4658b4c73244d83f260dd437d`.
