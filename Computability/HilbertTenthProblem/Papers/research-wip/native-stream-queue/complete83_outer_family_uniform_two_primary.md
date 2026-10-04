# A compiler-independent parameter cutoff for the two-primary outer condition

For every actual compiler in the unchanged original powers-of-five modified75 recipe, every member of the non-dyadic outer family with `n=1 mod4` and **n>=9** satisfies the two-primary part of the cubed-scale condition. The threshold9 is independent of the compiler numerals. The ordinary input continues to be constructed by that family; no prescribed-input statement is added. No odd-primary success, completed source zero, or universal83 conclusion is proved.

This is a refinement of `complete83_outer_family_two_primary.md`, whose all-size digit proof is retained. No source instruction, fixed coefficient, supplied witness, or compiler recipe changes. The new observation is that the actual cell mask is dense, whereas the earlier threshold counted only one set bit in each unchanged mask cell.

## 1. Actual source and layout

Use the original notation

`V=2^b`, `B=V^L=2^d`, `d=bL`, `K=DC+B*DR`.

Here K is the source coefficient, not the number of native positions. The modified75 fixed-mask definition retains complete76's finite set E of native inner-radix exponents, forbids End at exponent1 in the remainder, and permits the additional upper bit of an existing ignored dummy e*. The exact mask is

```
Dmask=(B−1)−MC=sum_{e in E, e!=1} V^e + 2V^e*,
Emax=max E=27M0,   e* in E\{1},   e*+1<Emax.       (1)
```

Thus Dmask has digit3 at e*, digit1 at every other member of E except1, and zero elsewhere. Since b>=5, these digits do not carry. In particular

```
pc(Dmask)=|E|,
pc(MC)=d−pc(Dmask),
0<Dmask<V^(Emax+1).                               (2)
```

The second equality is the exact d-bit complement identity, not a subtraction estimate.

The inherited complete78 geometry has

```
Hfield=51M0+3a0+1,
T1=105M0+4a0+2,
T2=159M0+4a0+3.
```

Complete76 chooses a power-of-five L strictly larger than `g+Emax`, where `g=T2+Emax+1`. Therefore

```
L>213M0+4a0+4>5(Emax+1),                          (3)
```

because the second difference is `78M0+4a0−1>0`. Here `M0>=1` and `a0>=1`. Consequently (2) implies

```
pc(Dmask)<=b(Emax+1)<d/5,
mu:=pc(MC)>4d/5.                                 (4)
```

Only the support bound in (2), rather than the sharper exact value |E|, is needed in what follows. Also L>213 and L is a power of5, so `L>=625`; since `b>=5`,

```
d>=3125.                                        (5)
```

These are fixed-compiler facts; no enlargement depending on n or the ordinary input is made.

## 2. A sharper bound on the complement size

Retain the preceding two-primary note's integers

```
Astar=64(4dK+4d+1),
ell=bitlength(Astar).
```

The actual outer-family proof establishes `K+2<4B^(5/4)`. Since `4d+1<8d`,

```
Astar<256d(K+2)<1024d B^(5/4).                    (6)
```

For every integer d>=65,

```
1024d<2^(d/4).                                   (7)
```

One exact base check is `(1024*65)^4<2^65`. The ratio of the right side to d increases at every integer increment because `2^(1/4)>66/65>=(d+1)/d`; equivalently the needed rational comparison is `2*65^4>66^4`. Thus (7) is an all-size inequality, not an inference from samples. Combining (5)--(7) gives

```
Astar<B^(3/2),    ell<3d/2+1.                    (8)
```

For every n>=5, `Q=B^n>Astar` automatically. Hence the high-digit identities and conservative carry estimates of the preceding proof apply without waiting for its older threshold `n>=3ell+5`.

## 3. Count every bit in the repeated native masks

For the unchanged outer-family member, put `D=dn`, `Q=2^D`, `r=(R−1)/2`. The preceding proof establishes, already for n>=5:

* the exact full-polynomial valuation `v2(M_r(X))=pc(r)`;
* n−3 disjoint low B-digits of R equal to MC;
* three high Q-complement digits, each containing at least D−ell set bits.

For the plus shape the high blocks are read from16R. The low blocks shift left by4 and remain below bitD because `(n−1)d+4<=D`. In both shapes they are disjoint from the high blocks, whose first position is4D. No changed carry or new mask assumption is being introduced.

Counting all mu set bits in each low cell, and using odd R, gives the refined inequality

```
p:=pc(r)>=3D−3ell+(n−3)mu−1.                     (9)
```

For n>=9, (4),(8),(9) imply

```
p > 3D−3(3d/2+1)+6(4d/5)−1
  = 3D+3d/10−4
  > 3D+1.                                       (10)
```

The last strict inequality follows from d>=3125. The two-adic exponent of q is D−1 in the plus shape and D in the minus shape. Hence `p>=3v2(q)+1`. The half-binomial value `Y=M_r(X)/2` is integral, with `v2(Y)=p−1`, so

```
2^(3v2(q)) divides Y.                            (11)
```

This proves the claimed fixed cutoff9 for all permitted family members. It does not decide n=1 or n=5, nor claim that9 is optimal.

## 4. Boundary and evidence scope

The unchanged outer family fixes all actual compiler constants, chooses one of its two q-shapes from K modulo5, constructs z and the ordinary input, and proves the exact outer constraints. The predecessor's two-primary proof supplies its exact low-window and high-borrow statements as quantified theorems. The present result strengthens only the lower population count. The odd-prime divisibility conditions still retain their original coupling to `X=2^R−2^u`; their local classifications or finite checks do not prove that any actual family member passes them.

The fresh companion pins eight predecessor files as inert bytes: the actual83 source JSON; complete76 and78 layout proofs; the modified75 mask proof; the outer-family proof; and the preceding two-primary proof/helper/receipt. It guards thirteen literal outer rows. The proof sources read for the new dependency are complete78 Sections1--2, complete76 Section1, modified75 Section1, and outer-family Section1, in addition to the previously reviewed full two-primary argument.

The new checker verifies the exact base and monotonic-ratio inequalities of Section2 using integers, checks448 additional d values and512 geometry pairs, and constructs four explicitly relaxed synthetic masks. It checks their exact complement populations and32 packed-index cases at n=9 or13, covering both q-shapes and two z sizes. The cases verify actual high complement digits, every repeated low cell, the weighted bound, and the unique central valuation; the largest materialized R has1,625,004 bits. The cases do not enforce the family's five-adic branch choice, its z congruence, or its constructed ordinary input. They are not compiler outputs. No X=2^R−2^u, Y, window table, predecessor execution, source zero, or Pell completion is materialized. No operation or degree improvement is asserted.

The helper's own bytes and every dependency are bound in its receipt. The fresh writer and exact normal and optimized-Python receipt replays all passed from `/` before freeze. Root independently read and challenged the full proof and helper, with no finding; that review is a separate artifact.

Final helper SHA256: `d58fbb7707e53a3d095752722433dd0bea858eae7f5d4c146c0d3716cdabc34b`.
Final receipt SHA256: `8290dff4e8ac731b69e94c66ea548a87a2854157bd9f2344eaa538a9425ac4f0`.
