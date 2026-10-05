# Shared-projection83 is unsound on the inherited compiler recipe

The specific shared-projection83 proposal has positive zeros at **unbounded ordinary inputs on every fixed compiler produced by the original powers-of-five modified75 recipe**. Applying this theorem to the actual empty-language compiler specified below gives infinitely many false positive inputs. Thus this candidate cannot replace complete84 with the same compiler recipe and input interpretation.

This is a parametric existence counterexample on a fully specified genuine compiler, not a materialized giant integer tuple. It refutes the previously unresolved soundness proposal for this source and recipe. The established universal frontier remains **84=47M+37A operations,18 positive witnesses,uniform exact degree187**. No impossibility theorem for83 operations, unrelated fixed slices of this polynomial, the separate independent-gamma83 proposal, or other computational substrates follows.

## 1. Fixed source, fixed compiler, exact quantifiers

The source is the unchanged [shared-projection83 packet](complete83_shared_projection_scout.md), whose JSON is pinned below:83=46M+37A,18 supplied positive witnesses, exact degree187. Let P be any genuine fixed program compiled by the original modified75 powers-of-five recipe. Write its native constants as `B=2^d`, inner width b, `DC,DR,MC,MF0`, and export the six actual source ports as

```
(Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF)
 = (B-1,DC+B*DR,2d,b,MC,MF0+B-1).                (1)
```

In particular the source MF is odd; it is not the native mask MF0. All six ports remain fixed as the outer family parameter increases. Let F83(P;x,w) denote this literal polynomial at these ports. Then

```
for every positive integer H0, there exist x>H0
and w in (Z_{>0})^18 such that F83(P;x,w)=0.      (2)
```

This does not assert a zero at every input, at x=1, or at a prescribed rejected input. The witnesses and constructed input may depend on the family parameter. Because a bounded subset of positive integers is finite, (2) implies infinitely many distinct accepted inputs on each such fixed slice.

## 2. Both shapes give simultaneous full zeros

Put K=DC+B*DR, m=B-1. The fixed residue of K chooses exactly one branch:

| Condition | q, with Q=B^n and D=dn | Odd part A | v2(q) |
|---|---|---|---|
| K!=3 modulo5 | Q(Q+1)/2 | Q+1 | D-1 |
| K=3 modulo5 | Q(2Q-1) | 2Q-1 | D |

Use the [growing-selector theorem](complete83_growing_resonant_selectors.md), with its explicit fixed-prime subsequences and doubled positivity threshold. On all sufficiently large parameters it constructs a positive selector z in the original source residue class, exact resonance A|(R+1), all positive outer slack, and an odd-prime input lift making A³ divide Y. Here

```
Z=C=z, F=Kz, W=0,
J=(q-1)/m,
R=q^4-F*q^3-(z+1)*q²+F*q+z+(MC+q*MF)*J.        (3)
```

The exact canonical selector residue is `z_A=Q-(MC/2)*(Q-1)/m` in PLUS and `z_A=2(m-MC)*(Q-1)/m` in MINUS. Write z=z_A+A*h_sel. The shifted search supplies both

```
h_sel -> infinity,      log(h_sel)/log(Q) -> 0. (4)
```

The source class gives z=1 modulo4. In MINUS, z_A is even and A is odd, so h_sel is positive and odd. The two binary theorems therefore apply:

- [PLUS](complete83_plus_resonant_population.md): eventually pc(R)>=3D+1, exceeding the required3(D-1)+2;
- [MINUS](complete83_resonant_minus_binary.md): eventually pc(R)>=3D+2, exactly the required threshold.

The compiler is fixed. Each proof has an eventual bound for that fixed compiler, so their conjunction with the selector and positivity bounds holds on a tail of the chosen unbounded subsequence. No uniform numerical threshold across all programs is needed.

The [source-coupled input theorem](complete83_source_coupled_input_lifting.md) constructs

```
x=x0+k*T,       x0 in [5n,5n+T-1],       k>=0,
u=2d*x+b,      alpha=q-(K+2)*z-2d*x.             (5)
```

The odd-prime CRT selects k within its explicitly affordable interval. It keeps q,z,F,R fixed and recomputes alpha. Hence the binary condition, which depends only on R, survives at the same input where the odd part passes. In the resulting positive domain the exact binary criterion is equivalent to `2^(3v2(q)) | Y`. Together with A³|Y, it proves q³|Y for `X=2^R-2^u` and `Y=M_r(X)/2`, r=(R-1)/2.

All other requirements of the [outer-family converse](complete83_nondyadic_outer_family.md), Section6, hold: `R=3 mod4`, `0<u<2q<R`, `q(q-1)|X`, and positive integral outer transport. That converse supplies all18 positive witnesses. W=0 is a computed register, not a supplied coordinate required to be positive.

For clarity about the positivity interface, `w=X/q`, `s=Y/q³` and `transport_quotient=1+z*w/(q-1)` are positive integers. The inherited strict first/main Pell ratio supplies positive eta,zeta and the native kernel h. With `a=Y(X+1)`, `H_Pell=4a+3` and `E_j=chi_{a+2}(j)-a*psi_{a+2}(j)`, the changed shared witness is `U=E_u>0` and

```
sigma=((E_R-2^R)-(E_u-2^u))/H_Pell >0.           (6)
```

Odd u>1 supplies positive integral delta. The auxiliary index2cR and its two congruences supply positive integral f,i,y_aux and auxiliary_quotient. The18 names in the actual source are

```
Jrep,F,alpha,transport_quotient,f,h,i,
auxiliary_quotient,s,w,tau_root,eta,zeta,y_aux,
Z,delta,shared_projection,sigma.
```

All seven normalized factors equal+1, so the actual polynomial vanishes. These are existential definitions of the original witnesses, not new uncharged circuit operations. Finally (5) gives x>=5n. Since the chosen n tends to infinity, (2) follows.

## 3. A genuine compiler with empty intended language

Use only Sections1–3 of the existing [rejecting compiler recipe](complete75_weakened86_rejecting_compiler.md). Its Section4 concerns a different weakened86 polynomial and is not an arithmetic premise here.

The normalized machine has tape alphabet{0,1,2}, blank0, initial state start and accepting state halt. Its complete transition table is:

| State | Read | Next | Write | Move |
|---|---:|---|---:|---|
| start | 0 | loop | 0 | stay |
| start | 1 | loop | 2 | stay |
| start | 2 | loop | 2 | stay |
| loop | 0 | loop | 0 | stay |
| loop | 1 | loop | 1 | stay |
| loop | 2 | loop | 2 | stay |
| halt | 0 | halt | 0 | stay |
| halt | 1 | halt | 1 | stay |
| halt | 2 | halt | 2 | stay |

Every initial step enters loop, and every step from loop remains in loop. Therefore halt is unreachable on every input. This invariant proves that the language is empty independently of a finite simulation. The start-on1 transition writes2, stays, and enters a distinct nonaccepting state, exactly the required stationary first-step normalization. The compiler's doubled ordinary-input convention preserves emptiness.

The finite tile alphabet has18 elements: two boundary tiles,12 ordinary symbol/head tiles and four initialization tiles. Take the full allowed radius-one helical window predicate, all permitted3-by-3 windows, and place the actual Start and End windows at selectors0 and1. Apply the original modified75 compiler and its `new_constants` export. This is a finite effective compiler recipe for fixed integers, even though the window alphabet is too large to materialize here. The existing recipe specifies the exact lazy enumeration and marker ordering.

Its retained metadata gives k=12,719,417,040 windows, N=12,719,417,207 native positions and M=12,719,417,311. The actual widths are b=5^17, L=5^18 and d=5^35. The native masks use the modified definitions, including the missing exponent1, extra dummy bit and MF0 correction4. The six ports for shared83 are precisely (1), including the extra B-1 added to MF0. We inherit the established recipe and compiler semantics; no billions-element list, fixed numeral export, archived helper or old compiler is evaluated in this packet.

This program is an authentic fixed slice covered by Section2. Therefore its F83 has zeros at unbounded positive x. Every such x is rejected by the intended program, so these are actual compiler/input false positives. A displayed numerical x or giant Pell tuple is unnecessary for this quantified counterexample. In particular, the old weakened86 example at x=1 is not being transferred to83.

More generally, any original slice with a finite intended language has false positives: choose H0 at least its largest accepted input and apply(2). The theorem alone makes no such conclusion for an arbitrary infinite language, whose accepted inputs could include the constructed sequence.

## 4. Which proposal fails, and which results remain

Every constructed zero has `W=0`, `X=2^R-2^u`, and common offset e=-2^u!=0. Thus the missing same-coordinate inverse is not restored. The empty-language example establishes semantic unsoundness as well; extra witness tuples alone would not have sufficed for that conclusion.

The exact forward map from every parent84 zero to a shared83 zero remains valid. The83 source count, witness count and degree are unchanged. Its proposed use with the inherited universal compiler recipe is refuted. Historical notes recording an unresolved binary condition or unknown valid-program counterexample are retained as dated stages of the investigation and superseded by this theorem.

This conclusion does not establish acceptance at every input, refute every use of the same polynomial with other fixed numerals, or exclude any83-operation universal equation. It does not concern the separate independent-gamma83 source. The minimum-operation universal construction in this repository remains84/187/18, with the established degree and witness tradeoffs unchanged.

## 5. Proof dependencies and verification scope

The proof composes the following exact sources; the companion JSON records their hashes and the literal18-witness interface. It is a fresh read-only provenance receipt, not a numerical zero check.

| Dependency | SHA256 |
|---|---|
| complete83_shared_projection_scout.json | dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c |
| complete83_growing_resonant_selectors.md | c005748a280f385c0278e6bfbf4c9f465e924ef9687ad773031d97d3a5760e15 |
| complete83_plus_resonant_population.md | c09e8a550a66cd89fe8b4281000d84c3bd5db2fe390d07c28e33348c7d93b31a |
| complete83_resonant_minus_binary.md | 5d130699b2060dcd0d5eee1f4ecd312a9a098bf36adb868c29b7e0491f445ed1 |
| complete83_fixed_prime_quotient_carries.md | 53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46 |
| complete83_source_coupled_input_lifting.md | 822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f |
| complete83_nondyadic_outer_family.md | 42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23 |
| complete83_shared_projection_math.md | 1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c |
| complete83_even_radix_boundary.md | eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc |
| complete75_weakened86_rejecting_compiler.md | 186fc8a89c99455361fd0eb0b90d53c1fa90af32191a741c02e950d3bb0d8e78 |
| complete75_half_binomial_compiler.md | 68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117 |

Root read the proof chain and challenged both binary arguments. Two additional reviewers separately checked branch coverage, unchanged input index R, the native/source MF distinction, all18 positivity requirements, and the actual rejecting recipe. The frozen independent review is linked on the research landing surfaces. No supplied, archived, committed or frozen helper/compiler was executed or imported. No scientific test was replayed for this corollary: the new ingredient is composition of quantified proofs with the explicit machine invariant, and the arithmetic controls remain in the reviewed branch packets.
