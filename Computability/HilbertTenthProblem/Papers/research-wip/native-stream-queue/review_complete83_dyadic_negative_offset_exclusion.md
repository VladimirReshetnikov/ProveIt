# Independent review: conditional dyadic negative-offset exclusion

**PASS in the stated scope; no author correction requested.** The frozen theorem excludes `u<t, W=2^u-q` on an actual inherited modified-compiler slice, assuming that `q=2^t`. It consequently restores the positive parent84 inverse when `u<t`. It does not prove q dyadic, exclude `u>=t, W=0`, settle the shared-projection83 language, or lower the established universal arithmetic bound.

The reviewed author files are:

| File | SHA-256 |
|---|---|
| `complete83_dyadic_negative_offset_exclusion.py` | `1bfe8166349fbd16b8557c87cccbbe9827f0eb0813c6227858c22a1fb5a32b35` |
| `complete83_dyadic_negative_offset_exclusion.json` | `6231bded06dbd82575414566cf0ddbd63594f2d21529e36a484cb024b4365144` |
| `complete83_dyadic_negative_offset_exclusion.md` | `9e24c06c8627e50718f0b00236df7dbb83e8ac9701bc3536e097148b3ae922f2` |

I read all226 lines of the author proof, all178 lines of its helper as inert text, and the entire55-line receipt. I did not execute or import those files or any predecessor helper. Only the newly written independent reviewer ran. No inherited source DAG was evaluated, no builder ran, and no native/Pell tuple was materialized.

## 1. Precise source and inherited premise boundary

The source really uses `q=(B-1)J+1`, `X=wq`, `Y=sq^3`, `C=q-F-Z-alpha-2dx`, `W=C-Z`, `u=2dx+b`, and

```
R=(q^2-Z-qF)(q^2-1)+(MC+q*MF_source)J.
```

The fresh reviewer guards21 actual producers for these quantities, including the factored `gap=(q-1)(q-F)+(q-F-Z)=q(q-F)-Z`. It also recounts all83 row operators as46 multiplications and37 additions/subtractions, and the18 supplied witnesses. This is a source-interface audit, not a new full-DAG identity, liveness or degree audit.

The accepted shared-projection theorem and its independent review explicitly supply `R=3 mod4`, `R>3q+1`, `0<u<2q`, `C>=0`, `F+Z<q`, `|W|<q`, exact first/main Pell indices, and `X-W=2^R-2^u` before dyadic typing or H-divisibility. The new proof uses these individual premises rather than invoking the positive parent compiler at a tuple without an integral rho.

Assuming q dyadic now gives `q=B^N`: the actual B is `2^d`, and `2^d-1 | 2^t-1` implies d divides t. The exact offset and the strict interval `-q<W<q` give the three stated branches. On each one `X>2^(R-1)`; in the noncanonical cases the subtracted exponent is t or u, both strictly below R-1. There is no inference that the repunit equation by itself makes q dyadic.

## 2. Half-binomial extraction before masks

I independently checked the order of the ratio estimates. The lower Pell ratio only requires the displayed first/main indices, positive X,Y, and `6XY^2>a`. With `X>=16,r>=24`, it gives `Y>X^r/3` and therefore `a>8r`, justifying the upper-ratio estimate. The source need not have `X=2^R` or the older stronger scale `X>=4096`.

Writing `xi=M+theta`, the bound `X>2^(2r)` gives `0<theta<1/2`. The upper-ratio error is below `16r/(X+1)<1/2`. Since q and X are even, M is even. Consequently

```
M/2<c/k<M/2+3/4.
```

Both M/2 and the supplied integer Y are then the same integer floor of c/k, because `Y<c/k<Y+1`. Thus Y=M/2 has been recovered before any population or mask conclusion.

For a noncanonical branch `X=2^R-2^ell`, with ell>=t, reduction modulo `2^(3t+1)` leaves only j=0,1,2,3 in the binomial polynomial: `R>3t+1`, and every j>=4 term has valuation at least4t>=3t+1. The author's cubic congruence is therefore equivalent to the retained q-cubed divisibility of this recovered Y. It is not claimed sufficient for a full zero.

## 3. The fixed-layout inequality and both denominator exclusions

The fixed layout is essential here. Write V0=2^b and `Dmask=B-1-MC`. The actual76 baseline mask together with the modified75 dummy change gives

```
Dmask=sum_(e in E,e!=1) V0^e+2V0^e_*.
```

Start is at0, End at1, the selected ignored dummy is above1, and all native positions are at most Emax. Thus the digits are at most3, `Dmask>=4`, and `Dmask<V0^(Emax+1)`. The actual76 choice of L strengthens the78 separation and gives `L>=Emax+2`. Hence `Dmask+V0<B-1`. None of this uses supplied Z being typed.

If `u<t`, then `dN>2dx+b` with `0<b<d`, so `N>=2x+1` and `2^u<=qV0/B`. On the proposed negative branch, the strict estimate

```
Dmask*J+2^u < q*(Dmask/(B-1)+V0/B) < q
```

and `C=Z+2^u-q>=0` give `4<=Dmask*J<Z<q`.

The actual packed index satisfies `R=Z-Dmask*J-1 mod q`. Put `k2=v2(r+1)` and `l2=v2(r+3)`. If `k2>=t-1`, then R is -1 modulo q and forces `Z=Dmask*J`, impossible. If `l2>=t-1`, then R is -5 modulo q, so Z would be congruent to `Dmask*J-4`. That representative lies in `[0,Dmask*J)`, whereas adding q leaves the allowed interval entirely. This proves **both** `k2,l2<=t-2`. Omitting the second restriction would be unsound; the author's scalar cancellation example correctly illustrates this point without claiming a compiler zero.

## 4. Unique central valuation and the exact population-to-AND step

For odd r, put `p=pc(r)` and `h2=v2(r-1)>=1`. Factorial valuation and the adjacent coefficient ratios give

```
v2(C0)=p,  v2(C1)=p-k2,
v2(C2)=p+h2-k2,  v2(C3)=p+h2-k2-l2.
```

On the negative-W branch ell=t, the weighted j=1,2,3 valuations exceed p: their differences are at least2, t+h2+2, and t+h2+4, respectively. There is a unique term of least valuation. Therefore the cubic has valuation exactly p, and q^3 dividing Y forces `p>=3t+1`, or `pc(R)>=3t+2`.

I checked the next inference against the **modified**, not baseline, compiler masks. The note's `MF0` means the modified native field mask; the source port is `MF0+B-1`. The actual modified native mask has `v2(MF0)=2`, MC is even, and their populations sum to d. For `q=B^N`, the repeated blocks have no carries. Hence for

```
S'=(Z-1)+qF,
T_C=MCJ+1, T_F=MF0J-1, T'=T_C+qT_F,
```

one has `pc(T')=t+2`, `0<T'<q^2-1`, and the source index is exactly `(q^2-S')(q^2-1)+T'`. The inherited raw bound supplies `1<=S'<q^2` without native typing.

For completeness, the inverse-population lemma follows directly by splitting at Lambda=2^n. When `S+T<Lambda`, the blocks are `Lambda-S-1` and `S+T`; their populations sum to `n-pc(S)+pc(S+T)`. Equality with `n+pc(T)` is precisely absence of carries, equivalently `S AND T=0`. When `S+T>=Lambda` and S<Lambda, the blocks are `Lambda-S` and `S+T-Lambda`. The carry out makes their population at most `n+pc(T)-1-v2(S)`, strictly smaller. S=Lambda is also strict. With Lambda=q^2 this proves the maximum3t+2 and its exact equality condition.

Thus the lower threshold just proved forces equality and `(Z-1) AND T_C=0`. Finally the t-bit complement of MCJ is Dmask*J. Because MCJ is even, the added origin bit has no carry and the complement of `MCJ+1` is `Dmask*J-1`. Therefore Z-1 is a bitwise subset of that value and `Z<=Dmask*J`, contradicting the earlier strict lower bound. The mask is recovered at this point; it was not assumed in establishing the lower bound or the valuations.

## 5. Evidence, read scope and limits

The independent reviewer and receipt share this note's basename. They authenticate all three author pins and all eight dependency pins. Their fresh checks use factorial valuations rather than the author's coefficient recurrence and comprise244 coefficient-valuation sets,1,220 guarded cubics,86,360 instances of the exact inverse-population inequality/equality (including S=Lambda), and1,009 added-origin complement identities. These finite tests corroborate the proof, not its all-integer quantifiers. Fresh normal and optimized exact reviewer replays from `/` pass; no author or predecessor replay was performed by this reviewer.

The precise additional text reads were:

| Inert dependency | Actual read scope |
|---|---|
| `complete83_shared_projection_math.md` | Full233 lines: premises, offset characterization and diagnostic scope |
| `review_complete83_shared_projection_math.md` | Full79 lines: independent premise and inverse audit |
| `complete83_shared_projection_scout.md` | Full source companion; conditional inverse and nonuniversality scope |
| `pell_kernel_half_binomial42.md` | Lines1–250, especially §§4–5 and the start of§6; ratio used with its explicit individual premises |
| `complete75_half_binomial_compiler.md` | Lines1–190, especially §§1–3; fixed native mask changes and inverse-population equality |
| `../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` | Lines1–170, especially §1; actual baseline MC, dummy placement and strengthened L |
| `../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` | Lines1–190, especially §2; separated exponents, anchors and layout |
| `complete83_shared_projection_scout.json` | Parsed inert packet;21 listed outer producer guards, all row-operator and witness counts |

All eight dependency hashes are recorded in the independent JSON. The machine-to-window compiler, historical Pell classification foundations, all archived code and the whole83 polynomial/degree are not newly re-certified here. No claim transfers this conditional result to arbitrary scalar numerals. The surviving W=0 and nondyadic sectors remain explicit, and the same-coordinate parent inverse is invoked only after the canonical branch establishes H-divisibility.
