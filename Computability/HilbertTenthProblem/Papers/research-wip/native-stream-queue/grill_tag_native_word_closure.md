# A fixed-arity native representation of padded-input Grill halting

For every fixed nonempty finite Grill program, this compiler gives one polynomial with a fixed number of strictly positive witnesses. Its only free input is the ordinary positive integer x. The existence of its positive witnesses says exactly that **some high-zero-padded binary representation of x, of width P0>3x, halts**. The computation duration is existentially packed; it is no longer an external horizon or a varying number of scalar coordinates.

For the small program `(0,1,1)`, the complete literal source costs **219=98M+121A**, with **31 positive witnesses**, 11 comparisons before its integer-product finalizer, and formal degree **at most1187**. A complete raw sum of squares alternative costs243=104M+139A, with37 positive witnesses,20 comparisons and degree at most484. This is not an instantiated universal program and does not improve the separate87-operation universal bound. The informal Genera-to-Grill compiler and the required ordinary-input universal recognizer remain unverified.

The construction adapts the actual [slope-class affine-pair history](pcp_affine_slope_class_history.md), including its complete prescribed-AND kernel, and its [native-unit projection](pcp_uniform_affine_pair_units.md). It uses the word-closure equivalence already proved in [the finite Grill closure](grill_tag_word_closure.md), while replacing that entire finite source by a uniform native history. The [source](grill_tag_native_word_closure.py) pins its local dependencies before loading their source bytes, applies an exact guarded adaptation of the retained builder, and emits every scalar gate and finalizer. The [receipt](grill_tag_native_word_closure.json) contains both full `(0,1,1)` polynomials and additional program ledgers.

## 1. Reverse the two words, keeping the ordinary input numeric

Fix a program `(n_0,...,n_(m−1))`, m>=1. At original phase p a one head appends `g_p=0(10)^n_p`; a zero head appends nothing. Put

```
H_p=4^n_p,          C_p=2(H_p−1)/3.
```

Each g_p is a palindrome. In particular `C_p` is both its little-endian value and its usual most-significant-bit-first value. For each phase p retain two distinct tile IDs, even if some of their numerical affine maps coincide:

```
(p,0): (U,V) -> (2U,   V),
(p,1): (U,V) -> (2U+1, 2H_p V+C_p).                 (1)
```

These are positive-slope, nonnegative-offset maps, exactly the domain of the existing affine-pair theorem. The empty appendant for a zero head uses slope1 and offset0; no unsupported empty-word call to the parent's `maps_from_tiles` helper is used.

Both sentinel accumulators start at1. Apply the tile sequence in **reverse original head order**, and enforce that its phase decreases by one modulo m at each step, ending with original phase0. If the original head word is h and its concatenated selected appendants are G(h), the final sentinels are

```
Ufinal=code(reverse(h)),
Vfinal=code(reverse(G(h))),
code(v)=2^length(v)+value_MSB(v).                    (2)
```

The empty G is allowed and has sentinel1. Now supply positive Z0 and Vfinal and compute

```
P0=3x+Z0,
Ufinal=P0*Vfinal+x.                                 (3)
```

This costs four operations: multiplication by3, addition of Z0, multiplication by Vfinal and addition of x. Ufinal is computed, not a free witness or an uncharged boundary equality. It is strictly positive before using any kernel theorem.

A separately paid lane below forces P0 dyadic. Since `0<x<P0/3<P0`, equation(3) is precisely concatenation of the high word `reverse(G(h))` and the low, fixed-width binary word `reverse(w)`, where w has little-endian content x and width P0. Uniqueness of binary sentinel coding then gives

```
reverse(h)=reverse(G(h))*reverse(w),
h=w*G(h).                                          (4)
```

This argument forces both the word length and content identities. A quotient equation with arbitrary positive P0 would not suffice.

## 2. Literal paid history and phase ports

There are s=2m tile selectors. Let g be the number of distinct program exponents; these give the g exceptional lower slopes relative to baseline1. The upper slope is always2 and has no exceptional products. Supply the usual positive selector hats `Shat_i`, selected-lower-history hats `ZVhat_e`, histories `H_U,H_V`, global slack beta, height slack rho and the 22 raw prescribed-AND auxiliaries. In addition to the free x, supply the three positive coordinates `Z0,Vfinal,phase_initial`.

Write `S_i=Shat_i−1` and `Z_e=ZVhat_e−1` only as proof notation; their actual weighted sums and packed forms are paid by the source. Use the existing fixed dyadic compiler multiplier

```
kappa = least power of two >= max(8,s+4,1+max_i(a_i+c_i,b_i+d_i)).
```

Compute the enlarged height and geometry

```
D=Ufinal+phase_initial+rho,
B=kappa*D,
J=sum_i Shat_i−s,
P=(B−1)J+1.                                        (5)
```

The two height additions are paid. On every positive supplied tuple, P0>=4 and `Ufinal=P0*Vfinal+x` strictly exceeds P0, Vfinal and1. Thus D exceeds every required endpoint and P0 without separately adding them. Its paid phase_initial addend supplies the phase bound as well; no inequality about that coordinate is assumed for free.

For each exponent e let `I_e` contain the one-head tiles with exponent e, and `G_e=sum_(i in I_e)S_i`. The two update histories are

```
NU=2H_U+sum_(one-head i)S_i,
NV=H_V+sum_e(2*4^e−1)Z_e+sum_(one-head i)C_i S_i.    (6)
```

The original three outer comparisons, with both starts fixed at1, are

```
H_U+H_V+sum_e ZVhat_e+beta=P,
B*NU+1=H_U+P*Ufinal,
B*NV+1=H_V+P*Vfinal.                                (7)
```

Phase p has positive code p+1; its successor in the reverse chronology is `(p−1 mod m)+1`. Using exactly the same tile selectors, compute

```
Q=sum_(p,d)(p+1)S_(p,d),
Next=sum_(p,d)((p−1 mod m)+1)S_(p,d).
```

The one new phase comparison is

```
B*Next+phase_initial=Q+P*m.                          (8)
```

Every fixed-coefficient product, hatted constant correction and sum in these expressions is in the emitted schedule. The final phase code m is a fixed literal. It denotes the phase immediately after original phase0 in the reverse traversal, not a free terminal-state choice.

## 3. One complete native AND, including input-width typing

The parent packs g selected-history lanes, s controller lanes, two history-range lanes and two radix lanes. Its old total exponent is `N0=g+s+4`. For concise notation, define the actual paid base-P quantities

```
Rep_l(P)=sum_(j<l)P^j,
S=sum_i S_i P^i,                   Mc=J*Rep_s(P),
Hb=H_V*Rep_g(P),
Mb=(B−1)*sum_e G_e P^e,            Zb=sum_e Z_e P^e,
T=H_U+P*H_V,                      RM=(D−1)J(1+P),
Common=P^g*S+P^(g+s)*T.
```

The new native ports are

```
H=Hb+Common+P^(g+s+2)*B     +P^N0*P0,
M=Mb+P^g*Mc+P^(g+s)*RM
       +P^(g+s+2)*(B−1)    +P^N0*(P0−1),
Z=Zb+Common,
Scale=P^(N0+1).                                     (9)
```

All fixed powers and repunits are generated by the inherited paid multiplication/doubling DAG. Apply the unchanged complete prescribed AND64 to conceptual positive inputs `(Scale,H+1,M+1,Z+1)`. Its literal source inlines those wrappers using

```
q_native=16*Scale,
padded_A=16H+12,
padded_B=16M+10,
F3=16Z+8.                                          (10)
```

All 64 native operations,16 raw native comparisons and22 raw positive native witnesses remain present. There is no caller-supplied AND fact, power predicate, duration, selected-cell multiplication or range oracle.

## 4. Geometry and chronology are recovered before word semantics

On every positive supplied tuple, (3) gives P0>3x and Ufinal>0. The enlarged D in(5) is positive and exceeds P0, phase_initial, Ufinal and Vfinal. Every decoded selector and selected product is nonnegative; J>=0 and P>=1. Thus all conceptual native inputs in(9)–(10) are positive before native classification.

At a zero of the first row of(7), P>1. Hence J>0 and B<=P. It also bounds every history and every selected product strictly below P. The parent selector bound `(B−1)G_e< P` follows from `0<=G_e<=J`. Its physical, controller and two range regions therefore fit in their declared base-P lanes, exactly as in the retained proof.

The old top region begins at exponent `g+s+2=N0−2` and has two lanes. This is necessary because B may equal P at duration1. The new input region starts at N0, after both old top lanes. Since `P0<D<B<=P`, both P0 and P0−1 fit strictly within its single new lane. It is disjoint from every old region, and all of H,M,Z lie below Scale. This bound is derived before interpreting binary AND.

The complete native theorem first makes Scale dyadic, hence P dyadic. Binary AND now separates the base-P regions. It gives all the parent's physical selection, Boolean controller, history-range and radix identities, plus

```
P0 AND(P0−1)=0.                                    (11)
```

Since P0>0, (11) forces P0 to be a power of two. The old radix identity gives B dyadic. Because kappa is fixed dyadic, D is dyadic too. The repunit relation in(5) then gives `P=B^t`, `J=1+B+...+B^(t−1)` for an integer t>=1. This is the variable duration, represented with the same finite witness list for every t.

The inherited controller proof makes the base-B digits of the S_i Boolean and exactly one-hot at every one of those t positions. Its range proof bounds every U/V digit by D−1, and its physical proof identifies Z_e digitwise with selection of V. Every update under a fixed map(1) is less than B, by the definition of kappa. The two transport rows of(7) therefore recover a genuine common affine path from `(1,1)` to `(Ufinal,Vfinal)`.

Now use the phase equation. Each base-B digit of Q and Next is one of 1,...,m. These are all strictly below B since `kappa>=2m+4`. Also `phase_initial<D<B`. Both sides of(8) are canonical base-B expansions, so it asserts, in order:

* the first selected phase code equals phase_initial;
* each subsequent selected source phase equals the preceding selected reverse successor;
* the last selected reverse successor is m, hence the last original phase is0.

Thus for reverse time j the selected phase is `(t−1−j) mod m`. This is the actual chronological phase path, not a balance of aggregate transition counts. It also forces phase_initial into1,...,m; no separate uncharged phase-range assumption is used.

Consequently (2) holds for the reversed head word with the actual Grill phases. Equations(3),(11) give(4). The complete word-closure proof says that the real queue halts at or before the proposed closure length; it stops at the first empty queue and does not treat a post-halt suffix as real firings.

## 5. Full positive completeness

Suppose some padded binary x in the stated cone halts. Its actual finite head word gives a closure h=wG(h). Reverse its tile order, retaining each original phase, and compute the two positive sentinel histories from(1). Let their endpoints be Ufinal and Vfinal; equation(3) follows from the closure.

Take `phase_initial=(t−1 mod m)+1`. Choose a dyadic D strictly larger than `Ufinal+phase_initial`, and set rho to the positive difference. Since Ufinal>P0,Vfinal,1, the same D also exceeds every other endpoint needed by the proof. All affine states are positive and nondecreasing, hence below D. Put B=kappa D, P=B^t and use the corresponding repunit J. Pack the pre-update histories, one-hot tile selectors and selected-lower-history products; add1 to the hats.

Set beta from the first row of(7). The same parent bound supplies beta>0: the sum of histories is at most `2(D−1)J`, and the sum of decoded class-selected products is at most that sum. Therefore

```
beta >= ((kappa−4)D+3)J+1−g >0.
```

The last strict inequality follows from kappa>=s+4, g<=m=s/2 and D>=1. The transport and phase rows telescope digitwise. All old AND regions have their intended meaning. The new region holds because the chosen input width P0 is dyadic and fits below P. The complete positive converse of the unchanged prescribed-AND theorem supplies its remaining native Pell witnesses at this exact Scale.

These are parametric positive-witness arguments. The executable fixtures instantiate the full outer history and truthful AND ports but do **not** materialize the enormous positive Pell witnesses or claim that placeholders make the complete polynomial zero.

Together with soundness, this proves the fixed-arity theorem stated at the top for each fixed finite program. Post-halt closures may provide extra witnesses, as in the finite closure packet; they do not change the existential halting language.

## 6. Native units and complete costs

The optional unit mode applies the retained, literally guarded rewrite to the unchanged native core. It preserves its strong auxiliary equation, both positive ratio slacks, scale and every new outer comparison. Its three norm factors cannot equal−1 modulo4; their product with the native checksum being1 therefore forces all four factors to1. Six native positive definitions are projected using the inherited explicit positive restoration. Their positivity still holds here before typing, because q_native>=16 and F3>=8 follow from the nonnegative wrapper above.

Thus the established positive-zero bijection between the raw and native-unit histories also applies to this composed wrapper. It is not an assertion that their off-zero polynomials are equal. The checker verifies the complete restoration identity including every new outer residual.

Write C for the actual raw certificate source cost before finalization. The raw certificate has20 comparisons and `s+g+29` positive witnesses. Its sum of squares adds20 multiplications and39 additions, for C+59. The unit certificate has cost C+3,11 comparisons and `s+g+23` witnesses. Its integer-product finalizer costs32 more, for C+35, exactly24 fewer total operations. There is only one native checksum family in this product.

| Fixed program | Raw polynomial | Raw witnesses | Unit polynomial | Unit witnesses | Formal degree upper raw/unit |
|---|---:|---:|---:|---:|---:|
| `(0)` |192=84M+108A|32|168=78M+90A|26|304 /737|
| `(1)` |195=86M+109A|32|171=80M+91A|26|304 /737|
| `(0,1,1)` |243=104M+139A|37|219=98M+121A|31|484 /1187|
| `(2,0,1)` |252=111M+141A|38|228=105M+123A|32|520 /1277|

Degree numbers are literal formal upper bounds propagated on each complete DAG. The parent exact-degree metadata is cleared: the enlarged top lane and computed boundary change its degree hypotheses, so its old exact formula is not imported. The counts include nontrivial fixed-numeral multiplications. They do not measure bit complexity, prove circuit optimality or provide a numeric universal Grill instance.

The extra power lane is essential to this interpretation. For `(0,1,1)`, heads `1001` have reversed sentinels U=25,V=4. With x=1,Z0=3 the boundary says P0=6 and `25=6*4+1`, although P0 is not dyadic. This is a counterexample to dropping width typing, not a claim that x=1 lies outside the padded-input halting language.

## 7. Reproducibility and remaining obligation

The guarded adapter authenticates the retained builder and all72 local Python dependencies before import. A custom source-only loader compiles those authenticated bytes directly, bypassing timestamp-based bytecode caches; local preloaded module objects are removed for the isolated import and restored afterward. The source-adaptation text comes directly from the pinned bytes, not Python's line cache. The private fixture test includes an apparently fresh malicious bytecode cache and a preloaded fake module; neither is executed.

`build(program,unit_product=True,root=...)` emits a fresh complete packet; `checked` compares its entire typed descriptor with a fresh canonical emission. `evaluate` uses exact positive integers, or an explicitly requested signed algebra mode. All hashes and the full source are in the receipt. Run the writer or fresh comparison with the maintained WIP directory as `--root`; no output is written unless `--output` is supplied.

The bounded tests cover eight complete source ledgers,96 independent full raw residual/SOS identities,96 full native-unit restoration identities,120 genuine outer closure fixtures and8,468 phase-word candidates, along with malformed descriptor and import-isolation cases. Half of the raw/unit algebra cases are signed. Every raw identity compares all20 residuals, including a separately executed original native source at the independently reconstructed new ports. Outer fixtures deliberately stop at exact semantic AND interfaces; full native existence is supplied by the retained theorem and the completeness proof above.

The uniform packing obligation for this precise padded-input relation is now paid. The remaining universality obligation is specific: exhibit a fixed finite Grill program whose behavior on **every existentially allowed ordinary binary padding** gives the intended universal recognizer, with a proved paid program/input decoding interface. The informal block-encoded Genera construction, including its unresolved source discrepancy, does not establish that claim. No unspecified MRDP invocation fills this gap.
