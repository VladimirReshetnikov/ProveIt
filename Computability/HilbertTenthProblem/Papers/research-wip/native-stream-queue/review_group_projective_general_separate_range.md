# Independent review of the general eight-lane range transfer

**PASS.** The seven complete sources in [the author packet](group_projective_general_separate_range.md) implement the stated range change with every gate and finalizer paid. Their positive-zero projections onto the retained outer coordinates agree with their respective parents. The exact-degree formula is valid under the stated canonical, independent-coordinate hypotheses. No author correction is requested.

This review consists of a [standalone standard-library checker](review_group_projective_general_separate_range.py), its [saved receipt](review_group_projective_general_separate_range.json), and this mathematical scope review. It imports or executes no author or historical Python. It independently reconstructs every complete child instruction array from the actual saved parents and directly authenticates all 54 dependency blobs, the author's literal dependency inventory, and its receipt's source hash. The frozen author hashes are:

- Python: `7da26e02d657f53fc6f27977d92065f15a5769533e27489d73ecd810c327f49c`.
- JSON: `23c18690cb114bfc4a0290b89383a4922ac3d32f55aa4b8dc60d05db5840ae2f`.
- Markdown: `2e0744fd1aad96cc3a1e94ad47237e3c81f2d73705dca72998daf422cf2c3614`.

## 1. Literal source and paid cost

| Complete source | m | Full operations | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|
| Inverse private |64|492 = 191M + 301A|74|5821|
| Exact-language shared |32|432 = 178M + 254A|56|3517|
| Nielsen private |32|371 = 150M + 221A|54|3517|
| Inverse folded |32|376 = 147M + 229A|54|3517|
| Earlier private |8|235 = 98M + 137A|34|1789|
| Earlier shared |8|229 = 97M + 132A|33|1789|
| Ten-letter tail |16|244 = 103M + 141A|36|2365|

All seven retain six comparisons and the literal seventeen-gate finalizer, costing 6M + 11A. The checker verifies complete dependency closure, unique destinations, exact operation types, every gate's output liveness, coordinate domains, unchanged comparisons, and every finalizer instruction. It recounts 2,379 paid live gates.

For `R_k(P)=sum(P^i, i=0..k−1)`, it independently expands the actual paid P8, R8, Pm, Rm, and scale cones. The controller keeps `O=J R_m(P)` and `T=P^(m+8)`. The range mask changes to `J R_8(P)` and its top scale changes from `T P^m` to `T P^8`. The private multiplication `2*T2` is deleted; its sole consumer instead uses T2. Pm remains used in T and Rm remains used in O.

Thus the exact full delta is `−1 + indicator(J R8 was not already paid)` multiplications and zero additions. For m8 the existing controller mask is reused and one multiplication disappears. Each larger saved case pays one new mask multiplication and has unchanged cost. This is a literal-source result, not an arithmetic lower bound.

The checker proves 61 scalar coefficient identities, 14 complete checksum/history identities, and 2,374 common computed-register identities under the three changed scalar interfaces. It checks all 42 comparisons and seven entire output interfaces. The m8 arrays equal the frozen unit-top-mask arrays instruction for instruction; the Nielsen array equals the frozen separate8 nonempty-mask source. The old and new polynomials are not asserted equal on arbitrary identical supplied tuples.

## 2. Positive-domain theorem and its order of proof

The general argument requires a finite nonempty graph, injective edge lanes, `1≤n≤m`, power-of-two m at least eight, and valid state codes. Arbitrary branching uses the paid general weighted flow, not private-path arithmetic. The actual ordinary prefix remains `u=alpha*x+gamma`, `D=u+height_slack`, `B=16D`, with positive supplied x and height slack. A sufficient pretyping margin is `16(alpha+gamma+1)>m`. The seven actual prefixes have alpha24 and gamma13, so B≥608>64. A different graph must supply its own proved or paid margin; the review does not silently pad an arbitrary enumeration.

At a positive full zero, the output `U(1+sum of five residual squares)−1` makes all five outer residuals zero and every native integer factor a unit. The unchanged joint bound first gives P≥12 and bounds every history field and each unshifted selected-source field below P. Positive edge hats give nonnegative edge words. The computed relation `P=(B−1)J+1` then implies J≥1 and B≤P. The radix margin was already proved without binary typing.

Let Hb, Mb, Zb be the physical eight-lane words and C the controller word. Independent expansion of the actual sources gives

    T=P^(m+8), T2=P^(m+16), O=J R_m(P),
    M8=(2D−1)J R_8(P),
    H=Hb+P^8 C+T Hb+B T2,
    M=Mb+P^8 O+T M8+T2,
    Z=Zb+P^8 C+T Hb,
    q=32B T2.

The nonnegative low physical fields are below P8, `C≤J R_m(P)<P^m`, and `(2D−1)J<P`. Therefore `H=H0+B T2`, `M=M0+T2`, `Z=Z0`, with each low part below T2. In particular,

    H−Z≥(B−1)T2+1,
    M−Z≥1,
    2B T2−H−M+Z≥(B−3)T2+2.

These give strict positivity of all four actual native truth fields: `q−16H−16M+16Z−15`, `16(H−Z)+4`, `16(M−Z)+2`, and `16Z+8`. They sum to q−1 and have residues 1,4,2,8 modulo16. Consequently the pinned [tail bootstrap](group_projective_tail_quotient_shift.md#3-native-recovery-including-both-index-signs) applies in its established order, treating both index signs before recovering the large X bound. It gives native signs +1 and dyadic q. The product scale and computed repunit then give dyadic B and `P=B^t` for an integer t≥1.

Put `L=(2D−1)J<P`. In this typed radix, `L R_m(P) mod P^8=L R_8(P)`: all omitted terms are multiples of P8, and L<P excludes digit carries. Since Hb<P8, its AND with either mask is identical. The physical and controller blocks are unchanged, while B AND1 and B AND2 both vanish because B=16D. The same one-hot, general-flow and selected-source theorems therefore recover the same chronological histories.

For the reverse direction, retain the outer coordinates of a parent or child zero, including input, height slack, edge hats, histories, selected-source hats and global slack. The changed scalar prescription has the required positive truth fields and satisfies the other AND mask. The component converse supplies **fresh positive native witnesses**, followed by the tail-coordinate construction. This proves equality of the complete positive-zero projections onto those outer coordinates. It does not assert a native-witness bijection, unconditional signed transport, or equality of the complete polynomials.

## 3. Uniform exact degree

All supplied coordinates, including x, have degree one; fixed compiler data have degree zero. Write a_scale for the exponent in T2 and put

    Q=1+2*a_scale, F=2m+31, R=3Q+F.

The new a_scale is m+16, hence Q−F=2. The nonempty graph gives the nonzero checksum leader `J*=sum edge_hat`. With `D*=alpha*x+height_slack`, `B*=16D*`, the computed leader is `P*=B*J*`. The independent expansion verifies the actual physical ordering

    Hb=H1(1+P)+H0(P²+P³)+H3(P⁴+P⁵)+H2(P⁶+P⁷).

Thus `Hb*=(P*)^7 H2`; in particular the last field is H2. The highest truth-field and scale terms are `F3*=16(P*)^(m+8)Hb*` and `q*=32B*(P*)^a_scale`. Competing physical and controller terms have strictly smaller degrees. Their positive coefficients survive every allowed fixed graph choice.

For the independent native coordinates `s*=2*odd_half`, `k*=eta+zeta`, set `a*=s*(q*)³F3*` and `c*=k*s*q*`. The seven nonzero highest unit forms and degrees are:

| Factor | Highest form | Degree |
|---|---|---:|
| First |`4a*c*(g−k*)`|R+Q+4|
| Main |`8ga(a*)²c*`|2R+Q+5|
| Auxiliary |`i²(c*)⁶`|6Q+14|
| Index |`−h a*`|R+2|
| Linear |`−2h a*`|R+2|
| Strong |`−(a*)²f²`|2R+4|
| Joint |`−P*`|2|

Here g and ga are distinct supplied root slacks. The checker guards every producer in the main-norm cancellation and uses its exact all-value identity with `v=X+gamma`: `v(v+2ac)−(4a+3)c²`. It uses no equation valid only at zeros.

The history-residual leaders are `−B*D*(dS_i*+J*)`, of degree three. An edge of physical label l has coefficient `1+indicator(l=2i+1)−indicator(l=2i+2)` in the latter linear form. Three of the four coefficients are one. For every nonempty graph, at least one history leader is nonzero. Their sum of squares has degree six over the real coefficient field; the flow residual has degree at most two. The product of the seven nonzero unit leaders is nonzero in the polynomial ring. The exact final degree is consequently

    29Q+7F+39 = 73+2(29*a_scale+7m+106),
    old 130m+749; new 72m+1213; decrease 58(m−8).

This is a general noncancellation proof under independent canonical coordinates. It does not assert exactness after arbitrary coordinate identification or specialization, nor for supplied-P or differently optimized native kernels. The checker also gives two independently weighted nonzero modular top coefficients for each entire saved array, totaling fourteen certificates. These corroborate the fixed-source result; they are not the proof of the uniform theorem.

## 4. Concrete evidence and remaining scope

Eight genuine outer fixtures cover all four inverse graphs at x2 and x7. The checker follows actual graph edges, checks the paired shear trajectory to `(0,1,0,1)`, pays the ordinary prefix and height, and evaluates all five outer equations, the joint unit, the complete joined AND and the new product scale. It verifies strict positivity and disjointness of all prescribed truth fields. Their lengths are 124 and 364; chosen heights are 128 and 256. No enormous native Pell zero is numerically materialized. Extension to such a zero uses the component theorem above.

The author's final discussion correctly separates the general compiler transfer from an instantiated universal table. A bounded primary-source check confirms that Mikaelian supplies a constructive finite-presentation embedding procedure, whereas executing it on the particular recursive presentation and obtaining named words remains work not performed here. [Mikaelian, Algorithm 1.1](https://arxiv.org/pdf/2507.04347v8). The finite fibre-product generating recipe does not need the extra asphericity assumptions used for the later recursive-presentation theorem. [Bogopolski–Ventura, Section 1](https://arxiv.org/pdf/0810.0690). This review does not independently reprove those embedding papers or claim a numerical size bound for their output.

The maintained scope is a reproducible, bounded command-line source/proof packet. No hostile-callable-API promise, compiler optimum, numerical universal operation improvement, or external computation horizon is inferred. The four inverse benchmarks retain their proper nonempty relation, and the older m8 benchmark retains its empty relation. The reviewer previously authored the pinned inverse-graph construction, but authored neither this range transformation nor its arithmetic compiler; the complete arithmetic reconstruction here is independent.

Run from any directory:

    python3 /absolute/path/review_group_projective_general_separate_range.py --root /absolute/path/to/native-stream-queue --expect /absolute/path/review_group_projective_general_separate_range.json

The writer passed, and the exact saved-receipt replay from `/` passed against the frozen installed author and dependencies. No historical suite was run and no repository file was edited.
