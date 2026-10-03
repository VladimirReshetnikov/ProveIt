# Asymmetric scales in the three complete74 comparison sources

The three complete74 comparison sources admit the one-row change **X=wq³ to X=wq**, retaining Y=sq³. Their full positive integer zero sets are in bijection by `w_new=q²*w_old`, with every other supplied coordinate, the ordinary input and the fixed compiler slice unchanged. Certificate costs remain **74=40M+34A**; the complete SOS degrees fall from52/84/84 to **44/68/68**.

| Selected source | Positive witnesses | Equations | Comparison operations | Complete SOS | Exact SOS degree |
|---|---:|---:|---:|---:|---:|
| `raw30` |30|19|40M+34A=74|59M+71A=130|44|
| `positive22` |22|11|40M+34A=74|51M+55A=106|68|
| `signed20` |20|9|40M+34A=74|49M+51A=100|68|

This completes a missing literal transfer of those three saved sources. It does not lower the established74-operation comparison bound or86-operation universal polynomial bound, nor assert a new global operation/degree frontier. The older [normalized87/coupled88 scale transfer](complete75_asymmetric_scale_tradeoffs.md) and [retained-a,c gap family](complete113_asymmetric_retained109.md) use different interfaces and finalizers. Their general native argument is reused below with the hypotheses verified for these actual sources.

The standalone [source](complete74_asymmetric_scale_transfer.py) and [receipt](complete74_asymmetric_scale_transfer.json) contain all three complete comparison DAGs, all three complete SOS DAGs, unchanged witness lists and comparisons, current ledgers, graph maps and exact degree certificates. They read authenticated JSON and proof bytes; no historical Python module or suite executes.

## 1. Literal source boundary and full polynomial identity

The direct parent is the frozen three-form [complete74 packet](complete74_factored_first_norm.md). In every form, the actual paid rows are

```
Lbig = q*q
n2 = Lbig*q
wn2 = w*n2
sn2 = s*n2.
```

Change only the `wn2` row to `wn2=w*q`. The cube stays paid and live through `sn2`. Supplied w has exactly this one source consumer and no direct comparison consumer. Every other instruction, comparison pair, residual subtraction, square and final sum is unchanged. In particular no index row or supplied r is removed.

Let q(v) be supplied q in `raw30`, or the computed `(B−1)Jrep+1` in the two projected forms. It is independent of w. The forward map is the polynomial assignment

\[
 w_{\rm new}=q(v)^2w_{\rm old}.
\]

The literal X rows agree because `(q²w)q=w(q²q)`. A small coefficient expansion checks this identity, and the sole-consumer audit then permits a common-X cut. Every subsequent computed register, every comparison residual and the complete SOS agree. Thus

\[
 F_{\rm new}(v,w=q(v)^2u)=F_{\rm old}(v,w=u)
\]

over any commutative ring, including q=0. This is an identity after the specified coordinate map, not an assertion that the two polynomials are equal at unchanged w. The changed supplied leaf w is not counted among the unchanged computed registers.

For q≠0, the rational inverse `w_old=w_new/q²` gives the converse entire-polynomial identity. It need not be integral on an off-zero positive tuple. Sections2–4 prove its positive integrality at every positive child zero on a valid fixed compiler slice.

The original factored coefficient remains `L(L+k)`, with `L=XY²k`. Its k operand is still the independent supplied `k` in `raw30`; only the projected forms use computed `R10b=eta+zeta`. The raw equation k=eta+zeta is used below only after all comparisons vanish. The source never assumes it in an off-zero identity.

## 2. Common native equations at a positive child zero

Use the same admissible fixed compiler numerals as the selected parent: `Bm1=B−1`, B=2^d≥16, the original ordinary-input constants and shifted masks. Write MF0 for the native mask, so the source's `MF` port is MF0+B−1. In particular

\[
 0<MC,MF0<B-1,\qquad MF0\ge4.
\]

All supplied witnesses and the ordinary input x are strictly positive integers. Write R for the supplied coordinate `r`, X=wq, Y=sq³, E=XY, H=4a+3, Delta=a²+H and A=a+2. The source register named `A` contains Delta; the mathematical A here is the Pell base.

At a zero, all three forms supply the following positive native quantities and equations:

\[
\begin{gathered}
 a=Y(X+1),\quad k=\eta+\zeta,\quad c=kY+\eta,\quad k=R+1+hE,\\
 D=X+ac+\gamma H,\quad D^2=1+\Delta c^2,\\
 \tau^2-XY^2(XY^2+1)k^2=1,\\
 (ic^2)^2=\Delta(f^2-1),\\
 (ic^2)^2\bigl((jc-R)^2-y^2\bigr)=1-y^2,\quad jc-R=of-c.
\end{gathered}
\]

In `raw30`, a,c,D,k and gamma are supplied positive witnesses, and their defining equalities are retained. In `positive22`, a,c,D,k are positive computed definitions and gamma is supplied `ga`. In `signed20`, they are again positive computed definitions, with gamma=`rho+sigma`. Hence D>0 unconditionally on its supplied positive grid. The auxiliary y is the supplied `y_aux`.

The first displayed norm is exactly the retained comparison `L(L+k)=tau²−1`, not a weakened unit equation. If comparison with the retained-a,c gap proof is desired, then `tau²−L²=Lk+1>0` and positivity give g=tau−L>0, without invoking a parent theorem. The native argument can equivalently use ordinary tau directly.

The repunit relation gives q=(B−1)J+1≥16 in every form, either as a retained equality or a definition. Put

\[
 S'=Z+qF-1,\quad T_C=MCJ+1,\quad T_F=MF0J-1,\quad T'=T_C+qT_F.
\]

The actual packing row expands, using the repunit relation, to

\[
 R=(q^2-S')(q^2-1)+T'.
\]

The native mask ranges imply `3q+1≤T'<q²−1`. Supplied F,Z>0 imply S'≥q. Supplied R>0 excludes S'>q², so

\[
 q\le S'\le q^2,\qquad 3q+1\le R<q^4.
\]

The boundary S'=q² is allowed; it is not discarded by a fictitious F+Z<q bound. These conclusions require neither C, W, mu nor an input-gap witness. The asymmetric scales now give

\[
 X\ge q,\quad Y\ge q^3,\quad E\ge q^4>R,\quad 0<R+1\le E.
\]

This is the precise weak packing/native interface used in [retained-a,c Sections3–5](complete113_asymmetric_retained109.md), whose proof dependencies are pinned. It differs from the stronger packing bounds in the older normalized87 family.

## 3. Native rank and index recovery before restoring the old scale

Here is the applicable native argument, with its order of proof explicit. Let V=XY² and P=2V+1. The first norm is `tau²−V(V+1)k²=1`. Its fundamental positive Pell unit is `(P,2)`, giving

\[
 \tau=\chi_P(n),\quad k=2\psi_P(n),\quad n\ge1.
\]

Since P=1 modulo E, the retained first-index equation implies

\[
 2n=R+1+vE.
\]

The bounds `0<R+1≤E` exclude v<0, including the endpoint R+1=E. Thus n≥(R+1)/2≥25. The positive main norm gives `c=psi_A(p), D=chi_A(p)`. Because P>A and c>k, monotonicity gives p>n. The actual ratio equations also give `kY<c<k(Y+1)`. Consequently

\[
 c>A\Delta^2,\quad c>2p,\quad c>kY\ge 2nY\ge Y(R+1)>2R.
\]

The first inequality follows already from p≥26 and standard positive Pell growth. These are established before any exponent or population decoding.

Apply the pinned [ordinary relaxed auxiliary rank proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md) at base A=a+2 to the actual equation `(ic²)²=Delta(f²−1)`. The required rank hypothesis c>A Delta² has just been proved. It gives

\[
 f=\chi_A(m),\quad p\mid m,\quad c\mid m,\quad m\ge c>2p,\quad ic^2=\Delta\psi_A(m).
\]

This is the ordinary strong equation, not the different normalized strong equation. No normalized divisibility is imported. Also U=jc−R>0 from c>2R and j≥1. The auxiliary norm and `U=of−c` allow the odd-index polynomial congruences from the pinned [half-parameter index proof](../../1980/HALF_PARAMETER_PELL_92_PROOF.md). Its strict nearest-multiple step-down, as detailed in retained-a,c Section4, uses m>2p and yields

\[
 R=\pm p\pmod c.
\]

Since `0<R,p<c/2`, this forces p=R. If v≥1 in the first-index relation, then `2n≥R+1+E≥2R+2`, contrary to n<p=R. Thus

\[
 2n=R+1.
\]

Only E>R was needed; the unavailable stronger E>2R is not assumed.

Set r0=(R−1)/2. The lower Pell ratio estimate proved in the pinned retained-a,c argument uses only X≥16, r0≥1 and `6XY²>a`, all true here. With `xi=(X+1)^(2r0)/X^r0`, it gives `c/(k/2)>xi`, hence

\[
 Y>\xi/2-1>X^{r0}/3,\qquad a>X^{r0+1}/3>2^R.
\]

The recurrence of `chi_A(j)−a psi_A(j)` has first values1,2 and is congruent to2^j modulo H=4a+3. The main-root projection therefore gives X=2^R modulo H. Both positive representatives lie below a<H, so

\[
 X=2^R.
\]

Now q divides X=wq, hence q=2^t with t≥4. Since R≥3q+1>3t, q³ divides X. Therefore

\[
 w_{\rm old}=X/q^3=w_{\rm new}/q^2
\]

is a strictly positive integer. Only at this point do we restore the selected symmetric parent and invoke its complete theorem. The argument used the explicitly available native subset; it did not invoke the old whole kernel theorem under an unverified X=wq³ hypothesis.

## 4. All three positive-domain transfers, especially signed20

For `raw30` and `positive22`, all other supplied coordinates are unchanged and positive, and the complete source identity shows that the restored tuple is a zero of its exact selected symmetric parent. The same reasoning applies to `signed20`: its supplied coordinates, including r, are all positive. Only w changes. Its computed C,W,mu and missing input-gap witness do not enter the native integrality proof above.

After w is restored, every computed register of the symmetric signed20 source agrees. That source has its original q³ scale and its full positive supplied interface. Its already proved [signed projection theorem](complete75_signed_projection_elimination101.md) now supplies the omitted-coordinate positivity and the ordinary-input interpretation. We never restore signed W as a positive raw witness before proving it, and never invoke the raw parent theorem with an unverified sign.

For a separate consistency check, the old signed proof's preliminary estimates also survive the asymmetric scale: transport gives 0<C<q, packing gives W=C−Z>−q², and `a=Y(X+1)>q⁴>q²` yields mu>0. Its comparison of input and main indices only needs `W<q≤X` together with sigma>0; a strict q<X is unnecessary. These observations are not needed as an additional premise for the scale inverse.

Conversely, every positive zero of any selected symmetric parent maps to a positive asymmetric zero by `w_new=q²*w_old`; the entire-polynomial identity applies. The two maps are inverse on the **full positive integer zero sets**, not just on canonical compiler witnesses. They preserve the ordinary input and fixed program numerals, introduce no horizon, and remove no ratio, norm, mask, input equation or witness.

The fixed compiler hypotheses remain necessary. The arithmetic evaluator's ability to substitute arbitrary positive constants is not a proof that they encode a valid program. No integer-scale inverse is asserted on arbitrary off-zero tuples or unrestricted signed zero sets.

## 5. Fully paid ledgers and uniform exact degree

A binary addition, subtraction or multiplication costs one operation, including multiplication by a fixed numeral. The single changed row remains one multiplication. All74 comparison gates remain live. For e comparisons, the explicit SOS pays e subtractions, e squares and e−1 additions; counts therefore remain130/106/100.

All supplied witnesses and ordinary input have degree1. Fixed compiler numeral ports have degree0. In raw30, q and k remain independent supplied coordinates. The first coefficient has leading term

```
w^2*s^4*k^2*q^14
```

of degree22. Every other residual has smaller degree. Hence the unique highest square has exact degree44 and leader

```
w^4*s^8*k^4*q^28.
```

In the projected forms, q has leader `(B−1)J`, a has degree6, and c has degree5 with leader

```
c_top = (eta+zeta)*s*(B−1)^3*J^3.
```

The auxiliary residual is

\[
 (ic^2)^2\bigl((jc-r)^2-y^2\bigr)-(1-y^2).
\]

Its unique degree34 term is `i²j²c_top⁶`. The helper authenticates every actual instruction forming this coefficient and its two factors. The whole SOS consequently has degree68 and leader

```
(B−1)^36*J^36*s^12*i^4*j^4*(eta+zeta)^12.
```

The receipt expands its thirteen binomial terms, rather than checking only a specialization where eta=zeta. This polynomial is nonzero uniformly for every admissible B−1>0; the other fixed numerals do not enter it.

To justify that no other residual reaches degree34, the only cancellation needing explicit expansion is the input norm. In the actual source H=4a+3, Delta=a²+H, κ=u+δDelta and mu=W+aκ+rho H, so

\[
 \mu^2-\Delta\kappa^2-1
 =W^2+2aW\kappa+2\rho WH+2a\rho\kappa H
   +\rho^2H^2-H\kappa^2-1.
\]

The exact local coefficient expansion is checked in independent atoms W,a,κ,rho,H. Their actual weights are1,6,13,1,6, so the displayed term degrees are `2,20,8,26,14,32,0`. The input residual therefore has degree32, below the auxiliary residual's34. Every other residual has naive upper degree below34. The honest naive degree upper bound through the unexpanded input source is76; it is recorded separately from exact68.

Six exact dense univariate executions of the entire finalizer, at two fixed B−1 choices per form, attain these degrees and leaders. They supplement the symbolic uniform argument. No finite numerical sample is substituted for the general native proof or the uniform noncancellation proof.

## 6. Guarded interface, provenance and replay

The public entry points are `canonical_parent`, `build`, `rewrite`, `checked`, `polynomial_source`, `degree_certificate`, `evaluate`, `forward_assignment`, `rational_pullback` and `restore_assignment`. They authenticate all13 declared source/proof blobs on every call. Existing canonical paths take precedence: a mismatched canonical proof is rejected even when an unchanged flattened fallback exists. No imported historical builder, private cache or stale bytecode supplies a packet.

`rewrite(parent,mode)` accepts only the exact complete selected symmetric parent. `checked` rejects any changed child source, interface, map, degree or metadata using recursive exact-type equality; Boolean and floating aliases do not pass. Mutable returns are freshly constructed. The old same-coordinate first-norm refactoring metadata is explicitly archived under `historical_parent_transformation`; current scale metadata describes the w map.

`evaluate` accepts exact integers, with strict positivity by default and explicit Boolean `signed=True` for algebra tests. `forward_assignment` has the same integer-domain options and implements the polynomial direction, including q=0 in signed mode. `rational_pullback` accepts exact integers/Fractions, rejects q=0 and returns the precise rational inverse. `restore_assignment` requires positive supplied integers and rejects a nonintegral w/q²; the theorem proves that its divisibility check succeeds at every positive zero on a valid compiler slice. It does not need to solve a Pell equation or test the full zero condition to perform an already integral map.

Python3 standard library only:

```sh
python3 complete74_asymmetric_scale_transfer.py \
  --root /path/to/native-stream-queue \
  --expect complete74_asymmetric_scale_transfer.json
```

`--output PATH` writes the deterministic receipt. Optimized Python execution is rejected at module entry. The saved receipt includes three complete structural identities covering336 computed gates and39 residuals;144 entire forward evaluations including72 signed cases;48 full rational inverse evaluations; three q=0 forward identities; six positive map roundtrips; and six full degree expansions. It also records196 malformed requests rejected,21 defensive-copy checks,130 warm dependency-pin rejections and three canonical relative-proof mismatch rejections with intact fallback files.

These finite evaluations are off-zero algebra and API checks, not materialized accepting Pell towers. The mathematical argument above supplies the zero-set theorem. The source and all parent bytes remain separate frozen artifacts. A fresh replay from `/` matched the saved receipt by exact recursive types and values.
