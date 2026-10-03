# A smaller native quotient shift lowers the group compiler degree

The [complete source](group_projective_tail_quotient_shift.py) changes one operand in the latest [product-scale group compiler](group_projective_product_radix_scale.md). Its saved ten-letter instance remains **244=103M+141A operations**, with36 strictly positive witnesses, one ordinary positive input, and six comparisons. Its exact polynomial degree is **2829**, improving the parent's bound3396 at the same cost. Computation length remains existential and unbounded.

This is a complete positive-zero bijection with that parent, proved by recovering the native exponent before restoring its old quotient. The signed inverse can be negative away from zeros. The source emits exactly one authenticated saved instance; the proof and degree formula below apply to the canonical nonempty fixed-table family. No numerical universal matrix alphabet is instantiated, and244 is not a universal numerical bound.

## 1. One changed operand, all arithmetic retained

Use the inherited native names `q,Y,k,c,a,E` and the four positive truth fields. Write

\[
 Z_0=(q-1)F_3,\quad
 S=A_{pad}+(q+1)(B_{pad}+Z_0),\quad r=(q-1)S.
\]

Here `Z_0` is the already-paid register `packed_z_product`; it is not an individual output history lane. The folded ports are `A_pad=16H+13`, `B_pad=16M+10`, and `F3=16Z+8`. Thus they are positive on the stated supplied domain before Boolean typing. These formulas are the actual factoring of the native packed index, not a new free computation.

Replace precisely

```
shifted_native_quotient = selection__w + packed_top_sum
```

by

```
shifted_native_quotient = selection__w + packed_z_product
```

and retain `X=q*shifted_native_quotient`. The supplied positive quotient therefore has the new meaning

\[
 X=q(w+Z_0)\quad\text{instead of}\quad X=q(w_{old}+S).
\]

The producer/consumer audit checks that `selection__w` is consumed only by this addition, which in turn is consumed only by `X`. Neither `S` nor `Z_0` depends on `w`; all of their producers remain paid and live. Every other instruction, all comparisons, every other supplied coordinate and the full finalizer stay literally unchanged.

For the saved instance, the227-gate certificate costs97M+130A. Its six-comparison unsquared-product finalizer costs17=6M+11A, giving244=103M+141A. The37 free coordinates are ordinary positive `x` and36 positive witnesses. The ten-letter macro is `(1,2,3,4,5,6,7,8,1,2)`, with fixed `alpha=24,beta=12`, controller range reuse and computed `P`. It is an illustrative table, not asserted universal.

The exact all-value graph identity is

\[
 F_{new}(x,w,\mathbf v)
 =F_{old}(x,w+Z_0-S,\mathbf v).
\]

It holds over every commutative ring. The checker expands the affine quotient identity, then uses that proved cut to compare every complete downstream register, all six comparison operands, and the actual full output. There is no same-coordinate polynomial-identity claim.

The parent-to-child map `w=w_old+S-Z_0` is unconditionally positive on the old supplied domain, since `S>Z_0>0`. The reverse map is signed in general. The all-ones child assignment already gives a negative restored old quotient; it is not a zero. The following argument establishes positive restoration at every positive zero, without assuming `X>r` in advance.

## 2. Pretyping bounds replacing the old X bound

The old [joint-bound sign bootstrap](group_projective_joint_bound_unit.md#2-pretyping-bounds-for-either-possible-joint-sign) and [product-scale block margins](group_projective_product_radix_scale.md#2-positive-computed-native-fields-before-any-radix-typing) depend only on the outer fields, which are unchanged. At a positive zero, the unsquared integer finalizer first makes every unit factor a sign and every retained outer residual zero. For either sign of the joint scalar unit, it gives `P>=12`, `J>=1`, `B<=P` and the positive reconstructed fields

\[
 \sum_i F_i=q-1,\quad 0<F_i<q,\quad q\ge16,
 \qquad (F_0,F_1,F_2,F_3)=(1,4,2,8)\pmod {16}.
\]

In particular `F3>=8`. The packed index satisfies

\[
 q^3+q^2+q+1\le r<q^4,\qquad
 r<q^3(F_3+1),\qquad r=1\pmod {16}.
\]

The odd quotient remains `Y=(2*odd_half+1)q>=3q`. The new source therefore gives

\[
 E=XY>3q^2(q-1)F_3>2r+3.
\]

For the last inequality,

\[
 E-2r>q^2\big((q-3)F_3-2q\big)
 \ge q^2(6q-24)>3.
\]

Also `X=q(w+(q-1)F3)>=16` and `a=Y(X+1)=E+Y>2r+3`. These are ordinary integer inequalities before any Pell recovery, radix power, population count or Boolean decoding. **They do not assert `X>r`.** They supply the actual bounds needed below.

The original history/output bound is retained as its protected joint unit. The [output-lane obstruction](group_projective_output_bound_obstruction.md) is therefore not bypassed: no output lane, range condition, selector or positive global slack is erased.

## 3. Native recovery, including both index signs

Let `A=a+2`, `Delta=A²-1`, `T=ic²`, `V=of-c`, and `K=k-hE`. The native factors remain

\[
\begin{aligned}
 N_0&=g^2+4XY^2k(g-k),\
 N_1&=d^2-\Delta c^2,\
 N_3&=T^2(V^2-y^2)+y^2,\
 N_4&=1+T^2-\Delta(f^2-1),\
 N_k&=K-r,\
 N_l&=V-jc+2K.
\end{aligned}
\]

All four norm/strong factors exclude `-1` modulo4 on every integer tuple, as in the [strong-unit proof](group_projective_strong_unit_product.md). Thus they equal1 before the rank argument. Write `Nk=epsilon` and `Nl=lambda`, each a sign. Then `K=r+epsilon` and put `Jnew=2K-lambda`.

The [coupled-linear proof](group_projective_coupled_linear_unit.md#2-bounds-before-any-native-typing) uses the old `X>r` only to obtain preliminary inequalities now supplied by Section2. More explicitly, `0<K<E`, `0<Jnew<=2r+3<E`, and `Pfirst=2XY²+1>A`. The positive inverse first-root map classifies `k=psi_Pfirst(n)` with `n=K mod E`, so `n>=r-1`. The positive main root classifies `c=psi_A(p)`. The retained ratio slacks give `kY<c<k(Y+1)` and hence `p>n`. Consequently

\[
 p\ge r,\quad c>A\Delta^2,\quad c>2p,
 \quad c>Y(r-1)>2(2r+3).
\]

The applicable [relaxed-rank lemma](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md) now gives an auxiliary index `m_aux` with

\[
 f=\chi_A(m_{aux}),\quad c\mid m_{aux},\quad
 m_{aux}\ge c>2p,\quad T=\Delta\psi_A(m_{aux}).
\]

It follows that `f>2c`, so `V=of-c>0` before applying the positive auxiliary Pell classification. The [half-parameter congruences](../../1980/HALF_PARAMETER_PELL_92_PROOF.md) and [signed step-down lemma](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md) give `Jnew=+p or-p mod c`. Since both `p,Jnew` lie strictly between0 and `c/2`, they give `p=Jnew`. As `n<p<E`, the earlier congruence gives `n=K` exactly.

If `lambda=-1`, then `p=2n+1`. But `Q2=chi_A(2)>Pfirst` and `2A>Y+1` imply

\[
 \psi_A(2n)=2A\psi_{Q2}(n)\ge2Ak>k(Y+1),
\]

contradicting the upper ratio for `c=psi_A(2n+1)`. Hence `Nl=1` and

\[
 p=2K-1,\qquad n=K.
\]

Up to this point `epsilon` can still be either sign. Set `r'=r` if `epsilon=1` and `r'=r-2` if `epsilon=-1`. All raw native equations have their original form at this positive odd `r'`, with `p=2r'+1,n=r'+1`. No complete old theorem requiring `X>r'` is invoked.

## 4. Exponent recovery without the old bound

The lower-ratio argument in [native selector Section3](native_controller_binary_selector56.md#3-lower-ratio-first-then-the-direct-binary-exponent) uses `a=Y(X+1)` and `6XY²>a`; those hold here independently of `X>r'`. Writing `xi=(X+1)^(2r')/X^r'`, it gives

\[
 c/k>\xi>X^{r'},\qquad c/k<Y+1,
 \qquad Y\ge X^{r'},\qquad a>X^{r'+1}.
\]

Because `X>=16` and `r'>=1`, we have

\[
 6r'/a<6r'/16^{r'+1}<1/2,
 \qquad 2^{2r'+1}=2\,4^{r'}<X^{r'+1}<a.
\]

Also `0<X<a`. The exact main recurrence and retained root equation give

\[
 X\equiv 2^{2r'+1}\pmod {4a+3}.
\]

Both positive representatives are below the modulus, so **now**, and not earlier,

\[
 X=2^{2r'+1},\qquad q=2^t.
\]

The old upper-ratio estimate `0<c/k-xi<24r'/(X+1)` is now below1/2. Together with the fractional binomial tail below1/4, it gives the unchanged exact integer quotient

\[
 Y=\binom{2r'}{r'}+\sum_{j=1}^{r'}\binom{2r'}{r'+j}X^j.
\]

Since `q<r'` and `q|X`, the exponent shows `2q|X`. The still-odd quotient `Y/q` gives `popcount(r')=t`.

If `epsilon=-1`, the actual positive fields at the original `r` yield `popcount(r)>=popcount(q-1)=t`. Since `r=1 mod16`, the exact identity

\[
 \operatorname{popcount}(r-2)
 =\operatorname{popcount}(r)+v_2(r-1)-2\ge t+2
\]

contradicts `popcount(r')=t`. Therefore `Nk=1`. All native units are1 and the product then forces the joint scalar unit to1. This recovers the full old bound as well as the exact index `r`, with `X=2^(2r+1)`.

Finally `q<r`, `S=r/(q-1)<r`, and `2^(2r+1)>r²` show

\[
 w_{old}=X/q-S>0.
\]

It is an integer by the literal `q|X` definition. The signed graph substitution therefore becomes a positive parent restoration on every child zero. Its inverse is the unconditional positive parent embedding from Section1. Every other coordinate is unchanged, so this is a bijection of the complete positive zero sets. It preserves the ordinary input, fixed program numerals, all outer history fields and the unbounded represented computation. No positive restoration is asserted off the zero set.

## 5. Exact degree, with no on-zero substitution

Let `m` be the inherited padded lane count, `nu=1+chi` for supplied/computed `P`, and let the paid product-scale exponent be

\[
 a_{scale}=2m+8\ \text{with controller range reuse},
 \qquad a_{scale}=m+16\ \text{otherwise}.
\]

The first option requires `m>=8`. Keep `a_scale` distinct from the native parameter `a`. Put

\[
 Q=1+\nu a_{scale},\quad F=1+\nu(m+15),\quad R=3Q+F.
\]

Thus `deg q=Q`, `deg F3=F`, and `Q>F`. The source's range-history term uniquely leads `F3`, with `F3*=16(P*)^(m+8)Hb*` and `deg Hb=7nu+1`. Its nonzero highest form has positive coefficients. The new source has

\[
 X^*=(q^*)^2F_3^*,\quad
 a^*=s^*(q^*)^3F_3^*,\quad c^*=k^*s^*q^*,
 \quad s^*=2\,odd\_half,\quad k^*=eta+zeta.
\]

The seven actual unit factors have these nonzero highest forms:

| Factor | Highest form | Degree |
|---|---|---:|
| first | `4 a* c* (g-k*)` | `R+Q+4` |
| main | `8 ga (a*)² c*` | `2R+Q+5` |
| auxiliary | `i²(c*)⁶` | `6Q+14` |
| index | `-h a*` | `R+2` |
| linear | `-2h a*` | `R+2` |
| strong | `-(a*)²f²` | `2R+4` |
| joint bound | `G*-P*` if supplied; `-P*` if computed | `nu` |

Here `ga` is the supplied main-root slack and `G` the joint bound sum. The main factor uses the actual all-value cancellation

\[
 (X+ac+gamma)^2-(a^2+4a+3)c^2
 =X^2+2Xac+2Xgamma+2acgamma+gamma^2-(4a+3)c^2.
\]

The helper checks every defining gate before using this identity for degree. No unit equation, power assertion or relation valid only on zeros is substituted.

For a nonempty table the largest remaining outer residual degree is3. The leading four history residuals are `-B*D*dS_i*` when `P` is supplied, and `-B*D*(dS_i*+J*)` when it is computed. At least one is nonzero. Their squared sum is therefore a nonzero polynomial over the reals; the flow residual has degree at most2. Multiplying this square sum by the seven displayed nonzero unit leaders gives the full highest form, of degree

\[
 \boxed{29Q+7F+37+\nu
       =73+\nu(29a_{scale}+7m+106).}
\]

The complete saved instance has `m=16,nu=2,a_scale=40`, hence `Q=81,F=63,R=306`. Its individual unit degrees are391,698,500,308,308,616,2, and its full exact degree is2829. For the same table with supplied `P`, the formula gives1451; no second full source is emitted in this packet. The general formula is a proof about the stated parent family, not an independently regenerated census of its historical variants.

For the saved circuit, a separate finite-field leading-form evaluation checks every actual gate, after the guarded main cancellation. With prime1000000007 and the receipt's fixed input weights, every gate's propagated leader is nonzero and the final degree2829 coefficient is935638906 modulo that prime. The upper-degree proof and this nonzero integer homogeneous-component witness prove exact degree; this is not a sampled numerical curve fit or a bounded-zero search.

## 6. Frozen evidence and reproduction

The helper authenticates fifteen source/receipt/proof files, including the actual product-scale trio and the applicable rank, half-parameter and signed-index notes. It imports no historical source. The [receipt](group_projective_tail_quotient_shift.json) stores the entire changed source, every comparison, coordinate domain, full ledger, exact-degree certificate, source pins and its own helper hash.

It proves the whole signed graph identity; supplements it with32 full evaluations including8 rational cases and192 residual comparisons; checks16 unconditional positive parent embeddings,512 pretyping field tuples including nondyadic scales, and144 population/positive-inverse size cases. Those finite checks do not materialize full Pell zeros and do not replace Sections2–4. No historical large partition or source suite is rerun.

```sh
python /path/group_projective_tail_quotient_shift.py --root ROOT \
  --output /path/group_projective_tail_quotient_shift.json
python /path/group_projective_tail_quotient_shift.py --root ROOT \
  --expect /path/group_projective_tail_quotient_shift.json
```

`ROOT` is the native-stream-queue directory with its pinned relative `../../1980` proof files. A bounded canonical builder, checked integer evaluator and signed pullback are included for replay; no general hostile-packet service or numerical universal alphabet is supplied. All predecessor bytes are preserved.
