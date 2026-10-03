# Nonlinear first-index projection of the three complete74 sources

This bounded scout emits an exact polynomial graph projection of each of the three authenticated complete74 comparison systems. It removes the supplied coordinate `r` and its first-index comparison. The complete comparison schedule still costs **74=40M+34A**; deleting one residual square saves three operations in the fully paid SOS. **Positive-zero soundness is unresolved. These candidates do not establish a lower universal operation bound or a new universal witness bound.**

| Parent mode | Retained positive-coordinate interface | Comparisons | Certificate | Full SOS | Exact SOS degree |
|---|---:|---:|---:|---:|---:|
| `raw30` | 29 | 18 | 40M+34A=74 | 58M+69A=127 | 52 |
| `positive22` | 21 | 10 | 40M+34A=74 | 50M+53A=103 | 84 |
| `signed20` | 19 | 8 | 40M+34A=74 | 48M+49A=97 | 84 |

The table records complete emitted polynomials and their proposed positive-coordinate interfaces. It does not assert that their positive zeros recognize the parent's language. Their parent SOS counts are 130, 106 and 100. The retained ordinary input, fixed compiler numeral ports and all other coordinate names are unchanged; there is no external time bound.

## Actual source and the paid rewrite

The pinned [complete74 source](complete74_factored_first_norm.py), [receipt](complete74_factored_first_norm.json) and [proof](complete74_factored_first_norm.md) supply all three complete parent schedules. The new [scout](complete74_nonlinear_index_projection_scout.py) reads authenticated JSON bytes and imports no parent or historical module. Its [receipt](complete74_nonlinear_index_projection_scout.json) saves all three complete child comparison schedules and complete SOS schedules.

In each literal parent, the only source consumers of supplied `r` are

```
r1 = r+1
H17 = jc-r.
```

The only comparison using `r` directly is `r=r_lhs`. The first-index cone is

```
hpm1 = h*UM
R11 = r1+hpm1,
```

with comparison `k=R11`. Here `UM=X*Y` is already computed. The actual `k` port is the supplied witness `k` in `raw30`, and the computed sum `R10b=eta+zeta` in the two projected forms. The scout checks those literal operands; it never substitutes the sum for supplied raw `k` on an off-zero tuple.

Remove `r1` and `R11`, retain `hpm1`, and emit

```
index_partial = actual_k-hpm1
restored_r = index_partial-1.
```

Replace `r` by `restored_r` in **both** remaining consumers: the packing comparison and `H17`. Remove the now-identically-zero first-index comparison and the supplied `r` coordinate. The two deleted additions are replaced by two subtractions, so the certificate cost ties at74. The existing multiplication `h*UM` remains paid. There is no free evaluation of the inverse coordinate inside the child source.

All72 retained old computed gates are equal to their parent values after this graph substitution. Every child gate and every retained supplied coordinate is live in its complete finalizer. No source row is counted as a free equality. For e comparisons the explicit finalizer pays e subtractions, e multiplications and e−1 additions, hence `74+3e−1`.

This is a single specified nonlinear projection in each of three parent forms. It is outside the earlier [constant-shift scout](complete74_index_transport_affine_scout.md), which kept all coordinates and only tested shifts by −1, 0 or1. It is not a census of nonlinear coordinate changes, circuit lower bound, or broad optimization search.

## Exact graph identity and the domain boundary

Let v denote all retained supplied values, let E(v) be the literal `UM` expression and K(v) the actual `k` port. Define

\[
 R(v)=K(v)-hE(v)-1.
\]

For each mode, the complete child and parent SOS polynomials satisfy

\[
 F_{\rm child}(v)=F_{\rm parent}(v,r=R(v))
\]

on every integer or rational tuple, and as a polynomial identity over every commutative ring. The deleted residual is literally

\[
 K(v)-\bigl(R(v)+1+hE(v)\bigr)=0.
\]

All other residuals agree individually after substitution. The checker proves the whole finalizer identity by normalizing the complete arithmetic DAGs; it does not assume that any retained equation holds and uses no cuts that hide the packing or auxiliary consumers.

Consequently, over unrestricted integer coordinates, projection of a parent zero and insertion of R(v) are inverse maps of the full zero sets. A positive parent zero also projects to a positive child zero. Conversely, a positive child zero restores a positive parent zero **if and only if**

\[
 K(v)>hE(v)+1.
\]

Thus there is a proved positive-zero bijection with the child zero subset satisfying this inequality. No proof that every positive child zero satisfies it is supplied here. The parent universal theorem requires strictly positive r, so unrestricted integer graph equivalence is insufficient for transferring that theorem.

The pinned [signed projection proof](complete75_signed_projection_elimination101.md), section2, explicitly uses supplied R>0 before recovering its packing bounds. With native MF equal to the source's `MF` port minus B−1, set

\[
 q=(B-1)J+1,\quad
 T_C=MCJ+1,\quad T_F=MF_{\rm native}J-1,\quad
 T'=T_C+qT_F,\quad S'=Z+qF-1.
\]

The actual valid mask ranges give `0<T'<q²−1`, and the packing equation is

\[
 R=(q^2-S')(q^2-1)+T'.
\]

Its nonzero remainder excludes R=0. It does **not** exclude a negative representative: at `S'=q²+1` this expression is `T'−(q²−1)<0`. In the old proof, positivity of R excludes this branch and yields `S'≤q²`, `3q+1≤R<q⁴` and the bounds needed before invoking the half-binomial kernel. Reusing those bounds in the new child would assume the missing conclusion.

The receipt includes small negative-inverse off-zero assignments and negative representatives of the valid remainder interval solely to expose this logical distinction. These are explicitly **not full zeros**, not authenticated compiler counterexamples, and not an obstruction to a possible stronger inverse proof. No giant Pell witness was materialized and no claim of a spurious accepted input is made.

The next mathematical obligation is precise: prove `actual_k>h*UM+1` from the *entire* positive child zero system on valid fixed compiler slices, before invoking the parent theorem; or construct a genuine full positive child zero with the opposite inequality. This scout resolves neither alternative. It establishes that the straightforward paid rewrite itself does not lower74, even before addressing that obligation.

## Exact degree, including the changed auxiliary cone

Fixed compiler numerals have degree0; ordinary input and every retained supplied witness have degree1. The exact-degree statements hold uniformly for admissible fixed numerals, in particular B−1>0.

In `raw30`, X=wq³ and Y=sq³ have degree4, E=XY has degree8, and the restored r has degree9. Hence the auxiliary residual has degree at most24: `(ic²)²` has degree6 and `H17²` has degree18. Every residual except the first norm has degree less than26. The first norm is unchanged and has leading term `w²*s⁴*k²*q¹⁸`. The unique top square therefore has degree52 and leader

```
w^4*s^8*k^4*q^36.
```

In the two projected forms, a has degree8, c degree5, restored r degree9 and `(ic²)²` degree22. The modified auxiliary residual has degree at most40. All other residuals apart from the input norm have degree less than42, even without using the main-norm cancellation.

For the actual input cone, write H=4a+3, Delta=a²+H and κ=u+δDelta. Its complete residual is

\[
 (W+a\kappa+\rho H)^2-(a^2+H)\kappa^2-1
 =W^2+2aW\kappa+2\rho WH+2a\rho\kappa H
  +\rho^2H^2-H\kappa^2-1.
\]

The helper checks this by an exact sparse coefficient expansion in five independent atoms and checks every actual source definition realizing those atoms. The seven displayed term degrees are respectively `2,26,10,34,18,42,0`. Since κ has unique leading term δa², the unique degree42 term is `−4δ²a⁵`. Also a has leading term `(B−1)^6*w*s*J^6`, so the unique degree84 square is

```
16*(B−1)^60*delta^4*w^10*s^10*J^60.
```

It is nonzero at every admissible B>1. The new auxiliary residual, at most degree40, cannot interfere with this leading square. Naive propagation through the unexpanded input norm still gives upper100; the receipt records that bound separately from the proven exact84.

Six exact dense univariate executions expand the *entire* finalized circuits, at two fixed B−1 values per form, and attain these degrees with the displayed coefficients. Those finite checks supplement the symbolic uniform proof rather than establishing it by sampling.

## Pinned bounded replay and result

Python3's standard library suffices:

```sh
python3 complete74_nonlinear_index_projection_scout.py \
  --root /path/to/native-stream-queue \
  --expect complete74_nonlinear_index_projection_scout.json
```

`--output PATH` writes the deterministic receipt; `--expect` compares exact recursive types and values. All five declared source/proof dependencies are authenticated before use. A fresh saved-receipt replay from `/` passes byte-independent exact typed comparison. The supported scope is this bounded source-pinned CLI. Internal builder functions are not advertised as a general hostile-packet API.

The receipt verifies three complete graph identities,216 common computed-register identities,36 retained residual identities and3 deleted zero residuals. It independently recounts327 live paid gates across the three complete SOS circuits. It also checks96 whole numerical graph identities, including24 rational cases and1,152 retained numerical residual identities, the input coefficient identity, and six full degree expansions.

The established universal74 comparison bound and universal86 polynomial bound remain unchanged. This packet preserves a fully paid ring projection and the precise remaining positive inverse obligation for continuation.
