# Independent review of the bordered-Hua replacement

## Verdict

**The mathematical replacement in `bordered_hua.md` is sound.** It recovers the exact public majorant, including the powers of `2`, `rho`, `theta`, and `|det B|`. The construction does not need the geometric triangular normalization matrix `L`, its leading principal block, or its last diagonal entry. The generic positive-matrix factorization used inside the existing Hua adapter is legitimate shared infrastructure; it does not recreate the deleted triangular-frame construction.

The strengthened direct determinant reduction through `D*NE` is also correct and permits removal of the arbitrary `IsNegativeBasis` interface in this local proof. No counterexample or missing mathematical assumption was found after checking the actual pinned `OneRealPlace.lean` definitions and the relevant existing determinant/Hua APIs.

This verdict is about the mathematical derivation and source contracts. The complete replacement has not been implemented or compiled in Lean. The reported **611 lines are gross affected source regions, not measured net savings**. No complete source module becomes unreachable merely from this proposal.

## 1. Canonical-frame construction: all dimensions and signs agree

Use the notation of the proposal: `J=J*`, `J^2=I`, full frame `F`, selected-frame inclusion `E`, `B=E*ZE` invertible, `D=ZEB^{-1}`, and `P_y=frameLeftInverse y`. The definitions

\[
 \Omega=JP_y^*D,\quad P=\gamma FEB^{-1},\quad
 H=-\Omega^*J\Omega,\quad V=X^*(P-\Omega)
\]

have the required dimensions. The source's existing identities give

\[
 P_yF=I,\qquad F^*J\Omega=D=F^*JP,\qquad E^*D=I.
\]

Let `W=y^{-1}Omega` and `C=y^{-1}FE`. The columns of `W` lie in the negative eigenspace of the involution `J`. Hence

\[
 H=W^*W,\qquad C^*W=-I.
\]

The cross-Gram identity proves that `W` is injective, so `H` is positive definite. No orthonormal basis is hidden in this step.

Because `P-Omega` is orthogonal to the **entire** frame, the existing `gram_definiteCols_mul_eq` applies and gives

\[
 V^*V=(P-\Omega)^*J(P-\Omega).
\]

Orthogonality to only the selected subframe would not suffice for this conclusion. The proposal correctly proves the stronger full-frame identity using `D`.

## 2. Direct volume reduction and the Ostrowski factor

Put `N=P_y gamma F`. The existing volume formula says `nu=|det N|`. Since `D*E=I`, the source's elementary determinant reduction can be applied directly with `p=D`.

For every omitted frame index, the existing norm-one shared-vector data supply `x,x'` with `Nx'=x` and `x_top=0`. The source identity for `Z*x` then implies `x'_top=0` and `D*x=0`. These are the exact hypotheses of `norm_det_eq_norm_det_mul_inclMatrix`, including the leading coefficient norms. Thus

\[
 \nu=|\det(D^*NE)|.
\]

For `K=Omega*JP`, direct multiplication gives

\[
 K=D^*NEB^{-1},\qquad |\det K|=\nu/|\det B|.
\]

The determinant factor is **one power** of `|det B|`, not its square. Expanding the Gram identity gives

\[
 -K-K^*-(H+V^*V)=-P^*JP\ge0.
\]

The last inequality is exactly the source's nonpositive form on the image of the frame. Applying the existing Ostrowski--Taussky inequality in dimension `r=i+1` therefore yields

\[
 \nu\ge |\det B|\,2^{-r}\det(H+V^*V).
\]

Both the sign of `K` and the exponent `r` are correct.

## 3. The rho estimate needs no normalization

The Gram matrix of the concatenated columns `[C,W]` is positive semidefinite. Its mixed block is `C*W=-I`. The existing determinant Cauchy--Schwarz inequality gives

\[
 1\le\det(C^*C)\det H.
\]

Hadamard's inequality, applied to `C*C`, and the existing `frameBox rho` hypothesis give

\[
 (\det H)^{-1}\le\det(C^*C)
 \le\prod_a\|C_a\|^2\le\rho^{2r}.
\]

This is a direct replacement for the old estimate on `|det L|`. It does not require constructing the projection onto the column span of `W`, a square root of `H`, or an orthonormal basis. The exact existing APIs `norm_det_sq_le_of_posSemidef` and `hadamard_det_inequality` have the required forms.

## 4. The two last-column branches are valid

### Lower branch

For `j<=varrho`, one has `i=j`. The source's shared-vector lemma provides a vector whose coefficient at `z` has modulus one. It follows that the last column `P_z` lies in the span of the full frame and has `J`-square `-1`.

The difference `P_z-Omega_z` is orthogonal to the full frame, hence to `P_z`; its `J`-square equals `||v||^2`. Therefore

\[
 h+\|v\|^2=1,\qquad h=H_{zz}>0.
\]

This proves the branch with `j-i=0` exactly. It also reveals that the canonical last-column coordinate satisfies `||v||<1`, which is consistent with the old normalized identity after its scalar is cancelled.

### Top branch

Because `j<=varrho+1` and `i=min(varrho,j)`, the other branch has exactly `j=varrho+1`, `i=varrho`, and `j-i=1`. Now `E=I` and `D=I`. Thus `Omega_z` pairs to one with `z` and to zero with every isotropic frame vector.

The source's existing Bessel-length lemma supplies `u` in the Bessel unipotent group with `||uy||<=theta`. Since `u^{-1}z-z` lies in the isotropic frame span, the pairing with `Omega_z` remains one. Moving both vectors by `y^{-1}` and using Cauchy--Schwarz yields

\[
 1\le\theta\sqrt h,
 \qquad h\ge\theta^{-2}.
\]

The assumptions imply `theta>0`; this should be made explicit in the Lean arithmetic rather than silently dividing by an arbitrary real parameter. The source already has the relevant positive-length and norm facts. Adding `||v||^2>=0` proves the desired combined bound

\[
 h+\|v\|^2\ge\theta^{-2(j-i)}.
\]

Only this top branch needs the length parameter. No normalized last entry of `L` is used.

## 5. The affine variable and integral match the existing API

The public theorem's actual hypothesis has the shift

\[
 X^*\gamma FE=X^*\gamma_0FE+A^*B_{\mathrm{first}\ i\ \mathrm{rows}}.
\]

Right multiplication by `B^{-1}` gives the exact canonical shift

\[
 V_\gamma=V_{\gamma_0}+[A^*,0].
\]

Hence the final column is fixed, and the first `i` columns are `U_b+A*`. There is no change of the source variable and no missing determinant of a coefficient matrix.

For the bordered positive matrix

\[
 H=\begin{pmatrix}H_{11}&b\\b^*&h\end{pmatrix},
\]

put `S=H11-bb*/h`, `a=h+v*v`, `G=I-vv*/a`, and `Uc=vb*/h`. The block determinant-one congruence gives

\[
 \det(H+[U,v]^*[U,v])=a\det(S+(U-U_c)^*G(U-U_c)).
\]

The conjugation in `Uc` is correct. Choosing `R*R=S^{-1}`, Sylvester's identity gives the proposed alternative

\[
 \det(H+[U,v]^*[U,v])=
 \det H\det\left(G^{-1}+(R(U-U_c)^*)^*(R(U-U_c)^*)\right).
\]

With `U=Ub+A*`, the expression inside the ordinary Hua theorem is literally

\[
 Q+(RA+c)^*(RA+c),\qquad Q=G^{-1},\quad c=R(U_b-U_c)^*.
\]

The determinant factors are

\[
 |\det R|^{-2k}=(\det S)^k,
 \qquad (\det Q)^{-k}=(h/a)^k,
\]

so the full coefficient after the source Hua bound is

\[
 (\det H)^{-(k+i)}(\det S)^k(h/a)^k
 = (\det H)^{-i}a^{-k}.
\]

There is no extra real/complex Jacobian, factor of two, or power of `h`. The existing assumption `k>=7` is sufficient; no stronger hypothesis is introduced.

**Practical Lean recommendation:** define the measurable majorant directly in the existing `Q+(RA+c)* (RA+c)` format, with coefficient

\[
 (2^{i+1}/|\det B|)^{k+i}(\det H)^{-(k+i)}.
\]

Then the existing `measurable_det_add_conjTranspose_mul` and `lintegral_norm_det_add_inv_pow_le` apply verbatim. Use the bordered determinant identity only to connect this expression to the geometric lower bound. This avoids adding a parallel measurability proof for the bordered expression.

## 6. Constants and boundary cases

After integrating, the geometric prefactor is

\[
 (2^{i+1}/\delta)^{k+i}(\det H)^{-i}a^{-k}.
\]

Substituting the rho and theta bounds gives

\[
 \frac{2^{(i+1)(k+i)}\rho^{2i(i+1)}\theta^{2k(j-i)}}
      {\delta^{k+i}}
 =\frac{(2\rho^2)^{(i+1)i}
        (2^{i+1}\theta^{2(j-i)})^k}{\delta^{k+i}}.
\]

This is the current public theorem's constant, exactly.

For `i=0`, the integration variable has dimension zero, the leading Schur block is the empty matrix with determinant one, and the integral is simply `a^{-k}`. No inversion of a non-existent scalar block is necessary: only `h>0` is divided by. All formulas remain valid. The source's `k>=7` avoids any analytic small-dimension restriction, and the broader exact integral also handles `k=0` with the usual empty-space convention.

In the Lean implementation, determinants of positive complex matrices should continue to be written using norms, or explicitly coerced from their positive real values. This is a representation issue, not a mathematical obstacle. The current source already uses the same convention.

## 7. Independent exact geometry regressions

The independent script `check_bordered_geometry.py` has no workspace paths or repository dependency. It accepts `--output` and can be run from an extracted archive:

```sh
python3 check_bordered_geometry.py --output bordered_geometry_checks.json
```

It uses SymPy 1.14.0 and passed **248 assertions in 11 source-shaped rational examples**. Unlike the companion integral checker, these examples build actual indefinite unitary matrices `y,gamma` and the source's canonical frame objects.

The tested ambient spaces have hyperbolic ranks `1` and `2`, positive dimensions `1`, `2`, and **`7`**, and all lower levels `i=0,...,varrho`, together with the top branch. The matrices include nontrivial hyperbolic boosts and Bessel unipotent elements. The checks verify:

- `y*Jy=J` and `gamma*Jgamma=J`;
- the actual `frameLeftInverse`, canonical pairing and dual subframe identities;
- membership of `y^{-1}Omega` in the negative eigenspace;
- positive definiteness of `H`, and the cross-Gram matrix `-I`;
- the full-frame-to-positive-coordinate Gram identity;
- the direct determinant reduction and the **one-power** delta normalization;
- the exact Ostrowski hypothesis identity and its resulting volume bound;
- determinant Cauchy--Schwarz and the rho bound without `L`;
- lower-level energy equal to one and the top-level pairing estimate;
- actual Bessel-unipotent translates with unchanged frame products and shift exactly `[A*,0]`, including the fixed last column.

The output is `bordered_geometry_checks.json`. These finite checks address the geometry not covered by arbitrary positive-matrix integral tests. They still do not establish universal truth by enumeration or replace the outstanding Lean integration.

## 8. What the proposal does and does not remove

The canonical construction can replace both `IsTriangularBasis` and `IsNegativeBasis` locally. The old arbitrary-negative-frame reconstruction lemmas are unnecessary when the determinant reduction is applied directly to `D`.

The proposal retains the shared-vector theorem, elementary determinant reduction, subframe determinant identity, actual unipotent translation formula, ordinary Hua integral theorem, and standard determinant inequalities. It does not remove the unrelated arithmetic content of `BorderedDeterminant.lean`, the distinct Bessel Gram--Schmidt arguments elsewhere, or the ordinary Hua infrastructure. The source counts and final presentation should retain these boundaries.

The strongest justified conclusion is a concrete local mathematical shortening with unchanged contracts and constants, supported by exact checks and a detailed implementation route. A net line saving, successful new Lean build, and full theorem replay remain to be measured.
