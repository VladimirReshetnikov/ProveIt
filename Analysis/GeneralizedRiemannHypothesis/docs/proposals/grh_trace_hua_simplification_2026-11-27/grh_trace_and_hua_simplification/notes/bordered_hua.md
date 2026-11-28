# Canonical dual frames and a bordered Hua integral

## Status and scope

This is a proposed replacement for a local analytic argument in the GRH source at
commit `f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f`. The mathematical identities and
inequalities below are proved here. The proposed Lean adapter has not been
implemented or checked by Lean. `check_bordered_hua.py` supplies exact regression
checks, not a substitute for either the proofs or a Lean build.

The proposal targets
`src/New/Spanning/RemainingTerms/OneRealPlace.lean`. It retains the existing public
theorem `RealPlace.exists_majorant_volumeRatio_inv_pow`, including its constants.
Its caller in `SchurOrbit.lean` therefore needs no change. It replaces a
point-dependent triangular orthonormal frame by an explicit unnormalized dual
frame. The resulting determinant has a bordered positive matrix in place of the
identity. Completing one square evaluates precisely the integral needed by the
proof. The complete bordered integral is useful for the mathematical explanation;
the Lean implementation can use the existing, weaker Hua bound without adding
the exact evaluation.

There are 611 gross source lines in the identified replacement/removal regions:
582 in `OneRealPlace.lean` and 29 in `HermitianMatrices.lean`. This is not a claim
that the final source becomes 611 lines shorter. New canonical-frame lemmas,
the determinant identity, and the replacement majorant proof must be counted
against those lines. A net reduction is not measured. The affected region is
56.5% of the 1030-line `OneRealPlace.lean`, and 0.1281% of the entire 476849-line
project. The conceptual simplification is more substantial locally than the
whole-project percentage suggests: two frame structures and all triangular
coordinate bookkeeping disappear.

## 1. The matrix integral

Let `k,i` be nonnegative integers. Give the complex matrix space
`C^{k x i}` its ordinary product Lebesgue measure, with `C=R^2` in each entry.
Let

\[
 H=\begin{pmatrix}H_{11}&b\\b^*&h\end{pmatrix}>0,
 \qquad H\in M_{i+1}(\mathbb C),\qquad v\in\mathbb C^k.
\]

Here `*` denotes conjugate transpose; determinants of positive matrices are
regarded as positive real numbers. Then

\[
 \boxed{\displaystyle
 \int_{\mathbb C^{k\times i}}
 \det\!\left(H+[U,v]^*[U,v]\right)^{-(k+i)}\,dU
 =C_{k,i}\,(\det H)^{-i}\,(h+v^*v)^{-k}}
 \tag{1}
\]

where

\[
 C_{k,i}=\pi^{ki}\prod_{\ell=1}^{i}
              \frac{\Gamma(\ell)}{\Gamma(k+\ell)}
 =\pi^{ki}\prod_{r=0}^{i-1}\frac{r!}{(k+r)!}.
 \tag{2}
\]

### 1.1 Completing the square

Set

\[
 a=h+v^*v,\qquad
 S=H_{11}-bb^*/h,\qquad
 G=I_k-vv^*/a,\qquad
 U_c=vb^*/h.
 \tag{3}
\]

The Schur complement `S` is positive definite. Also `G` is positive definite:
for any vector `x`, Cauchy--Schwarz gives

\[
 x^*Gx\ge (1-\|v\|^2/a)\|x\|^2=(h/a)\|x\|^2.
\]

Its inverse and determinant have especially simple forms:

\[
 G^{-1}=I_k+vv^*/h,\qquad \det G=h/a,\qquad
 \det S=(\det H)/h.
 \tag{4}
\]

Use the determinant-one block change of variables

\[
 C=\begin{pmatrix}I_i&0\\-b^*/h&1\end{pmatrix}.
\]

It satisfies `C*HC=diag(S,h)` and `[U,v]C=[U-U_c,v]`.
Writing `W=U-U_c`, take the last scalar Schur complement of

\[
 C^*\left(H+[U,v]^*[U,v]\right)C
 =\begin{pmatrix}S+W^*W&W^*v\\v^*W&a\end{pmatrix}.
\]

This proves the central identity

\[
 \boxed{\det(H+[U,v]^*[U,v])=a\det(S+W^*GW).}
 \tag{5}
\]

### 1.2 The real Jacobian

Substitute `W=G^{-1/2}YS^{1/2}`. On complex matrices, the real Jacobian of
`Y -> LYR` is

\[
 |\det L|^{2i}|\det R|^{2k}.
\]

For the present substitution this is `(det G)^{-i}(det S)^k`.
Consequently the coefficient outside the ordinary Hua integral is

\[
 a^{-(k+i)}(\det S)^{-(k+i)}
       (\det G)^{-i}(\det S)^k
 =(\det H)^{-i}a^{-k}.
 \tag{6}
\]

The power `k+i` is what cancels every residual power of `h`.

### 1.3 The ordinary Hua constant

Define

\[
 J_{k,i}(p)=\int_{\mathbb C^{k\times i}}
                  \det(I_i+Y^*Y)^{-p}\,dY.
\]

For real `p>k+i-1`, integrate the last column of `Y` first. The determinant
lemma and the complex radial beta integral give

\[
 J_{k,i}(p)=\pi^k\frac{\Gamma(p-k)}{\Gamma(p)}
                    J_{k,i-1}(p-1),\qquad J_{k,0}(p)=1.
 \tag{7}
\]

Indeed, writing `Y=[Y_0,w]` and `M=I_k+Y_0Y_0*`, the determinant is
`det M (1+w*M^{-1}w)`. The substitution `w=M^{1/2}z` has real
Jacobian `det M` and leaves `det M^{1-p}`. The remaining scalar integral is
`pi^k Gamma(p-k)/Gamma(p)`. Tonelli applies because the integrands are
nonnegative; the stated condition makes each integral finite.

Iterating (7) at `p=k+i` yields (2), and (5)--(6) give (1).
For `k>=7`,

\[
 C_{k,i}\le\left(\frac{\pi^k}{k!}\right)^i\le1,
 \tag{8}
\]

since `(k+r)!/r! >= k!` for each `r`. Thus the source only needs the consequence

\[
 \int\det(H+[U,v]^*[U,v])^{-(k+i)}\,dU
 \le (\det H)^{-i}a^{-k}.
 \tag{9}
\]

### 1.4 Edge cases and an asymmetric example

If `i=0`, the integration space has dimension zero and total measure one. The
left-hand side of (1) is simply `(h+v*v)^{-k}`. The determinant factor is
`(det H)^0=1`, and the empty product defining `C_{k,0}` is one. No limiting
argument is needed. The same convention makes `k=0` valid as well, although the
source application always has `k>=7`.

For

\[
 k=i=1,\quad
 H=\begin{pmatrix}3&1+\mathrm i\\1-\mathrm i&2\end{pmatrix},
 \quad v=1+2\mathrm i,
\]

we get `det H=4`, `a=7`, `S=2`, `G=2/7` and `U_c=(3+i)/2`. In particular

\[
 \det(H+[u,v]^*[u,v])=14+2\left|u-\frac{3+\mathrm i}{2}\right|^2,
\]

and its inverse square integrates to `pi/28`, exactly as (1) predicts.
The complex off-diagonal entries test the conjugation in the translation center.

## 2. A short adapter to the existing Lean Hua bound

A proof of the exact equality (1) is not required for the simplification.
The current source already contains

`New.lintegral_norm_det_add_inv_pow_le`

in `Lib/General/Analysis/HolomorphicIntegrals.lean:666--692`. In mathematical
notation, it states that for `R` an invertible `i x i` matrix, `Q>0` a `k x k`
matrix, `C>=0`, and `k>=7`,

\[
 \int_{A\in\mathbb C^{i\times k}}
 C\det\!\left(Q+(RA+c)^*(RA+c)\right)^{-(k+i)}\,dA
 \le C\,|\det R|^{-2k}(\det Q)^{-k}.
 \tag{10}
\]

Choose any invertible `R` with `R*R=S^{-1}`. Such a factor is provided by the
same strictly-positive C-star factorization used at lines 537--540 of the
current `HolomorphicIntegrals.lean`; no triangular factor is needed.
Sylvester's determinant identity changes (5) into

\[
 \boxed{\det(H+[U,v]^*[U,v])
   =\det H\;\det\!\left(G^{-1}+
                  (R(U-U_c)^*)^*(R(U-U_c)^*)\right).}
 \tag{11}
\]

The coefficient here is `a det S det G=det H`. In the actual application
`U=U_b+A*`, where the source variable `A` already has size `i x k`. Hence

\[
 R(U-U_c)^*=RA+R(U_b-U_c)^*.
\]

Equation (10) applies literally to the source variable with

\[
 Q=G^{-1},\quad c=R(U_b-U_c)^*,\quad C=(\det H)^{-(k+i)}.
\]

Its bound is

\[
 (\det H)^{-(k+i)}(\det S)^k(\det G)^k
 =(\det H)^{-i}a^{-k}.
 \tag{12}
\]

Thus the proposed Lean replacement does not need a new two-sided Jacobian
lemma, a transpose/conjugation measure-preserving lemma, or a gamma-function
evaluation. The source variable is already in the orientation required by the
existing API. Only finite-dimensional matrix algebra is new.

## 3. Canonical dual frame in the source's notation

Write `J=mathfrak{s}.J_1`, let `F=mathfrak{s}.frameCols` be the full frame, and
let `X` be `mathfrak{s}.definiteCols`, whose columns are the basis of `X_0`.
The full frame has `n=rho_rank+1` columns, where the source writes the rank as
`mathfrak{s}.varrho`; below the separate real size parameter is called `rho`.
Set

\[
 i=\min(\varrho,j),\quad q=i+1,\quad
 E=\operatorname{inclMatrix}(\operatorname{subframeIndex}),\quad F_s=FE,
\]

\[
 Z=F^*J\gamma F,\qquad B=E^*ZE,\qquad D=ZEB^{-1}.
 \tag{13}
\]

The hypothesis `h_delta` is precisely `det B != 0`; write
`delta=|det B|>0`. The source already defines `D` as `dualProducts hi Z`
and proves `E*D=I` in `inclMatrix_mul_dualProducts`.

Let `P_y=frameLeftInverse y`. The identities already proved in the source give
`P_yF=I`, and the columns of `JP_y*` lie in `yV_-`. Define, with no choices,

\[
 \boxed{\Omega=JP_y^*D,\qquad
          P=\gamma F_sB^{-1},\qquad
          H=-\Omega^*J\Omega,\qquad
          V=X^*(P-\Omega).}
 \tag{14}
\]

This `Omega` is exactly the intermediate `omega_0` already constructed at
`OneRealPlace.lean:482--497`, before the current proof normalizes it.

Both `Omega` and `P` pair with the full frame by the matrix `D`:

\[
 F^*J\Omega=D=F^*JP,\qquad F_s^*J\Omega=I_q.
 \tag{15}
\]

Put `W=y^{-1}Omega` and `T=y^{-1}F_s`. Since `JW=-W`, equations (15) imply
`T*W=-I_q`. In particular `W` is injective, and

\[
 H=W^*W>0.
 \tag{16}
\]

Since `P-Omega` is orthogonal to the full frame, the existing
`gram_definiteCols_mul_eq` gives

\[
 V^*V=(P-\Omega)^*J(P-\Omega).
 \tag{17}
\]

### 3.1 Reduce the volume ratio directly

Let `N=P_y gamma F`. The source proves

\[
 \nu(\gamma,y)=|\det N|
\]

as `volumeRatio_eq_norm_det`. The existing elementary determinant lemma
`norm_det_eq_norm_det_mul_inclMatrix` reduces this to

\[
 \boxed{\nu(\gamma,y)=|\det(D^*NE)|.}
 \tag{18}
\]

For completeness, its hypotheses follow directly from the shared isotropic
vectors in `NormOnePairOccursFrom j gamma`. First `D*E=I`, the adjoint of (15).
For each omitted frame index the norm-one pair supplies `x,x'` with
`gamma F x'=F x`, with `x_top=0` and the required triangular leading
coefficients. Then `Nx'=x`. The existing
`conjTranspose_realFrameGram_mulVec` gives
`Z*x=-x'_top e_top` and `|x'_top|=|x_top|=0`, so

\[
 D^*x=B^{-*}E^*Z^*x=0.
\]

These are exactly the hypotheses of the determinant reduction. No arbitrary
negative basis or reconstruction theorem is necessary.

If `K=Omega*JP`, then the definitions and `J*=J`, `J^2=I` give

\[
 K=D^*NEB^{-1},\qquad |\det K|=\nu(\gamma,y)/\delta.
 \tag{19}
\]

### 3.2 The determinant lower bound

The form on the image of the frame is nonpositive, so `-P*JP>=0`.
Expanding (17) gives

\[
 -K-K^*-(H+V^*V)=-P^*JP\ge0.
\]

Apply the same Ostrowski--Taussky inequality already used in the source to
the positive definite matrix `H+V*V` and the matrix `-K`. By (19),

\[
 \boxed{\nu(\gamma,y)\ge
        2^{-(i+1)}\delta\det(H+V^*V).}
 \tag{20}
\]

This is the unnormalized version of the current triangular-frame lower bound.
Its essential improvement is that no `L`, leading submatrix of `L`, or last
diagonal entry of `L` appears.

### 3.3 Translation has no coefficient matrix

The hypothesis of the public majorant theorem is

\[
 X^*\gamma F_s=X^*\gamma_0F_s+A^*B_{\mathrm{first}\ i\ \mathrm{rows}}.
\]

Multiplying by `B^{-1}` yields

\[
 V_\gamma=V_{\gamma_0}+[A^*,0].
 \tag{21}
\]

Write `V_gamma0=[U_b,v]`. The final column `v` is fixed, precisely as required
by the bordered integral. The current translated matrix is instead
`V_gamma0+A*L_first_rows`; (21) removes this bookkeeping at its source.

## 4. Recover the exact rho and theta factors

### 4.1 The frame-box estimate

The hypothesis `y in frameBox rho` bounds each column of `T=y^{-1}F_s`
by `rho`. The Gram matrix of `[T,W]` is positive semidefinite. Its mixed block
is `T*W=-I`, so determinant Cauchy--Schwarz gives

\[
 1=|\det(T^*W)|^2\le\det(T^*T)\det H.
\]

The existing `norm_det_sq_le_of_posSemidef` proves this matrix inequality.
Hadamard's inequality, already available as `New.hadamard_det_inequality`
in `MinorProducts.lean:278--293`, gives

\[
 \det(T^*T)\le\prod_{a=1}^{i+1}\|T_a\|^2\le\rho^{2(i+1)}.
\]

Therefore

\[
 \boxed{(\det H)^{-1}\le\rho^{2(i+1)}.}
 \tag{22}
\]

No orthogonalization or chosen orthonormal basis is required.

### 4.2 Lower levels: the fixed energy is exactly one

Suppose `j<=varrho`, so `i=j`. The source lemma
`exists_common_vector_of_normOnePairOccursFrom` supplies `x,c` with

\[
 |x_z|=1,\quad \gamma F_sc=Fx,\quad Bc=-x_z e_z.
\]

Consequently the last column of `P` is
`P_z=-(x_z)^{-1}Fx`. It has Hermitian square `-1`.
Set `d=P_z-Omega_z`; it is orthogonal to the full frame, hence to `P_z`,
and its Hermitian square is `||v||^2`. Thus

\[
 -H_{zz}=\Omega_z^*J\Omega_z=-1+\|v\|^2,
 \qquad \boxed{H_{zz}+\|v\|^2=1.}
 \tag{23}
\]

This is the source's current last-column identity with the normalization
already cancelled.

### 4.3 Top level: the fixed energy is at least theta^{-2}

At `j=varrho+1`, `i=varrho`, so the subframe is the full frame, `E=I`, and
`D=I`. Equations (15) imply that `Omega_z` pairs to one with `z` and to zero
with the isotropic vectors.

Use the existing `exists_norm_le_of_besselLength_le`: the hypothesis
`besselLength y<=theta` gives a Bessel unipotent `u` with `||uy||<=theta`.
The vector `u^{-1}z` differs from `z` by an isotropic frame vector, so

\[
 1=|\langle u^{-1}z,\Omega_z\rangle_J|
   \le \|y^{-1}u^{-1}z\|\,\|y^{-1}\Omega_z\|
   \le\theta\sqrt{H_{zz}}.
\]

Here the usual equality of the norms of a `J`-unitary matrix and its inverse
is already part of the source API. Hence `H_zz>=theta^{-2}`. Together with
(23), both cases give

\[
 \boxed{a=H_{zz}+\|v\|^2\ge\theta^{-2(j-i)}.}
 \tag{24}
\]

Only the top level uses the length parameter.

## 5. The unchanged public majorant

Set `s=k+i`, `q=i+1`, and define the explicit measurable function

\[
 \phi(A)=\left(\frac{2^q}{\delta}\right)^s
      \det\!\left(H+[U_b+A^*,v]^*[U_b+A^*,v]\right)^{-s}.
 \tag{25}
\]

The determinant is strictly positive everywhere, so measurability follows
from continuity. Equations (20)--(21) prove `nu(gamma,y)^{-s}<=phi(A)` under
the existing translation hypotheses. Applying (9), or directly (10)--(12),
then (22) and (24), gives

\[
\begin{aligned}
 \int\phi(A)\,dA
 &\le \left(\frac{2^{i+1}}{\delta}\right)^{k+i}
                (\det H)^{-i}a^{-k}\\
 &\le \frac{2^{(i+1)(k+i)}
          \rho^{2i(i+1)}\theta^{2k(j-i)}}{\delta^{k+i}}\\
 &=\frac{(2\rho^2)^{(i+1)i}
         (2^{i+1}\theta^{2(j-i)})^k}{\delta^{k+i}}.
\end{aligned}
 \tag{26}
\]

This is exactly the existing conclusion, including every exponent and power
of two. The source's use of `ENNReal.ofReal` introduces no new issue because
all the displayed real factors are nonnegative. The `i=0` case is covered by
empty matrices and the zero-dimensional integral convention above.

## 6. Proposed Lean implementation order

1. Add the block determinant identity (11) and its positivity hypotheses in a
   general matrix helper. Use a sum-indexed block matrix internally; reindex
   `Fin (i+1)` only at the adapter. Apply the existing positive factorization
   to `S^{-1}` and the existing Hua inequality. It is unnecessary to formalize
   the gamma constant for this refactor.
2. Define the canonical matrices in (14). Reuse the first half of
   `exists_isTriangularBasis` for their pairing, negative-space, and positive
   Gram facts. Do not construct `L`.
3. Prove (18) by specializing `norm_det_eq_norm_det_mul_inclMatrix` to `D`;
   prove (20) by the current Ostrowski--Taussky argument with `H` replacing
   `I`.
4. Replace the translation lemma by (21), prove the Gram determinant bound
   (22), and translate the two existing final-column arguments to (23)--(24).
5. Replace the proof, but preserve the statement, of
   `RealPlace.exists_majorant_volumeRatio_inv_pow` using (25)--(26).
6. Rebuild the changed module and its direct caller; then rebuild `Main` and
   inspect the final theorem's assumptions. Only after this can a net source
   reduction and kernel validation of the replacement be reported.

The public theorem currently has its only nonlocal reference in
`New/Spanning/RemainingTerms/SchurOrbit.lean:553`. Its wrapper
`HasCellRank.exists_majorant_lintegral_le_kernelBound` at lines 535--575 can
remain unchanged.

## 7. Audited source replacement/removal regions

All line numbers refer to the pinned commit, and counts include comments and
blank lines. These are gross affected regions, not net deletion estimates.

| File | Lines | Count | Action |
|---|---:|---:|---|
| `OneRealPlace.lean` | 241--282 | 42 | Remove the two arbitrary-negative-frame reconstruction helpers |
| `OneRealPlace.lean` | 360--426 | 67 | Replace `IsNegativeBasis` and its quotient theorem by (18)--(19) |
| `OneRealPlace.lean` | 449--707 | 259 | Replace triangular normalization, determinant tracking, and translation |
| `OneRealPlace.lean` | 795--1008 | 214 | Replace final-column bounds and the majorant proof; preserve public statement |
| `HermitianMatrices.lean` | 71--99 | 29 | Remove the now-unused triangular normalization existence lemma |
| **Total** | | **611** | **22 local declarations and one support declaration affected** |

The 22 local declarations comprise two reconstruction lemmas, the general
negative-basis structure and theorem, 14 declarations in the triangular-frame
section, and four declarations in the final-column section. Many of their
mathematical roles are replaced, rather than merely deleted.

The name `New.exists_lowerTriangular_conjTranspose_mul_mul_eq_one` has exactly
one call site in the project, inside `exists_isTriangularBasis`. All source
references to `IsNegativeBasis` and `IsTriangularBasis` occur in
`OneRealPlace.lean`. In contrast, the determinant reduction lemma, the shared
vector lemma, the subframe determinant formula, and the unipotent translation
formula should remain.

No complete module is made unreachable. In particular:

- `BorderedDeterminant.lean` contains arithmetic link/gauge constructions used
  elsewhere. Its name does not mean the present integral can replace it.
- `Bessel/Basic.lean` has a different Gram--Schmidt frame used by rational
  fundamental-domain coordinates, box bounds, and packing. It is retained.
- `Frames/RealPlaceGauge.lean` uses a common orthogonal kernel and sphere
  density for two simultaneous metrics. That argument is retained.
- The existing ordinary Hua integral and determinant inequalities remain
  shared infrastructure. Their removal is not part of this proposal.

## 8. Nonduplication and validation

The proposal-corpus audit examined all 28 proposal directories at this pin.
The scanned main TeX/README/planning text contains no hits for `OneRealPlace`,
`RemainingTerms`, `Bessel`, `negative basis`, `volumeRatio`, `isotropic quotient`,
`Schur complement`, `majorant`, or `Gram--Schmidt`. The existing Gram-adjoint
proposal concerns integral comparison operators and inverse Fock Gram forms;
it does not perform this bordered-integral replacement. The branching proposal
uses a Schur commutant/highest-vector argument, again on another object.
This establishes a concrete source-level distinction; novelty in the wider
mathematical literature is not claimed.

`check_bordered_hua.py` was run with SymPy 1.14.0 and seed 20261128. It passed:

- 36 exact rational-complex tests with `H=R*R+I`, dimensions `1<=k<=3` and
  `0<=i<=3`, including the empty-column edge case. Each test checks the block
  congruence, translation center, Schur identity, both determinant factors,
  inverse of `G`, and the direct adapter identity (11).
- Nine exact real-Jacobian determinant checks for `Z -> LZR`, in real
  dimensions 2 through 18, verifying the exponents `2i` and `2k`.
- Symbolic cancellation of every determinant and scalar factor in (6), (12),
  and the match of source constants in (26).
- The ordinary-Hua constant recurrence for these dimensions, and the exact
  radial integral `pi/28` in the asymmetric scalar example.

The machine-readable output is `bordered_hua_checks.json`. These checks catch
conjugation, exponent, and transpose errors in the new algebra. They do not
establish the complete Lean integration or certify the overall GRH proof.
