import Lib.Weil.DualPair.WeilAction

/-!
# Mixed models and zero terms of a pair with one split space: Levi and radical laws

Let V = range l ⊕ ιV₀ ⊕ range k be a splitting of a hermitian space V over V₀
(`New.Space.Splitting`: isotropic dual frames k, l and an isometry ι, the field `i`, from V₀), and
let T be another space. The splitting induces splittings of Hom(V,T) and Hom(T,V). This file
computes, for these, the zero term and the mixed model of the representation `New.pairWeil` of the
pair.

* `New.Space.Splitting.homSource`, `New.Space.Splitting.homTarget`: the induced splittings of
  Hom(V,T) over Hom(V₀,T) and of Hom(T,V) over Hom(T,V₀).
* `New.Space.Splitting.homSlice`: the term f[x] of an adelic n' × p matrix x in the mixed model;
  `New.Space.Splitting.hasSum_theta_homSlice`: θ(f) is the sum of the θ(f[T.x⁻¹x]) over rational
  x; `New.Space.Splitting.symm_homSource_zeroTerm_eq_integral`: the integral of the terms over
  adelic x is the zero term for the splitting with k and l exchanged;
  `New.Space.Splitting.homSlice_rho`: the law of f[x] under the Heisenberg operators.
* `New.Space.Splitting.homSource_zeroTerm_pairWeil`,
  `New.Space.Splitting.homTarget_zeroTerm_pairWeil`: the zero term of ω(g,h)f, resp. ω(h,g)f, when
  gk = km.
* `New.Space.Splitting.homSlice_levi`, `New.Space.Splitting.homSlice_radicalElement`: the laws of
  f[x] under the Levi subgroup and under the radical of the stabiliser of range k.

Notions from other files:
* `New.pairWeil V T a b (g, h)`, written ω_{a,b}(g,h): the Weil representation of x ↦ h x g⁻¹ on the
  data of Hom(V,T), twisted by a(det h) b(det g)⁻¹.
* `New.Space.ϱ`: the Heisenberg operators on the data space 𝒮 of a space.
* `New.Space.Splitting.zeroTerm` (ev): the mean of f(ιy + kb) over b in 𝔸^p / E^p;
  `New.Space.Splitting.slice x f` is ev(ϱ(lx) f).

`kAdelic`, `iAdelic` and `lAdelic` are the frames in adelic coordinates; `kCoord`, `iCoord` and
`lCoord` send kb + ιw + la to b, w and a. In formulas ȷ is `WeilData.j`, ψ is `stdAddChar`, υ is the
splitting character and * is the conjugate transpose.

## Relation to the literature

Known; see `Lib.Weil.DualPair.ThetaLiftConvergence` for sources.
-/

noncomputable section

namespace New.Space

open Matrix Kronecker WeilData G Fintype AutChar

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {s : n → ℤˣ} {s' : n' → ℤˣ}
  {n₀ p : Type} [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p]
  {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p) (T : Space E n' s')
  (a b : AutChar E) {n₁ q : Type} [Fintype n₁] [DecidableEq n₁] [Fintype q] [DecidableEq q]
  {s₁ : n₁ → ℤˣ} {V₁ : Space E n₁ s₁}

/-- For a space T with adelic frame x, the invertible adelic matrix (x⁻¹)* ε, with inverse ε x*,
where ε is the standard form of its signs. -/
def dualFrame : GL n' (𝔸 E) where
  val := T.x⁻¹.1ᴴ * stdForm E s'
  inv := stdForm E s' * T.xᴴ
  val_inv := by simp [conjTranspose_nonsing_inv, Matrix.mul_assoc]
  inv_val := by simp [conjTranspose_nonsing_inv, Matrix.mul_assoc]

/-- For q = (g, h), the Heisenberg operator ϱ(x) of Hom(V,T) moves past ω_{a,b}(q) by turning x,
read as an n' × n matrix, into h⁻¹xg: ϱ(x) ω(q) f = ω(q) ϱ(h⁻¹xg) f. -/
lemma rho_pairWeil (q : G E s × G E s') (x : n' × n → 𝔸 E) (f : 𝒮 (V.hom T)) :
    ϱ (V.hom T) x (pairWeil V T a b q f) =
      pairWeil V T a b q (ϱ (V.hom T) (matrixToVec
        (q.snd⁻¹.adeleMatrix * vecToMatrix x * q.fst.adeleMatrix)) f) := by
  -- ↓: `adeleMatrix_onHom` must act before simp unfolds the matrix of `onHom` into `toUnitary`.
  simp [pairWeil, omega_rho, ↓adeleMatrix_onHom, adeleMatrix, Matrix.mul_assoc,
    kronecker_mulVec_eq_matrixToVec]

namespace Splitting

/-! ### The induced splittings and their frames -/

/-- From a splitting (k, l, ι) of V over V₀, the splitting of Hom(V,T) over Hom(V₀,T) with
frames J_T⁻¹⊗(k*J)ᵀ, 1⊗(l*J)ᵀ, 1⊗(J₀⁻¹ι*J)ᵀ; the first spans the maps killing k^⊥. -/
def homSource : (V.hom T).Splitting (V₀.hom T) (n' × p) where
  k := T.J⁻¹ ⊗ₖ (D.kᴴ * V.J)ᵀ
  l := 1 ⊗ₖ (D.lᴴ * V.J)ᵀ
  i := 1 ⊗ₖ (V₀.J⁻¹ * D.iᴴ * V.J)ᵀ
  gram_kk := by simp [conjTranspose_kronecker, conjTranspose_J, hom_J,
    conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul]
  gram_ll := by simp [conjTranspose_kronecker, conjTranspose_J, hom_J,
    conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul]
  gram_lk := by
    rw [← conjTranspose_inj]
    simp [-gram_kl, conjTranspose_kronecker, hom_J, Matrix.mul_assoc,
      conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul]
  gram_ii := by
    rw [← conjTranspose_inj]
    simp [conjTranspose_kronecker, hom_J, Matrix.mul_assoc,
      conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul]
  gram_ik := by
    rw [← conjTranspose_inj]
    simp [conjTranspose_kronecker, hom_J, Matrix.mul_assoc,
      conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul]
  gram_il := by
    rw [← conjTranspose_inj]
    simp [conjTranspose_kronecker, hom_J, Matrix.mul_assoc,
      conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul]
  card_eq := by
    simp [D.card_eq]
    ring

/-- From a splitting (k, l, ι) of V over V₀, the splitting of Hom(T,V) over Hom(T,V₀) with
frames k⊗J_Tᵀ, l⊗1, ι⊗1. -/
def homTarget : (T.hom V).Splitting (T.hom V₀) (p × n') where
  k := D.k ⊗ₖ T.Jᵀ
  l := D.l ⊗ₖ 1
  i := D.i ⊗ₖ 1
  gram_kk := by simp [conjTranspose_kronecker, hom_J, ← mul_kronecker_mul]
  gram_ll := by simp [conjTranspose_kronecker, hom_J, ← mul_kronecker_mul]
  gram_lk := by simp [conjTranspose_kronecker, hom_J, ← mul_kronecker_mul, ← transpose_mul]
  gram_ii := by simp [conjTranspose_kronecker, hom_J, ← mul_kronecker_mul]
  gram_ik := by simp [conjTranspose_kronecker, hom_J, ← mul_kronecker_mul]
  gram_il := by simp [conjTranspose_kronecker, hom_J, ← mul_kronecker_mul]
  card_eq := by
    simp [D.card_eq]
    ring

/-- The zero term on Hom(V,T) is the same for two splittings of V with orthogonal frames k and
equal ι. -/
lemma zeroTerm_homSource_congr {D' : V.Splitting V₀ q} (hk : D'.kᴴ * V.J * D.k = 0)
    (hi : D'.i = D.i) :
    (D'.homSource T).zeroTerm = (D.homSource T).zeroTerm := by
  apply zeroTerm_congr
  · simp [hk, hom, homSource, conjTranspose_kronecker, conjTranspose_J,
      conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul]
  · simp [hi, homSource]

/-- Zero terms on Hom(·, T) can be taken in stages: for splittings D of V over V₀ and D' of V₀ over
V₁, the zero term for the splitting of Hom(V,T) induced by the composite `D.comp D'` is the zero
term for D' applied after the zero term for D. -/
lemma zeroTerm_homSource_comp (D' : V₀.Splitting V₁ q) (f : 𝒮 (V.hom T)) :
    ((D.comp D').homSource T).zeroTerm f =
      (D'.homSource T).zeroTerm ((D.homSource T).zeroTerm f) := by
  -- By `zeroTerm_congr`, as `(D.comp D').k` is isotropic, the zero term is that of
  -- `(D.homSource T).comp (D'.homSource T)`, which `zeroTerm_comp` computes in stages.
  have h_iso := (D.comp D').gram_kk
  have h_zeroTerm_eq :
      ((D.comp D').homSource T).zeroTerm = ((D.homSource T).comp (D'.homSource T)).zeroTerm := by
    apply zeroTerm_congr
    · -- simp_all, not simp: the blocks of `h_iso` are needed to simplify the goal.
      simp_all [comp, hom, homSource, ← ext_iff, Matrix.mul_assoc, conjTranspose_kronecker,
        conjTranspose_fromCols_eq_fromRows_conjTranspose, conjTranspose_J, ← mul_kronecker_mul,
        conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul]
    · simp [comp, hom, homSource, Matrix.mul_assoc, ← mul_kronecker_mul, ← transpose_mul,
        conjTranspose_fromCols_eq_fromRows_conjTranspose]
  rw [h_zeroTerm_eq, zeroTerm_comp]

section

omit [WeilData E]

/-- The adelic k-frame of the splitting `New.Space.Splitting.homSource` of Hom(V,T) is the Kronecker
product of the inverse of `New.Space.dualFrame` of T with the transpose of `lCoord`. -/
lemma homSource_kAdelic : (D.homSource T).kAdelic = ↑T.dualFrame⁻¹ ⊗ₖ D.lCoordᵀ := by
  simp [kAdelic, hom, homSource, Matrix.mul_assoc, map_kronecker, map_J_inv, transpose_map, map_J,
    ← mul_kronecker_mul, ← transpose_mul, dualFrame, lCoord]

/-- The adelic l-frame of the splitting `New.Space.Splitting.homSource` of Hom(V,T) is the Kronecker
product of x_T⁻¹ with the transpose of `kCoord`, where x_T is the point of T. -/
lemma homSource_lAdelic : (D.homSource T).lAdelic = ↑T.x⁻¹ ⊗ₖ D.kCoordᵀ := by
  simp [lAdelic, hom, homSource, Matrix.mul_assoc, map_kronecker, transpose_map, map_J,
    ← mul_kronecker_mul, ← transpose_mul, kCoord]

lemma homSource_iAdelic : (D.homSource T).iAdelic = 1 ⊗ₖ D.iCoordᵀ := by
  simp [iAdelic, ratMap, hom, homSource, Matrix.mul_assoc, map_kronecker, transpose_map, map_J_inv,
    map_J, ← mul_kronecker_mul, ← transpose_mul, iCoord]

lemma homTarget_kAdelic : (D.homTarget T).kAdelic = D.kAdelic ⊗ₖ T.dualFrameᵀ := by
  simp [kAdelic, hom, homTarget, map_kronecker, transpose_map, map_J, ← mul_kronecker_mul,
    ← transpose_mul, dualFrame]

lemma homTarget_iAdelic : (D.homTarget T).iAdelic = D.iAdelic ⊗ₖ 1 := by
  simp [iAdelic, ratMap, hom, homTarget, map_kronecker, ← mul_kronecker_mul, ← transpose_mul]

end

/-! ### The mixed model on Hom(V,T) -/

/-- For an adelic n′×p matrix x, the map f ↦ f[x]: the zero term, along maps killing k^⊥, of
ϱ(x̃)f, where x̃ ∈ Hom(V,T) has x̃k = x and kills l, ι. -/
def homSlice (x : Matrix n' p (𝔸 E)) : 𝒮 (V.hom T) →L[ℂ] 𝒮 (V₀.hom T) :=
  (D.homSource T).zeroTerm ∘L ϱ (V.hom T) (matrixToVec (x * D.kCoord))

/-- For a splitting `D` of V over V₀ and an adelic n′ × p matrix x, `New.Space.Splitting.homSlice`
at x_T⁻¹x (x_T the point of T) equals `New.Space.Splitting.slice` at x, read as a vector on n′ × p,
for `homSource`. That is the splitting of Hom(V,T) over Hom(V₀,T) induced by `D`. A slice at x is
the bounded map f ↦ ev(ϱ(lx)f) from 𝒮(Hom(V,T)) to 𝒮(Hom(V₀,T)). -/
lemma homSlice_eq_slice (x : Matrix n' p (𝔸 E)) :
    D.homSlice T (T.x⁻¹.val * x) = (D.homSource T).slice (matrixToVec x) := by
  simp [homSlice, slice, homSource_lAdelic, kronecker_mulVec_eq_matrixToVec]

/-- For split V and any datum f on Hom(V,T), θ(f) is the convergent sum of the θ(f[x]) over
rational n' × p matrices x, taken at the adelic matrices x_T⁻¹x (x_T the point of T), f[x] being
the term of x in the mixed model. -/
lemma hasSum_theta_homSlice (f : 𝒮 (V.hom T)) :
    HasSum (fun x : Matrix n' p E ↦
      θ (V₀.hom T) (D.homSlice T (T.x⁻¹.val * Matrix.map x toAdele) f))
      (θ (V.hom T) f) := by
  simp_rw [homSlice_eq_slice]
  exact (Equiv.curry n' p E).hasSum_iff.mp ((D.homSource T).hasSum_theta_slice f)

/-- On Hom(V,T), the zero term for the splitting with k and l exchanged, that is along the maps
killing l^⊥, is the integral over adelic x, in rational coordinates, of the terms of the mixed model
(the terms f[x_T⁻¹x], by `New.Space.Splitting.homSlice_eq_slice`). -/
lemma symm_homSource_zeroTerm_eq_integral (f : 𝒮 (V.hom T)) :
    (D.symm.homSource T).zeroTerm f = ∫ x : n' × p → 𝔸 E, (D.homSource T).slice x f := by
  -- Replace the zero term by that of `H.symm`; it is a mean over the quotient by the rational
  -- vectors, which unfolds into the integral of the mixed model.
  set H : (V.hom T).Splitting (V₀.hom T) (n' × p) := D.homSource T
  -- Both splittings have the same `i`, and their frames `k` are orthogonal, as `l` is isotropic.
  have h_zeroTerm_symm : (D.symm.homSource T).zeroTerm = H.symm.zeroTerm := by
    apply H.symm.zeroTerm_congr
    · simp [symm, homSource, H, gram_ll, conjTranspose_kronecker, conjTranspose_J, hom_J,
        conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul]
    · simp [symm, homSource, H]
  ext y
  -- At each `x`, the values of the terms `f[ξ + x]` at `y` sum over rational `ξ` to the value of
  -- `f` at `ι y + l x`: the expansion `hasSum_theta_slice` of θ at the translate of `f`.
  have h_sum (x : n' × p → 𝔸 E) :
      HasSum (fun ξ : New.ratVectors E (n' × p) ↦ H.slice (ξ +ᵥ x) f y)
        (f (H.iAdelic *ᵥ y + H.lAdelic *ᵥ x)) := by
    refine (Equiv.ofInjective _ (toAdele (E := E)).injective.comp_left).hasSum_iff.mp ?_
    -- After reindexing, the index is a rational vector ξ, which acts by adding `toAdele ∘ ξ`.
    show HasSum (fun ξ : n' × p → E ↦ H.slice (toAdele ∘ ξ + x) f y) _
    simpa [mulVec_add] using
      H.hasSum_theta_slice ((V.hom T).ϱ (H.iAdelic *ᵥ y + H.lAdelic *ᵥ x) f)
  -- Evaluation at `y` is the continuous linear map `evalAt`, so it commutes with the integral.
  let evalAt := (V₀.hom T).rawTheta ∘L (V₀.hom T).ϱ y
  have h_int := H.integrable_slice f
  -- Unfold the mean over the quotient by the rational vectors, which has volume one.
  have h_unfold :
      quotMean (New.ratVectors E (n' × p)) (fun x ↦ f (H.iAdelic *ᵥ y + H.lAdelic *ᵥ x)) =
        ∫ x, evalAt (H.slice x f) := by
    simpa [symm, kAdelic, lAdelic, iAdelic] using
      quotMean_tsum_eq_integral _ _ (evalAt.integrable_comp h_int)
        (H.symm.isContPeriodic_along_k f y) h_sum
  rw [h_zeroTerm_symm, zeroTerm_apply]
  exact h_unfold.trans (evalAt.integral_comp_comm h_int)

/-- For split V, y in Hom(V,T) and f[x] = `New.Space.Splitting.homSlice` x f:
(ϱ(y)f)[x] = ψ(½ȷ tr((yl)*ε'(2x + yk))) ϱ(yι) f[x + yk], with ε' the standard form of T. -/
lemma homSlice_rho (x : Matrix n' p (𝔸 E)) (y : Matrix n' n (𝔸 E)) (f : 𝒮 (V.hom T)) :
    D.homSlice T x (ϱ (V.hom T) (matrixToVec y) f) =
      (stdAddChar E
          (toAdele (j / 2) *
            ((y * D.lAdelic)ᴴ * stdForm E s' * (x + x + y * D.kAdelic)).trace)).val •
        ϱ (V₀.hom T) (matrixToVec (y * D.iAdelic)) (D.homSlice T (x + y * D.kAdelic) f) := by
  -- The law `isMixedLaw_slice` of the splitting `D.homSource T`, in matrix coordinates.
  simpa [adelicHeisenberg, add_assoc, kCoord, lCoord, iCoord, dualFrame, homSlice, slice,
    homSource_lAdelic, homSource_kAdelic, homSource_iAdelic, conjTranspose_kronecker, mulVec_add,
    kronecker_mulVec_eq_matrixToVec, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul,
    conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul] using
    (D.homSource T).isMixedLaw_slice (matrixToVec (T.x.val * x)) (matrixToVec y) f

/-- The character `New.WeilData.upsilonU1` is υ on the norm-one ideles. -/
private lemma upsilonU1_apply (u : unitary (𝔸 E)) : upsilonU1.val u = υ.1 (Unitary.toUnits u) :=
  rfl

/-- On a norm-one idele u, the character `New.chiAdelic` x ↦ υ(x)|x|^(−1/2) is υ: the idele norm
of u is one. -/
@[simp↓]
lemma chiAdelic_toUnits (u : unitary (𝔸 E)) : chiAdelic (Unitary.toUnits u) = upsilonU1.val u := by
  simp [ideleAbs_eq_one_of_mem_unitary, chiAdelic, upsilonU1_apply]

omit [WeilData E] in
/-- If g k = k m for an invertible adelic p × p matrix m (`hk`), and g₀ is the block of g on ιV₀,
that is, the ι-coordinates of gι (`hi`), then det g = (det m / star (det m)) · det g₀. -/
lemma det_eq_divStar_mul (g : G E s) (g₀ : G E s₀) (m : GL p (𝔸 E)) (hk : D.ActsOnFrame g m.val)
    (hi : D.iCoord * (g.adeleMatrix * D.iAdelic) = adeleMatrix (s := s₀) g₀) :
    g.det = divStar m.det * g₀.det := by
  -- In the frame `(k, ι, l)` the matrix of `g` is block triangular with diagonal blocks
  -- `m`, `g₀` and `m⁻¹ᴴ`.
  let P : Matrix n ((p ⊕ n₀) ⊕ p) (𝔸 E) := (D.kAdelic.fromCols D.iAdelic).fromCols D.lAdelic
  let Q : Matrix ((p ⊕ n₀) ⊕ p) n (𝔸 E) := (D.kCoord.fromRows D.iCoord).fromRows D.lCoord
  have hPQ : P * Q = 1 := by simpa [P, Q, fromCols_mul_fromRows] using D.sum_frame_mul_coord_eq_one
  -- ↓: the block products must be formed before simp rewrites the blocks themselves.
  have hQP : Q * P = 1 := by simp [P, Q, ↓fromRows_mul_fromCols]
  have h_det : (g.det : 𝔸 E) = (m.det : 𝔸 E) * g₀.det * star ((m.det⁻¹ : (𝔸 E)ˣ) : 𝔸 E) := by
    rw [coe_det, ← det_conj_of_mul_eq_one hQP hPQ, fromRows_mul]
    simp [P, D.lCoord_mul_adeleMatrix hk, ↓fromRows_mul_fromCols, hk, hi, Matrix.mul_assoc]
  -- Reorder: det m · star (det m)⁻¹ is divStar (det m).
  apply Subtype.ext
  rw [h_det, Submonoid.coe_mul, coe_divStar]
  ring

/-- Suppose g k = k m with m ∈ GL_p(𝔸) (`hk`), and g₀ is the block of g on ιV₀ (`hi`). On Hom(V,T),
ev ω_{aυ^p,b}(g,h)f = χ_T(det m)⁻¹ |det m|^(n′/2) ω_{a,b}(g₀,h) ev f,
with ev the zero term, n′ the rank of T and χ_T(x) = b(x/x̄)υ(x)^(−n′) (`New.AutChar.spaceChar`). -/
lemma homSource_zeroTerm_pairWeil (g : G E s) (g₀ : G E s₀) (m : GL p (𝔸 E))
    (hk : D.ActsOnFrame g m.val)
    (hi : D.iCoord * (g.adeleMatrix * D.iAdelic) = adeleMatrix (s := s₀) g₀) (h : G E s')
    (f : 𝒮 (V.hom T)) :
    (D.homSource T).zeroTerm (pairWeil V T (a * upsilonU1 ^ card p) b (g, h) f) =
      (((b.spaceChar (card n')).val m.det).val⁻¹ * √(ideleAbs m.det) ^ card n') •
        pairWeil V₀ T a b (g₀, h) ((D.homSource T).zeroTerm f) := by
  -- On the maps `x' * D.lCoord` the pair `(g, h)` acts by `x' ↦ h x' mᴴ` (in the coordinates
  -- `T.dualFrame`).
  let M : Matrix (n' × p) (n' × p) (𝔸 E) :=
    (T.dualFrame.val * h.adeleMatrix * T.dualFrame⁻¹.val) ⊗ₖ m.valᴴᵀ
  have h_lCoord_inv : D.lCoord * g⁻¹.adeleMatrix = m.valᴴ * D.lCoord := by
    have h_adj : (g.adeleMatrix * D.kAdelic)ᴴ = (D.kAdelic * m.val)ᴴ := congrArg conjTranspose hk
    simpa [lCoord, adeleMatrix_inv, Matrix.mul_assoc] using congrArg (· * stdForm E s) h_adj
  have h_onHom_kAdelic :
      (G.onHom (g, h)).adeleMatrix * (D.homSource T).kAdelic = (D.homSource T).kAdelic * M := by
    simp [M, h_lCoord_inv, homSource_kAdelic, ← mul_kronecker_mul,
      ← transpose_mul, Matrix.mul_assoc]
  have h_onHom_iAdelic :
      (D.homSource T).iCoord * ((G.onHom (g, h)).adeleMatrix * (D.homSource T).iAdelic) =
        (G.onHom (g₀, h)).adeleMatrix := by
    -- Without -coord_mul_frame_mul, simp loops between it and the bracketing by mul_assoc.
    simp [iCoord, ← hi, adeleMatrix_inv, -coord_mul_frame_mul, homSource_iAdelic, Matrix.mul_assoc,
      conjTranspose_kronecker, conjTranspose_transpose_eq_transpose_conjTranspose,
      ← mul_kronecker_mul, ← transpose_mul]
  have h_det_M : M.det = (Unitary.toUnits h.det ^ card p * star m.det ^ card n').val := by
    rw [det_kronecker, det_units_conj, det_transpose, det_conjTranspose]
    simp
  -- The factors `upsilonU1 (det h) ^ p` cancel, and `det g = (det m / star (det m)) * det g₀`.
  -- ↓: map_mul and map_pow split the character values before simp unfolds the characters.
  have h_char : pairChar (a * upsilonU1 ^ card p) b (g, h) *
        (chiAdelic (Unitary.toUnits h.det ^ card p * star m.det ^ card n'))⁻¹ =
      ((b.spaceChar (card n')).val m.det).val⁻¹ * √(ideleAbs m.det) ^ card n' *
        pairChar a b (g₀, h) := by
    simp [pairChar_apply, D.det_eq_divStar_mul g g₀ m hk hi, ↓map_mul, ↓map_pow, chiAdelic, υ_star,
      mul_pow, spaceChar, baseChange_apply_coe_toFun]
    field_simp
  rw [pairWeil_apply, map_smul, (D.homSource T).zeroTerm_omega (G.onHom (g₀, h)) h_onHom_iAdelic
    h_onHom_kAdelic _ h_det_M, pairWeil_apply, smul_smul, smul_smul, h_char]

/-- Suppose g k = k m with m ∈ GL_p(𝔸) (`hk`), and g₀ is the block of g on ιV₀ (`hi`). On Hom(T,V),
ev ω_{a,bυ^p}(h,g)f = χ(det m) |det m|^(n′/2) ω_{a,b}(h,g₀) ev f, with ev the zero term, n′ the rank
of T and χ(x) = a(x/x̄)υ(x)^(−n′) (`New.AutChar.spaceChar`). -/
lemma homTarget_zeroTerm_pairWeil (g : G E s) (g₀ : G E s₀) (m : GL p (𝔸 E))
    (hk : D.ActsOnFrame g m.val)
    (hi : D.iCoord * (g.adeleMatrix * D.iAdelic) = adeleMatrix (s := s₀) g₀) (h : G E s')
    (f : 𝒮 (T.hom V)) :
    (D.homTarget T).zeroTerm (pairWeil T V a (b * upsilonU1 ^ card p) (h, g) f) =
      (((a.spaceChar (card n')).val m.det).val * √(ideleAbs m.det) ^ card n') •
        pairWeil T V₀ a b (h, g₀) ((D.homTarget T).zeroTerm f) := by
  -- On the maps `k y` the pair `(h, g)` acts by `y ↦ m y h⁻¹` (in the coordinates `T.dualFrame`).
  let M : Matrix (p × n') (p × n') (𝔸 E) :=
    m.val ⊗ₖ (T.dualFrame.val * h⁻¹.adeleMatrix * T.dualFrame⁻¹.val)ᵀ
  have h_onHom_kAdelic :
      (G.onHom (h, g)).adeleMatrix * (D.homTarget T).kAdelic = (D.homTarget T).kAdelic * M := by
    simp [M, hk, homTarget_kAdelic, ← mul_kronecker_mul, ← transpose_mul]
  have h_onHom_iAdelic :
      (D.homTarget T).iCoord * ((G.onHom (h, g)).adeleMatrix * (D.homTarget T).iAdelic) =
        (G.onHom (h, g₀)).adeleMatrix := by
    simp [iCoord, ← hi, homTarget_iAdelic, conjTranspose_kronecker,
      ← mul_kronecker_mul, ← transpose_mul]
  have h_det_M : M.det = (m.det ^ card n' * Unitary.toUnits h⁻¹.det ^ card p).val := by
    rw [det_kronecker, det_transpose, det_units_conj]
    -- The determinant of `h⁻¹` is that of its matrix, by definition.
    rfl
  -- The factors `upsilonU1 (det h) ^ p` cancel, and `det g = (det m / star (det m)) * det g₀`.
  -- ↓: map_mul and map_pow split the character values before simp unfolds the characters.
  have h_char : pairChar a (b * upsilonU1 ^ card p) (h, g) *
        (chiAdelic (m.det ^ card n' * Unitary.toUnits h⁻¹.det ^ card p))⁻¹ =
      ((a.spaceChar (card n')).val m.det).val * √(ideleAbs m.det) ^ card n' *
        pairChar a b (h, g₀) := by
    simp [pairChar_apply, D.det_eq_divStar_mul g g₀ m hk hi, ↓map_mul, ↓map_pow, chiAdelic, mul_pow,
      spaceChar, baseChange_apply_coe_toFun]
    field_simp
  rw [pairWeil_apply, map_smul, (D.homTarget T).zeroTerm_omega (G.onHom (h, g₀)) h_onHom_iAdelic
    h_onHom_kAdelic _ h_det_M, pairWeil_apply, smul_smul, smul_smul, h_char]

/-! ### The Levi and radical laws -/

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- For the Levi element g = `New.Space.Splitting.levi` (m, g₀), which has gk = km and gι = ιg₀:
(ω_{aυ^p,b}(g,h)f)[x] = χ_T(det m)⁻¹ |det m|^(n′/2) ω_{a,b}(g₀,h) f[h⁻¹xm],
with f[x] = `New.Space.Splitting.homSlice` x f, n′ the rank of T and χ_T(y) = b(y/ȳ)υ(y)^(−n′). -/
lemma homSlice_levi (m : GL p (𝔸 E)) (g₀ : G E s₀) (h : G E s') (x : Matrix n' p (𝔸 E))
    (f : 𝒮 (V.hom T)) :
    D.homSlice T x (pairWeil V T (a * upsilonU1 ^ card p) b (D.levi (m, g₀), h) f) =
      (((b.spaceChar (card n')).val m.det).val⁻¹ * √(ideleAbs m.det) ^ card n') •
        pairWeil V₀ T a b (g₀, h) (D.homSlice T (h⁻¹.adeleMatrix * x * m.val) f) := by
  -- Move the pair past `ϱ` by `rho_pairWeil`, then past the zero term.
  -- The hole is the matrix form of `D.levi (m, g₀)`, which simp reaches by unfolding `levi`.
  simp [D.homSource_zeroTerm_pairWeil T a b _ g₀ m, homSlice, levi, Matrix.mul_assoc,
    rho_pairWeil, Matrix.mul_add, Matrix.add_mul]

/-- For the unipotent element u = `New.Space.Splitting.radicalElement` c z, which fixes k:
(ω_{a,b}(u,1)f)[x] = ψ(½ tr(z x*ε′x)) ϱ(x c* ε₀) f[x], where ε′, ε₀ are the standard forms of T
and V₀ and f[x] = `New.Space.Splitting.homSlice` x f. -/
lemma homSlice_radicalElement (c : Matrix n₀ p (𝔸 E)) (z : Matrix p p (𝔸 E)) (x : Matrix n' p (𝔸 E))
    (f : 𝒮 (V.hom T)) :
    D.homSlice T x (pairWeil V T a b (D.radicalElement c z, 1) f) =
      (stdAddChar E (toAdele (2⁻¹ : E) * (z * (xᴴ * stdForm E s' * x)).trace)).val •
        ϱ (V₀.hom T) (matrixToVec (x * cᴴ * stdForm E s₀)) (D.homSlice T x f) := by
  -- The radical element does not change the zero term, so the left side is the term at `0` of
  -- `ϱ (matrixToVec y) f` for the `y` below; the law `homSlice_rho` computes it.
  obtain ⟨h_kAdelic, h_iAdelic⟩ : D.ActsOnFrame (D.radicalElement c z) (1 : GL p (𝔸 E)).val ∧
      D.iCoord * ((D.radicalElement c z).adeleMatrix * D.iAdelic) = adeleMatrix (s := s₀) 1 := by
    simpa using D.exists_eq_radicalElement_iff.1 ⟨c, z, rfl⟩
  have h_zeroTerm_radicalElt (u : 𝒮 (V.hom T)) :
      (D.homSource T).zeroTerm (pairWeil V T a b (D.radicalElement c z, 1) u) =
        (D.homSource T).zeroTerm u := by
    rw [← div_mul_cancel a (upsilonU1 ^ card p), homSource_zeroTerm_pairWeil D T
      (a / upsilonU1 ^ card p) b (D.radicalElement c z) 1 1 h_kAdelic h_iAdelic]
    simp [Prod.mk_one_one]
  let y : Matrix n' n (𝔸 E) := x * D.kCoord * (D.radicalElement c z).adeleMatrix
  have h_sourceTerm_eq :
      D.homSlice T x (pairWeil V T a b (D.radicalElement c z, 1) f) =
        D.homSlice T 0 ((V.hom T).ϱ (matrixToVec y) f) := by
    simp [y, homSlice, rho_pairWeil, h_zeroTerm_radicalElt]
  -- After the law `homSlice_rho` the two sides differ only in the value of `stdAddChar E`.
  -- The matrix of `radicalElement c z` turns its argument into a term in `c` and terms in `z`,
  -- `zᴴ`. By `stdAddChar_inv_two_mul_add_star` the value depends only on `t + star t`. The term in
  -- `c` is `j` times a self-conjugate adele and drops out of this sum; the terms in `z` and `zᴴ`
  -- are conjugate.
  set X : Matrix p p (𝔸 E) := xᴴ * (stdForm E s' * x) with hX
  have h_char : stdAddChar E (toAdele (j / 2) *
        ((y * D.lAdelic)ᴴ * stdForm E s' * (0 + 0 + y * D.kAdelic)).trace) =
      stdAddChar E (toAdele (2⁻¹ : E) * (z * X).trace) := by
    rw [← stdAddChar_inv_two_mul_add_star, eq_comm, ← stdAddChar_inv_two_mul_add_star]
    congr 1
    simp [y, radicalElement, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
      Matrix.sub_mul, hX, ← trace_conjTranspose, trace_mul_comm cᴴ, (stdForm E _).trace_mul_comm,
      z.trace_mul_comm]
    grind
  rw [h_sourceTerm_eq, homSlice_rho, h_char]
  simp [y, radicalElement, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, ← hX]

end Splitting

end New.Space

end
