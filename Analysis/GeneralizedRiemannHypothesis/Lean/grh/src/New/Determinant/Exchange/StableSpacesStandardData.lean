import New.Determinant.Exchange.MatchingPartners

/-!
# Criteria for a function with a matched function to lie in a stable space; vanishing of lifts

Let χ be tame (`New.TameLocalChar`), and let P be a GL_n(F)-stable space of Schwartz–Bruhat
functions on n × b matrices. Let Ψ be a locally constant function that has a matched function
(`New.AreMatched`). The file gives two criteria for Ψ ∈ P in terms of the standard data
`New.stdColDatum χ s`, the function y ↦ χ⁻¹(det s y) for integral y with det s y a unit of O, and 0
otherwise.

## Main definitions and results

* `New.Exchange.match_mem_of_stdColDatum`: if P contains a standard datum multiplied by an ℕ-valued
  function that is non-zero at a suitable point, then Ψ ∈ P; the proof averages over GL_n(O).
* `New.Exchange.IntegralFrame.match_mem_of_isPrimitiveMatrix_vanishing`: if a space M contains the
  shears of a standard datum and P contains what certain functionals kill in M, then Ψ ∈ P; a Gauss
  sum of the shears lies in P, and `New.Exchange.match_mem_of_stdColDatum` applies to it.
* `New.Exchange.IsEquivariantLift.shearInvariant_stdColDatum`: the partial means
  (`New.Space.Splitting.partialMean`) of the coefficients of the image of the standard datum of the
  frame are invariant under the local shears along one more isotropic line.
* `New.Exchange.IsSelfDualTestPair`, `New.Space.Splitting.VanishesAtSelfDual`: the pairs of an index
  and a Levi component at which vanishing at self-dual lattices is tested, and that vanishing.
* `New.Exchange.IsEquivariantLift.apply_eq_zero_of_areMatched`: `𝒟` vanishes on every locally
  constant datum with a matched function, once the image of the standard datum of the frame vanishes
  at self-dual lattices.

Notions from other files:
* `New.SemilocalField`: Conditions met by a finite product of non-archimedean local fields: a
  locally compact ring with Haar measure, compact open subring O of volume one, a topologically
  nilpotent invertible ϖ in O, and `New.IsValuationPair O`.
* `New.schwartzBruhat`: The space of locally constant, compactly supported complex functions that
  vanish outside a given set.
* `New.HasIntegralConductor`: The additive character ψ is continuous and has conductor O: ψ is
  trivial on tO exactly when t lies in O.
* `New.Exchange.IntegralFrame.stdDatum`: For a function G, the function equal to G(x·(K I)) at
  integral x and 0 elsewhere, with K and I two of the column blocks K, I, L of the frame.
* `New.Space.Splitting.partialMean`: the mean of a Fourier coefficient over the shifts of one more
  isotropic vector; `New.Space.Splitting.ShearInvariant` is its invariance under local shears.
-/

/-! ## Stable spaces containing a standard datum -/

namespace New.Exchange

open Matrix MeasureTheory SemilocalField schwartzBruhat IsIntMatrix Finset Function

variable {F a b m n : Type} [V : SemilocalField F] [Fintype a] [Fintype b] [DecidableEq b]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] {χ : MulChar F ℂ}
  {P : Submodule ℂ (Matrix n b F → ℂ)} {Φ : Matrix a n F → ℂ} {Ψ : Matrix n b F → ℂ}
  [hχ : TameLocalChar χ] {e : b ⊕ a ≃ n} {U : Set (Matrix n b F)}

/-- Let χ be tame, let A be an integral frame (an integral basis of Fⁿ with column blocks L, K, I,
whose integral inverse has row blocks L', K', I'), and let σ order the n rows as L', K', I'. The row
datum `stdRowDatum σ χ A.dualL` sends x to χ⁻¹ of the determinant of the square matrix with rows L'
and x, ordered by σ, if that matrix is in GL_n(O), and to 0 otherwise. It equals c · χ⁻¹(det x (K
I)) at integral x with det x (K I) a unit of O, and 0 elsewhere, for a constant c of modulus 1. -/
lemma IntegralFrame.exists_stdRowDatum_eq_stdDatum (A : IntegralFrame F n m b) (σ : b ⊕ b ⊕ m ≃ n) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ stdRowDatum σ χ A.dualL =
      A.stdDatum fun x : Matrix (b ⊕ m) (b ⊕ m) F ↦ c * invOnUnits χ x.det := by
  classical
  -- Multiply `(dualL; x)` by the integral basis `P = (L K I)`, of unit determinant: the product is
  -- block triangular with diagonal blocks `1` and `x * (K I)`. The constant is `χ (det P)`.
  obtain ⟨hL', hI', hK, hL, hK', hI, hK'K, hI'K, hL'K, hK'I, hI'I, hL'I, hK'L, hI'L, hL'L⟩ :=
    A.blockRelations
  let P : Matrix n n F := (A.L.fromCols (A.K.fromCols A.I)).submatrix id σ.symm
  let Q : Matrix n n F := (A.dualL.fromRows (A.dualK.fromRows A.dualI)).submatrix σ.symm id
  have hP : IsIntMatrix O P := fun i ↦ σ.surjective.forall.2 (by simp [P, hL i, hK i, hI i])
  have hQ : IsIntMatrix O Q := σ.surjective.forall.2 (by simpa [Q] using ⟨hL', hK', hI'⟩)
  have hQP : Q * P = 1 := by simp [P, Q, ↓fromRows_mul_fromCols, ← submatrix_mul, *]
  have h_unit : IsIntegralUnit P.det :=
    (isPrimitiveMatrix_iff_int_and_unit_det.1 ⟨hP, Q, hQ, hQP⟩).2
  refine ⟨χ P.det, hχ.norm_eq_one h_unit, funext fun x ↦ if_congr ?_ ?_ rfl⟩
  · -- the square matrix with rows `dualL` and `x` is integral exactly when `x` is
    exact σ.surjective.forall.trans (by simp [IsIntMatrix, hL' _])
  · -- its determinant times `det P` is `det (x * (K I))`
    rw [invOnUnits_eq_mul_of_unit h_unit]
    simp [P, hL'K, hL'I, hL'L, ↓fromRows_mul_fromCols, ← det_mul, ← submatrix_mul]

/-- Let χ be tame (χ⁻¹ on the units of O is a primitive character of the finite ring O/ϖO) and let Ψ
be locally constant with a matched function Φ for χ over O (`AreMatched`: for k in GL_n(O), Φ at the
rows a of k⁻¹ is χ(det k) times Ψ at the columns b of k, in the order e, and both vanish
elsewhere). Then for some c, the function Ψ is invariant under translation by ϖ ^ c times integral
matrices. -/
lemma exists_pow_smul_add_eq (hΨ : IsLocallyConstant Ψ) (hΦΨ : AreMatched V.O e χ Φ Ψ) :
    ∃ c : ℕ, ∀ t : Matrix n b F, IsIntMatrix O t →
      ∀ y : Matrix n b F, Ψ (V.ϖ ^ c • t + y) = Ψ y := by
  classical
  -- `Ψ` is locally constant with compact support, so the `t` that fix it form an open set. It
  -- contains `0`; the integral matrices are compact and `ϖ ^ c` tends to `0`.
  obtain ⟨-, hΨ_mem, -⟩ := mem_sameSectionPairs_iff.1 (hΦΨ.mem_sameSectionPairs hχ hΨ)
  have h_translate : IsLocallyConstant fun t y : Matrix n b F ↦ Ψ (t + y) :=
    isLocallyConstant_curry hΨ_mem (· + ·) (-· + ·) neg_add_cancel_left
  have h_maps : ∀ᶠ c : ℕ in .atTop, Set.MapsTo (V.ϖ.1 ^ c • ContinuousMap.id (Matrix n b F))
      (SetLike.coe V.O).matrix {t | (fun y ↦ Ψ (t + y)) = Ψ} :=
    (V.isTopologicallyNilpotent_ϖ.smul_const (.id _)).eventually <| ContinuousMap.eventually_mapsTo
      isCompact_O.matrix (h_translate.isOpen_fiber Ψ) (by simp_intro _ _)
  exact h_maps.exists.imp fun c hc t ht ↦ congrFun (hc ht)

/-- Let χ be tame (χ⁻¹ on the units of O is a primitive character of the finite ring O/ϖO), let Φ be
a matched function of Ψ for χ over O (`AreMatched`: Φ at the rows a of k⁻¹ is χ(det k) times Ψ at
the columns b of k, for k in GL_n(O), the n indices being split as b ⊕ a by e, and both vanish
elsewhere), and let p = r · `stdColDatum χ s` with r an ℕ-valued function and s an integral matrix;
the standard datum `stdColDatum χ s` is χ⁻¹(det s y) at integral y with det s y a unit of O, and 0
elsewhere. Let x be integral with s x = 1, let Ψ be invariant under translation by ϖ ^ c times
integral matrices, and let d = ϖ ^ (-c) (1 - x (s - ϖ ^ c s)). Then Ψ(k⁻¹ x) p(d k y) =
|p(d k y)| Ψ(y) for k in GL_n(O). -/
lemma match_mul_stdColDatum_translate (hΦΨ : AreMatched V.O e χ Φ Ψ) {p : Matrix n b F → ℂ}
    {x : Matrix n b F} {s : Matrix b n F} (hx : IsIntMatrix O x) (hs : IsIntMatrix O s)
    (hsx : s * x = 1) {r : Matrix n b F → ℕ}
    (hp_eq : ∀ y : Matrix n b F, p y = r y • stdColDatum χ s y) {c : ℕ}
    (hc : ∀ t : Matrix n b F, IsIntMatrix O t → ∀ y : Matrix n b F, Ψ (V.ϖ ^ c • t + y) = Ψ y)
    {d : GL n F} (hd : d.val = (V.ϖ ^ c)⁻¹ • (1 - x * (s - V.ϖ ^ c • s)))
    (k : intGL n V.O) (y : Matrix n b F) :
    Ψ ((↑k⁻¹ : GL n F).val * x) * p ((d * k : GL n F).val * y) =
      ‖p ((d * k : GL n F).val * y)‖ * Ψ y := by
  classical
  set z : Matrix n b F := (d * k : GL n F).val * y with hz
  set k' : Matrix n n F := (↑k⁻¹ : GL n F).val with hk'
  by_cases h_zero : stdColDatum χ s z = 0
  · simp [hp_eq, h_zero]
  obtain ⟨hz_int : IsIntMatrix O z, h_prim : IsPrimitiveMatrix O (s * z)⟩ :=
    isIntMatrix_of_stdColDatum_ne_zero hs h_zero
  obtain ⟨g, hg : g ∈ intGL b O, hg_eq : g.val = s * z⟩ := isPrimitiveMatrix_iff.1 h_prim
  have h_unit : IsIntegralUnit g.val.det :=
    (isPrimitiveMatrix_iff_int_and_unit_det.1 ((isPrimitiveMatrix_iff_mem_intGL g).2 hg)).2
  -- `y` is congruent to `k⁻¹ * x * g` mod `ϖ ^ c`, where `g = s * z`, so `Ψ` agrees on the two.
  have h_congr : V.ϖ ^ c • (k' * (z - x * g.val)) + k' * x * g.val = y := by
    simp [hd, hz, hk', hg_eq, hsx, smul_sub, ← Matrix.mul_assoc, sub_sub, Matrix.mul_sub,
      Matrix.sub_mul]
  have h_int : IsIntMatrix O (k' * (z - x * g.val)) :=
    k⁻¹.prop.isIntMatrix.mul (hz_int.sub (hx.mul hg.isIntMatrix))
  have hΨy : Ψ (k' * x) = Ψ y * χ g.val.det := by
    rw [← h_congr, hc _ h_int, hΦΨ.right_mul _ hg]
  have h_value : p z = r z * (χ g.val.det)⁻¹ := by
    rw [hp_eq, stdColDatum, ite_eq_left hz_int, ← hg_eq, invOnUnits, ite_eq_left h_unit,
      nsmul_eq_mul]
  have h_norm : ‖χ g.val.det‖ = 1 := hχ.norm_eq_one h_unit
  have h_ne : χ g.val.det ≠ 0 := by simp [← norm_ne_zero_iff, h_norm]
  rw [hΨy, h_value]
  simp [h_norm, field]

/-- Let χ be tame and let P be a GL_n(F)-stable space of functions on n × b matrices that are
locally constant, compactly supported and zero outside a set U. Suppose that P contains
p = r · `stdColDatum χ s`, where `stdColDatum χ s` is the standard datum of the integral matrix s
(χ⁻¹(det s y) at integral y with det s y a unit of O, 0 elsewhere), and r is an ℕ-valued function
with r(x) ≠ 0 at an integral x with s x = 1. Then P contains every locally constant Ψ that has a
matched function Φ for χ over O (with the n indices split as b ⊕ a by e, Φ at the rows a of k⁻¹ is
χ(det k) times Ψ at the columns b of k, for k in GL_n(O), and both vanish elsewhere). -/
lemma match_mem_of_stdColDatum
    (hP_stable : ∀ g : GL n F, ∀ f ∈ P, (fun y : Matrix n b F ↦ f (g.val * y)) ∈ P)
    (hP_le : P ≤ schwartzBruhat U) (hΨ : IsLocallyConstant Ψ) (hΦΨ : AreMatched V.O e χ Φ Ψ)
    {p : Matrix n b F → ℂ} {x : Matrix n b F} {s : Matrix b n F} (hp : p ∈ P)
    (hx : IsIntMatrix O x) (hs : IsIntMatrix O s) (hsx : s * x = 1) (r : Matrix n b F → ℕ)
    (hp_eq : ∀ y : Matrix n b F, p y = r y • stdColDatum χ s y) (hr : r x ≠ 0) : Ψ ∈ P := by
  classical
  -- Average the translates `p (d * k * ·)` over `k` in `intGL n O` with weights `Ψ (k⁻¹ * x)`. Here
  -- `d` fixes `x` and expands the kernel of `s` by `ϖ ^ (-c)`, where `Ψ` is invariant mod `ϖ ^ c`.
  -- The average lies in `P` and is a positive multiple of `Ψ`.
  obtain ⟨c, hc⟩ := exists_pow_smul_add_eq hΨ hΦΨ
  obtain ⟨d, hd⟩ : ∃ d : GL n F, d.val = (V.ϖ ^ c)⁻¹ • (1 - x * (s - V.ϖ ^ c • s)) :=
    ⟨(V.ϖ ^ c)⁻¹ • GeneralLinearGroup.mk'' (1 - x * (s - V.ϖ ^ c • s))
      (by simp [↓det_one_sub_mul_comm x, hsx, Matrix.sub_mul]), rfl⟩
  have : CompactSpace (intGL n V.O) := isCompact_iff_compactSpace.1 (isCompact_intGL isCompact_O)
  have h_translates :
      IsLocallyConstant fun (k : intGL n V.O) (y : Matrix n b F) ↦ p ((d * k : GL n F).val * y) :=
    isLocallyConstant_curry (hP_le hp) (fun (k : intGL n V.O) y ↦ d.val * (k : GL n F).val * y)
      (fun k y ↦ (k : GL n F).inv * d.inv * y) (fun k y ↦ by simp [Matrix.mul_assoc])
  -- The integral `I y` of `‖p (d * k * y)‖` over `k` is constant where `Ψ y ≠ 0`: these `y` are in
  -- the orbit of `x`.
  let I (y : Matrix n b F) : ℝ := ∫ k : intGL n V.O, ‖p ((d * k : GL n F).val * y)‖ ∂.haar
  have h_orbit (y : Matrix n b F) (hy : Ψ y ≠ 0) : I y = I x := by
    obtain ⟨l, hl, rfl⟩ := hΦΨ.supp_right y hy
    -- `x` is integral with an integral left inverse, so it is a column block of some `j` too.
    obtain ⟨j, hj, rfl⟩ := (isValuationPair.exists_firstCols_iff e).2 ⟨hx, s, hs, hsx⟩
    -- Substitute `k * (j / l)` for `k`: the Haar measure is right invariant.
    let q : intGL n V.O := ⟨j / l, div_mem hj hl⟩
    calc I (firstCols e l)
        = ∫ k : intGL n V.O, ‖p ((d * ↑(k * q) : GL n F).val * firstCols e l)‖ ∂.haar :=
          (integral_mul_right_eq_self _ _).symm
      _ = I (firstCols e j) := by simp [I, q, mul_firstCols, Matrix.mul_assoc]
  have h_one : p ((d * (1 : intGL n V.O) : GL n F).val * x) ≠ 0 := by
    -- the value is `r x`, as `d * x = x` and `s * x = 1`
    simp [hd, hp_eq, hsx, hx, hr, invOnUnits, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      stdColDatum]
  have h_pos : 0 < I x :=
    (h_translates.comp fun f ↦ ‖f x‖).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (.of_compactSpace _) (fun _ ↦ norm_nonneg _) (norm_ne_zero_iff.2 h_one)
  -- The weighted translate is a nonnegative multiple of `Ψ`, point by point.
  have key_eq (k : intGL n V.O) (y : Matrix n b F) :
      Ψ ((↑k⁻¹ : GL n F).val * x) * p ((d * k : GL n F).val * y) =
        ‖p ((d * k : GL n F).val * y)‖ * Ψ y :=
    match_mul_stdColDatum_translate hΦΨ hx hs hsx hp_eq hc hd k y
  have h_mem (k : intGL n V.O) : (fun y ↦ ‖p ((d * k : GL n F).val * y)‖ * Ψ y) ∈ P := by
    simpa only [← key_eq, Pi.smul_def, smul_eq_mul] using P.smul_mem _ (hP_stable (d * k) p hp)
  -- The average over `k` equals `I x • Ψ` and lies in `P`.
  have h_eq : (fun y ↦ ∫ k : intGL n V.O, (‖p ((d * k : GL n F).val * y)‖ * Ψ y : ℂ) ∂.haar) =
      I x • Ψ := by
    funext y
    rw [integral_mul_const, integral_complex_ofReal]
    obtain hy | hy := eq_or_ne (Ψ y) 0
    · simp [hy]
    · rw [Pi.smul_apply, ← h_orbit y hy, Complex.real_smul]
  rw [← P.smul_mem_iff h_pos.ne', ← h_eq]
  exact integral_mem_of_isLocallyConstant .haar
    (h_translates.comp fun f y ↦ (‖f y‖ * Ψ y : ℂ)) h_mem

omit [TameLocalChar χ] in
/-- An integral frame A is an integral n × n basis cut into column blocks K, I, L (K and L are
n × b), with integral inverse cut into row blocks K', I', L'; thus K' K = L' L = 1 and
K' L = L' K = 0. The shear y ↦ y + L z K' y by an integral z fixes the standard datum of K', which
is χ⁻¹(det K' y) at integral y with det K' y a unit of O, and 0 elsewhere. -/
lemma IntegralFrame.stdColDatum_shear_of_isIntMatrix (A : IntegralFrame F n m b)
    {z : Matrix b b F} (hz : IsIntMatrix O z) :
    (fun y : Matrix n b F ↦ stdColDatum χ A.dualK (y + A.L * z * (A.dualK * y))) =
      stdColDatum χ A.dualK := by
  classical
  have h_blocks := A.blockRelations
  funext y
  -- `dualK` does not see the shear, as `dualK * L = 0`, and the added term is integral when
  -- `dualK * y` is.
  have hK'y : A.dualK * (y + A.L * z * (A.dualK * y)) = A.dualK * y := by
    simp [Matrix.mul_add, ← Matrix.mul_assoc, h_blocks.dualK_mul_L]
  have h_add (v : Matrix n b F) (hv : IsIntMatrix O v) : IsIntMatrix O (A.L * z * (A.dualK * v)) :=
    (h_blocks.isIntMatrix_L.mul hz).mul (h_blocks.isIntMatrix_dualK.mul hv)
  have h_int : IsIntMatrix O (y + A.L * z * (A.dualK * y)) ↔ IsIntMatrix O y :=
    ⟨fun hy ↦ by simpa [hK'y] using hy.sub (h_add _ hy), fun hy ↦ hy.add (h_add y hy)⟩
  simp only [stdColDatum, hK'y]
  exact if_congr h_int rfl rfl

/-- Let π : O → R be a homomorphism to a finite ring, η a primitive character of R, φ a primitive
additive character of R with φ(π x) = ψ(ϖ⁻¹ x), and l a section of the reduction of matrices by π.
If η vanishes at the determinant of the reduction of T, then the sum over b × b matrices r over R of
η(det r) ψ(ϖ⁻¹ trace(T l(r))) is zero. -/
lemma sum_mul_addChar_lift_eq_zero {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {π : V.O →+* R} {η : MulChar R ℂ} (h_prim : IsPrimitiveMulChar η)
    {φ : AddChar R ℂ} (hφ : φ.IsPrimitive) {ψ : AddChar F ℂ}
    (hφπ : ∀ x : V.O, φ (π x) = ψ (V.ϖ⁻¹.1 * x)) {l : Matrix b b R → Matrix b b V.O}
    (hl : ∀ r : Matrix b b R, (l r).map π = r) {T : Matrix b b V.O}
    (h_det : η (T.map π).det = 0) :
    ∑ r : Matrix b b R, η r.det * ψ (↑V.ϖ⁻¹ * (T.map Subtype.val * (l r).map Subtype.val).trace) =
      0 := by
  obtain ⟨γ, -, h_fourier⟩ := exists_matrixFourier_eq_mul_inv_det (a := b) hφ h_prim
  calc
    _ = matrixFourier φ (fun r ↦ η r.det) (T.map π) := by
      refine sum_congr rfl fun r _ ↦ congrArg _ ?_
      -- the pairing of `T` with the lift of `r` reduces to that of `T.map π` with `r`
      simpa [trace, mul_apply, ← congrFun₂ (hl r)] using (hφπ (T * l r).trace).symm
    -- The transform at `T.map π` is a constant times `η⁻¹ (det (T.map π))`.
    _ = 0 := by simp [h_fourier _, MulChar.inv_apply_eq_inv', h_det]

/-- For tame χ with reduction π and residue character η, and a matrix N over O, the value of χ⁻¹,
cut off to the units of O, at det N is η(det π(N)). -/
lemma invOnUnits_det_eq_resChar_det (N : Matrix b b V.O) :
    invOnUnits χ (N.map Subtype.val).det = hχ.resChar (N.map hχ.reduction).det := by
  simpa [RingHom.map_det, ← V.O.subtype_apply, -Subring.subtype_apply] using
    hχ.isPrimitive_resChar_and_invOnUnits_eq.right N.det

/-- Let χ be tame: there are a reduction π of O onto a finite ring with kernel ϖO and a primitive
character η of that ring with η ∘ π equal to χ⁻¹ on units and 0 on the rest of O. Let A be an
integral frame (an integral basis with column blocks K, I, L, whose integral inverse has row blocks
K', I', L'), so that L' L = 1 and K' L = 0. The standard datum `stdColDatum χ s` of a matrix s is
χ⁻¹(det s y) at integral y with det s y a unit of O, and 0 elsewhere. For r over O and x integral,
the standard datum of L' at L r K' x - ϖ x is η(det π(r)) times the standard datum of K' at x. -/
lemma IntegralFrame.stdColDatum_mul_sub_smul (A : IntegralFrame F n m b) (r : Matrix b b V.O)
    {x : Matrix n b F} (hx : IsIntMatrix O x) :
    stdColDatum χ A.dualL (A.L * (r.map Subtype.val * (A.dualK * x)) - V.ϖ.1 • x) =
      hχ.resChar (r.map hχ.reduction).det * stdColDatum χ A.dualK x := by
  have h_blocks := A.blockRelations
  set y : Matrix n b F := A.L * (r.map Subtype.val * (A.dualK * x)) - V.ϖ.1 • x with hy
  have hy_int : IsIntMatrix O y :=
    (h_blocks.isIntMatrix_L.mul
      (.mul (fun i j ↦ (r i j).2) (h_blocks.isIntMatrix_dualK.mul hx))).sub (hx.smul ϖ_mem)
  -- With `k`, `u` the lifts of `A.dualK * x`, `A.dualL * x` to `O`, `A.dualL * y` is
  -- `r * k - ϖ • u`.
  obtain ⟨k, hk⟩ : ∃ k : Matrix b b V.O, k.map Subtype.val = A.dualK * x :=
    ⟨of fun i j ↦ ⟨(A.dualK * x) i j, h_blocks.isIntMatrix_dualK.mul hx i j⟩, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Matrix b b V.O, u.map Subtype.val = A.dualL * x :=
    ⟨of fun i j ↦ ⟨(A.dualL * x) i j, h_blocks.isIntMatrix_dualL.mul hx i j⟩, rfl⟩
  let N : Matrix b b V.O := r * k - (⟨V.ϖ.1, ϖ_mem⟩ : V.O) • u
  have hN : A.dualL * y = N.map Subtype.val := by
    simp [N, hy, ← Matrix.mul_assoc, h_blocks.dualL_mul_L, ← hk, ← hu, ← Matrix.ext_iff, mul_apply,
      Matrix.mul_sub]
  have hϖ : hχ.reduction ⟨V.ϖ.1, ϖ_mem⟩ = 0 :=
    (hχ.reduction_surjective_and_eq_zero_iff.right _).2 (by simp)
  have hN_red : N.map hχ.reduction = r.map hχ.reduction * k.map hχ.reduction := by
    simp [N, Matrix.map_sub, Matrix.map_smul', hϖ]
  calc stdColDatum χ A.dualL y = hχ.resChar (N.map hχ.reduction).det := by
        simp [hy_int, hN, invOnUnits_det_eq_resChar_det, stdColDatum]
    _ = hχ.resChar (r.map hχ.reduction).det * stdColDatum χ A.dualK x := by
        simp [hx, ← hk, invOnUnits_det_eq_resChar_det, hN_red, stdColDatum]

/-- Let χ be tame, let ψ have conductor O, and let P be a GL_n(F)-stable space of locally constant,
compactly supported functions on n × b matrices that vanish outside a set U. The standard datum of
K' is the function S₀(y) = χ⁻¹(det K' y) at integral y with det K' y a unit of O, 0 elsewhere, and S
z is its shear y ↦ S₀(y + L z K' y), with L a block of the integral frame A and K' a block of its
inverse. Let M be a space of functions that contains all S z (`h_shear_mem`). Suppose that P
contains every f ∈ M with Λ f = 0 for all matrices T and functionals Λ such that Λ(S z) = ψ(tr T z)
Λ(S₀) for all z, and Λ(S₀) = 0 in case T is primitive, that is, integral with an integral left
inverse; for the square matrix T this means T ∈ GL_b(O) (`h_kill`). Then P contains every locally
constant Ψ that has a matched function Φ for χ over O. -/
lemma IntegralFrame.match_mem_of_isPrimitiveMatrix_vanishing
    (hP_stable : ∀ g : GL n F, ∀ f ∈ P, (fun y : Matrix n b F ↦ f (g.val * y)) ∈ P)
    (hP_le : P ≤ schwartzBruhat U) (hΨ : IsLocallyConstant Ψ) (hΦΨ : AreMatched V.O e χ Φ Ψ)
    (A : IntegralFrame F n m b) {ψ : AddChar F ℂ} {M : Submodule ℂ (Matrix n b F → ℂ)}
    (hψ : HasIntegralConductor ψ)
    (h_shear_mem : ∀ z : Matrix b b F,
      (fun y : Matrix n b F ↦ stdColDatum χ A.dualK (y + A.L * z * (A.dualK * y))) ∈ M)
    (h_kill : ∀ f ∈ M, (∀ (T : Matrix b b F) (Λ : (Matrix n b F → ℂ) →ₗ[ℂ] ℂ),
      (∀ z : Matrix b b F, Λ (fun y : Matrix n b F ↦
        stdColDatum χ A.dualK (y + A.L * z * (A.dualK * y))) =
        ψ (T * z).trace • Λ (stdColDatum χ A.dualK)) →
      (IsPrimitiveMatrix O T → Λ (stdColDatum χ A.dualK) = 0) → Λ f = 0) → f ∈ P) :
    Ψ ∈ P := by
  classical
  -- Sum the `S z` over `z = ϖ⁻¹ r`, `r` a matrix over the residue ring (lifted to `O`), against
  -- `η (det r)`. The functionals `Λ` kill this sum (a Gauss sum that vanishes off the units), so
  -- it lies in `P`. Its value at `-ϖ⁻¹ • y` is `stdColDatum χ A.dualL y` times the number of terms
  -- that do not vanish there; that number is not zero for `y = A.L - ϖ • A.K`, so
  -- `match_mem_of_stdColDatum` applies.
  let S (z : Matrix b b F) (y : Matrix n b F) : ℂ :=
    stdColDatum χ A.dualK (y + A.L * z * (A.dualK * y))
  -- `π : O → R` is the residue map, and `η ∘ π` is `χ⁻¹` on units and zero elsewhere.
  let R : Type := hχ.ResidueRing
  let π : V.O →+* R := hχ.reduction
  let η : MulChar R ℂ := hχ.resChar
  have h_surj : Surjective π := hχ.reduction_surjective_and_eq_zero_iff.left
  have : Fintype R := Fintype.ofFinite R
  obtain ⟨hL', -, hK, hL, -, -, hK'K, -, hL'K, -, -, -, hK'L, -, hL'L⟩ := A.blockRelations
  -- `x ↦ ψ (ϖ⁻¹ x)` descends to a primitive character `φ` of the residue ring.
  obtain ⟨φ, hφ, hφπ⟩ : ∃ φ : AddChar R ℂ, φ.IsPrimitive ∧ ∀ x : V.O, φ (π x) = ψ (V.ϖ⁻¹.1 * x) :=
    exists_primitive_residue_addChar hχ.reduction_surjective_and_eq_zero_iff hψ.right
  -- `l r` is a lift of `r` to `O`, with `l 1 = 1`.
  let l (r : Matrix b b R) : Matrix b b V.O := if r = 1 then 1 else r.map (surjInv h_surj)
  have hl (r : Matrix b b R) : (l r).map π = r := by
    ext i j
    by_cases hr : r = 1 <;> simp [l, hr, one_apply, apply_ite π, surjInv_eq h_surj]
  let f (r : Matrix b b R) : Matrix n b F → ℂ := η r.det • S (V.ϖ.inv • (l r).map Subtype.val)
  have h_avg : ∑ r, f r ∈ P := by
    refine h_kill _ (sum_mem fun r _ ↦ M.smul_mem _ (h_shear_mem _)) ?_
    intro T Λ (hΛ : ∀ z : Matrix b b F, Λ (S z) = ψ (T * z).trace • Λ (stdColDatum χ A.dualK))
      h_unit
    by_contra h_ne
    obtain ⟨h_sum, h_std⟩ : ∑ r, η r.det * ψ (↑V.ϖ⁻¹ * (T * (l r).map Subtype.val).trace) ≠ 0 ∧
        Λ (stdColDatum χ A.dualK) ≠ 0 := by
      simpa [f, hΛ, ← mul_assoc, ← sum_mul] using h_ne
    -- `T` is integral, because `S z` is the standard datum itself for integral `z`.
    have hT : IsIntMatrix O T := by
      refine fun i j ↦ (hψ.2 (T i j)).1 fun a ha ↦ ?_
      have h_single : IsIntMatrix O (single j i a) := fun _ _ ↦ by simp [single_apply, ite_mem, ha]
      simpa [S, A.stdColDatum_shear_of_isIntMatrix h_single, h_std, trace_mul_single] using
        hΛ (single j i a)
    obtain ⟨T₀, rfl⟩ : ∃ T₀ : Matrix b b V.O, T₀.map Subtype.val = T :=
      ⟨of fun i j ↦ ⟨T i j, hT i j⟩, rfl⟩
    -- `T` is not unimodular, so the Gauss sum of index `T` is zero.
    have h_det : η (T₀.map π).det = 0 := by
      rw [← invOnUnits_det_eq_resChar_det, invOnUnits,
        ite_eq_right fun h ↦ h_std (h_unit (isPrimitiveMatrix_iff_int_and_unit_det.2 ⟨hT, h⟩))]
    exact h_sum (sum_mul_addChar_lift_eq_zero hχ.isPrimitive_resChar_and_invOnUnits_eq.left hφ hφπ
      hl h_det)
  let g : GL n F := -V.ϖ⁻¹ • 1
  -- Every nonzero term of the sum at `g * y` equals `stdColDatum χ A.dualL y`.
  have h_term (y : Matrix n b F) (r : Matrix b b R) (hr : f r (g.1 * y) ≠ 0) :
      f r (g.1 * y) = stdColDatum χ A.dualL y := by
    let x : Matrix n b F := g.1 * y + A.L * (V.ϖ.inv • (l r).map Subtype.val) *
      (A.dualK * (g.1 * y))
    have hx_int : IsIntMatrix O x := (ite_ne_right_iff.1 (right_ne_zero_of_mul hr)).1
    -- `A.dualK * x = A.dualK * (g * y)` as `A.dualK * A.L = 0`; solve the definition of `x` for
    -- `y`.
    have hy : y = A.L * ((l r).map Subtype.val * (A.dualK * x)) - V.ϖ.1 • x := by
      simp [x, g, ← Matrix.mul_assoc, hK'L, Units.smul_def, smul_smul, Matrix.mul_add]
    calc f r (g.1 * y) = η r.det * stdColDatum χ A.dualK x := rfl
      _ = stdColDatum χ A.dualL y := by rw [hy, A.stdColDatum_mul_sub_smul (l r) hx_int, hl]
  -- The sum translated by `g` is a multiple of `stdColDatum χ A.dualL`, non-zero at
  -- `A.L - ϖ • A.K`.
  have h_ne_one : f 1 (g.1 * (A.L - V.ϖ.1 • A.K)) ≠ 0 := by
    -- the term `r = 1` is `stdColDatum χ A.dualK A.K = 1` there
    simp [f, g, l, ← Units.smul_def, S, invOnUnits, hK, hK'K, hK'L, stdColDatum,
      Matrix.mul_add, Matrix.mul_sub]
  refine match_mem_of_stdColDatum hP_stable hP_le hΨ hΦΨ (hP_stable g _ h_avg)
    (hL.sub (hK.smul ϖ_mem)) hL'
    (by simp [hL'K, hL'L, Matrix.mul_sub]) (fun y ↦ #{r | f r (g.1 * y) ≠ 0}) (fun y ↦ ?_)
    (card_ne_zero.2 ⟨1, by simpa using h_ne_one⟩)
  rw [Finset.sum_apply, ← sum_filter_ne_zero]
  exact sum_eq_card_nsmul (by simpa using h_term y)

end New.Exchange

/-!
## Vanishing of an equivariant lift on the data with a matched function

`New.Exchange.IsEquivariantLift` says that `𝒟` maps local data at the places `𝔠.ramifiedPlaces`
equivariantly to automorphic functions. `New.Space.Splitting.centreCoeff` is the Fourier coefficient
along the centre of the unipotent radical of the parabolic subgroup attached to a splitting
`New.Space.Splitting`. The standard datum of the frame of a splitting `D` is `New.stdColDatum` of
the dual block `dualL` of `adaptedFrame 𝔠.readsAt D`.
-/

section StandardCoefficients

open Matrix Prod New Exchange SemilocalField G Space Splitting Gf RingHom WeilData

/-- Let `𝒟` be an equivariant lift on `M`: a linear map from functions of `m × b` matrices over the
completions at the ramified places `S = 𝔠.ramifiedPlaces` of the character `𝔠` to functions on
`U(X)` which, on the space `M` of locally constant compactly supported such functions, has
automorphic values, turns translation by the group at `S` into right translation up to a character
of the determinant, and has values right invariant under the standard level away from `S`. Let `D`
split `X` as `W₁` plus hyperbolic planes along `b` lines and be adapted (its adelic frame is
orthonormal at infinity and integral at the finite places; `adaptedFrame 𝔠.readsAt D` is this frame
read in the completions at `S`). Let `O` be the product of the rings of integers at `S`, and let
`Ψ₀ ∈ M` be the standard datum of the dual block `dualL` of that frame, the function
`y ↦ χ⁻¹(det (dualL y))` at integral `y` where this determinant is a unit, 0 elsewhere, with
`χ = 𝔠.semilocalChar`. Suppose that the Fourier coefficient `D.centreCoeff T` of `𝒟 Ψ₀` along the
centre of the unipotent radical of the parabolic of `D`, at a skew-hermitian index `T`, vanishes at
every point `(1, g)`, with `g` trivial at `S`, whenever `(invDifferentIdele E)⁻¹ • T` lies in
`GL_b(O)` at `S`. Then `𝒟` kills every locally constant datum `Ψ` that has a matched function
`Φ`. -/
lemma New.Exchange.IsEquivariantLift.apply_eq_zero_of_centreCoeff_eq_zero
    {E : Type} [Field E] [CMType E] [H : WeilData E] {n b m : Type}
    [Fintype n] [DecidableEq n] [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
    {s : n → ℤˣ} {r : m → ℤˣ} {μ : NumberField.InfinitePlace E → ℤ} {𝔠 : SplitTameChar E μ}
    {X : Space E m r} {W₁ : Space E n s}
    {M : Submodule ℂ (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ)}
    {𝒟 : (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E r → ℂ}
    (h_lift : IsEquivariantLift 𝔠 X M 𝒟) (D : X.Splitting W₁ b) [IsBaseAdapted D]
    (h_frame : stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL ∈ M)
    {p : Type} [Fintype p] {σ : b ⊕ p ≃ m} {Φ : Matrix p m (LocProd 𝔠.ramifiedPlaces) → ℂ}
    {Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hΨ : IsLocallyConstant Ψ) (hΦΨ : AreMatched O σ 𝔠.semilocalChar Φ Ψ)
    (h_coeff : ∀ T : Matrix b b E, Tᴴ = -T →
      IsPrimitiveMatrix O (((invDifferentIdele E)⁻¹.val • T.map toAdele).map (componentsAt 𝔠)) →
      ∀ g ∈ Gf.trivialOn m 𝔠.ramifiedPlaces,
        D.centreCoeff T (𝒟 (stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL)) (1, g) =
          0) :
    𝒟 Ψ = 0 := by
  -- Apply `IntegralFrame.match_mem_of_isPrimitiveMatrix_vanishing` to `M ⊓ ker 𝒟`. Its functionals
  -- are the coefficients: `Λ T x` agrees on `M` with the `T`-th coefficient of `𝒟` at `x`, and a
  -- shear along the frame at `x` multiplies it by a value of the additive character.
  choose Λ hΛ using h_lift.exists_linear_centreCoeff D
  let Ψ₀ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ :=
    stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL
  let τ (T : Matrix b b E) : Matrix b b (LocProd 𝔠.ramifiedPlaces) :=
    ((invDifferentIdele E)⁻¹.val • T.map toAdele).map (componentsAt 𝔠)
  have hΛ_eq (T : Matrix b b E) (x : G E r) {f : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hf : f ∈ M) :
      Λ T x f = D.centreCoeff T (𝒟 f) x := (hΛ T x f hf).1
  have hΛ_shear (T : Matrix b b E) (x : G E r) (w : Matrix b b (LocProd 𝔠.ramifiedPlaces)) :
      let Ψ' (y : Matrix m b (LocProd 𝔠.ramifiedPlaces)) : ℂ :=
        Ψ₀ (y + (x⁻¹.adeleMatrix * D.kAdelic).map
        (componentsAt 𝔠) * w * ((D.lCoord * x.adeleMatrix).map (componentsAt 𝔠) * y))
      Ψ' ∈ M ∧ Λ T x Ψ' = 𝔠.readsAt.ψ (τ T * w).trace • Λ T x Ψ₀ := (hΛ T x _ h_frame).2 w
  refine ((adaptedFrame 𝔠.readsAt D.symm).match_mem_of_isPrimitiveMatrix_vanishing
    h_lift.comp_mul_mem_ker (fun _ hf ↦ h_lift.le_schwartzBruhat hf.1) hΨ hΦΨ
    𝔠.readsAt.hasIntegralConductor_psi (M := M) (fun w ↦ ?_) (fun f hf h_kill ↦ ⟨hf, ?_⟩)).2
  · -- The shears of the standard datum lie in `M`. The frame of `D.symm` is that of `D` with its
    -- two isotropic parts exchanged.
    simpa [Ψ₀] using! (hΛ_shear 0 1 w).1
  -- By weak approximation it suffices that `𝒟 f` vanishes at `(1, g)`, `g` trivial at
  -- `𝔠.ramifiedPlaces`, and for that, that its coefficients vanish there.
  obtain ⟨h_cont, h_left⟩ := h_lift.isAutFunction hf
  refine funext ((X.weak_approximation 𝔠.ramifiedPlaces.finite_toSet).eq (fun ⟨γ, g, hg⟩ ↦ ?_)
    h_cont)
  suffices h_centre : 𝒟 f (D.radicalCentre 0 * (1, g)) = 0 by simpa [h_left] using h_centre
  refine IsDualFamily.eq_zero_of_quotMean_mul_eq_zero
    (D.isContPeriodic_radicalCentre ⟨h_cont, h_left⟩ (1, g))
    (fun T h_per ↦ ?_) 0
  -- Hermitian matrices are periods of `D.radicalCentre`, so only skew-hermitian `T` are to be
  -- tested.
  have hT : Tᴴ + T = 0 := by
    refine isDualFamily_ratMatrices.eq_zero_of_forall_eq_one _ fun Z ↦ ?_
    have h_period (x : Matrix b b (𝔸 E)) : D.radicalCentre (x + (Zᴴ + Z)) = D.radicalCentre x :=
      ext_adeleMatrix (by simp [add_sub_add_comm])
    have h_one : (stdAddChar E (T.map toAdele * (Zᴴ + Z)).trace : ℂ) = 1 :=
      h_per (Zᴴ + Z) 1 (by simp [h_period])
    simpa [↓isDualFamily_ratMatrices.add_left, ↓isDualFamily_ratMatrices.add_right,
      ← stdAddChar_inv_two_mul_add_star (trace _), ← trace_conjTranspose, add_comm,
        Z.trace_mul_comm,
      Zᴴ.trace_mul_comm] using h_one
  refine (hΛ_eq T _ hf).symm.trans (h_kill (τ T) _ (fun w ↦ ?_) fun hP ↦ ?_)
  · -- `(1, g)` is `1` at `𝔠.ramifiedPlaces`, so the frame there is that of `D`.
    have h_components (x : G E r) :
        (adeleMatrix x).map (componentsAt 𝔠) = (atPlaces 𝔠.ramifiedPlaces x.2).val := rfl
    simpa [Ψ₀, atPlaces_eq_one_of_mem_trivialOn hg, h_components] using! (hΛ_shear T (1, g) w).2
  · exact (hΛ_eq T _ h_frame).trans (h_coeff T (eq_neg_of_add_eq_zero_left hT) hP g hg)

/-- Let `S` be the set of finite places outside `𝔠.ramifiedPlaces` and its conjugate and let `e` be
the idempotent adele `idemAdele S.conjClosure`, which is `1` on `S` and `0` elsewhere. If `P` is
integral at the places of `S` and their conjugates and the hermitian `Q` is integral at
`𝔠.ramifiedPlaces`, then `e • P + (1 - e) • Q` has integral finite part. -/
lemma New.Exchange.SplitTameChar.isIntMatrix_glue_hermitian {E : Type} [Field E] [CMType E]
    {μ : NumberField.InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ) {ι : Type*} [Fintype ι]
    {S : Set (FinPlace E)} (hS : S = (𝔠.ramifiedPlaces : Set (FinPlace E)).conjClosureᶜ)
    {P Q : Matrix ι ι (𝔸 E)} (hQ : Qᴴ = Q) (P_int : IsIntMatrix (closureIntegers S) P)
    (Q_int : IsIntMatrix O (Q.map (componentsAt 𝔠))) :
    let e : 𝔸 E := idemAdele S.conjClosure
    IsIntMatrix (Ô E) ((e • P + (1 - e) • Q).map Prod.snd) := by
  subst hS
  intro e i j
  -- at a place conjugate to one of `𝔠.ramifiedPlaces`, the entry `Q i j` is the conjugate of
  -- `Q j i`
  have entry_int (v : FinPlace E)
      (hv : v ∉ ((𝔠.ramifiedPlaces : Set (FinPlace E)).conjClosureᶜ).conjClosure) :
      Valued.v ((Q i j).snd v) ≤ 1 := by
    obtain hv | hv : v ∈ 𝔠.ramifiedPlaces ∨ star v ∈ 𝔠.ramifiedPlaces :=
      Set.notMem_compl_iff.1 fun h ↦ hv (Or.inl h)
    · exact Q_int i j ⟨v, hv⟩ trivial
    · rw [← hQ]
      exact (v_star_apply ..).trans_le (Q_int j i ⟨star v, hv⟩ trivial)
  exact add_mem (P_int i j) (by simpa [e, ← idem_compl, idem_mul_mem_Ô] using entry_int)

/-- The pairs `(T, q)` of an index `T` and a point `q` of `GL_b(𝔸)` at which vanishing at self-dual
lattices is tested, for a hermitian space `V'` over the CM field `E` with form `V'.J`, signs `t'`
and adelic frame `V'.x`. Either (a) `T = V'.J` and `q = scaleIdele E • V'.x * Y` (`scaleIdele E` is
the idele of `WeilData E` that makes `Ô` self-dual), where the finite part of `Y` times some
`k ∈ GL_b(Ô)` is unitary for the form `1` (`U 1`), so that the columns of `V'.x * Y` span a lattice
that is self-dual for `T`; or (b) `T` is invertible and not of the form `aᴴ diag(t') a` at some
infinite place, and `q` is arbitrary. -/
def New.Exchange.IsSelfDualTestPair {E : Type} [Field E] [CMType E] [H : WeilData E]
    {b : Type} [Fintype b] [DecidableEq b] {t' : b → ℤˣ} (V' : Space E b t') (T : Matrix b b E)
    (q : GL b (𝔸 E)) : Prop :=
  (∃ Y : GL b (𝔸 E), ∃ k ∈ intGL b (Ô E),
    scaleIdele E • V'.x * Y = q ∧
      Y.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)) * k ∈ U 1 ∧ V'.J = T) ∨
  IsUnit T ∧ ¬RepresentedBy t' (T.map toAdele)

/-- Let `D` be a splitting of the space `X` (indices `m`, signs `r`) as `W₁` (indices `n`, signs
`s`) plus hyperbolic planes along `b` lines. A function `f` on `U(X)` vanishes at self-dual lattices
if its Fourier coefficient along the centre of the unipotent radical of the parabolic of `D`, at the
index `j • T` (`j` is the fixed skew element of `WeilData E`), vanishes at each point
`D.radicalElement c z * D.levi (q, g)` of that parabolic (a radical element times the Levi element
of `q ∈ GL_b(𝔸)` and `g ∈ U(W₁)`) for which `(T, q)` is a test pair for `V'`
(`IsSelfDualTestPair`). -/
def New.Space.Splitting.VanishesAtSelfDual
    {E : Type} [Field E] [CMType E] [H : WeilData E] {n b m : Type}
    [Fintype n] [DecidableEq n] [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
    {s : n → ℤˣ} {r : m → ℤˣ} {X : Space E m r} {W₁ : Space E n s}
    (D : X.Splitting W₁ b) {t' : b → ℤˣ} (V' : Space E b t') (f : G E r → ℂ) : Prop :=
  ∀ (T : Matrix b b E) (c : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E)) (q : GL b (𝔸 E))
      (g : G E s),
    IsSelfDualTestPair V' T q → D.centreCoeff (H.j • T) f (D.radicalElement c z * D.levi (q, g)) = 0

/-- Let `D` be a splitting of `X` over `W₁` along `b` lines, let `j` be the fixed skew element of
`WeilData E` and `scaleIdele E` its idele that makes `Ô` self-dual. Let `f` be an automorphic
function that vanishes at self-dual lattices, tested on the pairs of a hermitian space `V'` with
Gram matrix `V'.J`, adelic frame `V'.x` and signs `t'`: its Fourier coefficient `D.centreCoeff`
along the centre of the unipotent radical, at the index `j • T`, vanishes at the points
`D.radicalElement c z * D.levi (q, g)` if (a) `T = V'.J` and `q = scaleIdele E • V'.x * Y`, where
the finite part of `Y` times some `k ∈ GL_b(Ô)` is unitary, or (b) `T` is invertible and at some
infinite place not of the form `aᴴ diag(t') a`. Let `det β ≠ 0`, and let the columns of `q * k`,
with `k ∈ GL_b(Ô)`, be orthonormal for `β` at the finite places. Then the coefficient at `j • β`
vanishes at `D.radicalElement l z * D.levi (scaleIdele E • q, g)`. -/
lemma New.Space.Splitting.centreCoeff_eq_zero_of_orthonormal
    {E : Type} [Field E] [CMType E] [H : WeilData E] {n b m : Type}
    [Fintype n] [DecidableEq n] [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
    {s : n → ℤˣ} {r : m → ℤˣ} {X : Space E m r} {W₁ : Space E n s} (D : X.Splitting W₁ b)
    {t' : b → ℤˣ} (V' : Space E b t') {f : G E r → ℂ} (h_aut : IsAutFunction X f)
    (h_van : D.VanishesAtSelfDual V' f) {β : Matrix b b E} (hdet : β.det ≠ 0) {q : GL b (𝔸 E)}
    {k : GL b (𝔸f E)} (k_int : k ∈ intGL b (Ô E))
    (h_orth : k.valᴴ * ((q.valᴴ * (β.map toAdele * q.val)).map Prod.snd * k.val) = 1)
    (l : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E)) (g : G E s) :
    D.centreCoeff (H.j • β) f (D.radicalElement l z * D.levi (scaleIdele E • q, g)) = 0 := by
  have hβ : IsUnit β := by simpa [isUnit_iff_isUnit_det] using hdet
  obtain h_real | h_real := em' (RepresentedBy t' (β.map toAdele))
  · -- case (b) of a test pair
    exact h_van _ _ _ _ _ (.inr ⟨hβ, h_real⟩)
  -- Now `β` has frames of signs `t'` at infinity and the orthonormal frame `q * k` at the finite
  -- places. By Landherr's theorem `β = cᴴ * V'.J * c` for a rational `c`, and the adelic frame of
  -- `β` is `c⁻¹ * V'.x * w` with `w` unitary (`hw`).
  choose a ha using h_real
  have a_unit (v : NumberField.InfinitePlace E) : IsUnit (a v) :=
    isUnit_of_mul_isUnit_right ((ha v).substr (hβ.map (mapMatrix _)))
  have h_infinite (v : NumberField.InfinitePlace E) :
      ((a_unit v).unit⁻¹).valᴴ * atRealPlace (β.map toAdele) v * ((a_unit v).unit⁻¹).val =
        signMatrix t' := gram_inv_of_gram_eq (ha v)
  have h_finite : (q.map (.snd ..) * k).valᴴ * β.map (↑) * (q.map (.snd ..) * k).val = 1 := by
    simpa [← coe_snd, mul_assoc] using! h_orth
  obtain ⟨c, w, rfl : _ = β, hw, -⟩ :=
    V'.exists_x_eq_and_ratEmbed_conj_eq ⟨β, _, gram_mkAdelicGL h_infinite h_finite⟩
  -- Move `c` from the index to the point (`centreCoeff_rat_mul` for the rational point
  -- `D.levi (c, 1)`), then commute that point past the radical: the new Levi part is
  -- `scaleIdele E • (c * q)`.
  rw [← smul_mul, ← mul_smul_comm,
    ← centreCoeff_rat_mul _ h_aut _ (levi_mem_Gamma _ _ (one_mem _)) _ (actsOnFrame_levi ..),
    ← mul_assoc, levi_conj_radicalElement, mul_assoc, ← map_mul]
  refine h_van _ _ _ _ _
    (.inl ⟨V'.x⁻¹ * (c.map toAdele * q), k, k_int, Units.ext (by simp), ?_, rfl⟩)
  -- The finite part of `V'.x⁻¹ * c * q * k` is that of the unitary point `w`, which is in `U 1`.
  have h_snd := congrArg (GeneralLinearGroup.map (.snd _ (𝔸f E))) (inv_mul_eq_of_eq_mul hw)
  convert w.2.2
  simpa [mul_assoc] using! h_snd

section PartialMeans

variable {E : Type} [Field E] [CMType E] [H : WeilData E] {n a b m : Type} [Fintype n]
  [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype m]
  [DecidableEq m]
variable {s : n → ℤˣ} {t : a → ℤˣ} {r : m → ℤˣ} {μ : NumberField.InfinitePlace E → ℤ}
  {𝔠 : SplitTameChar E μ} {X : Space E m r} {W₁ : Space E n s} {W : Space E a t}

/-- Let `𝒟` be an equivariant lift on `M` and let `ν ∈ U(X)` have matrix `1 + e u c - ē N`, with
`c u = 0`, `e` the idempotent of `𝔠.ramifiedPlaces` and `N` any matrix, so that `ν` is `1 + u c` at
`𝔠.ramifiedPlaces`. Let `A` split one isotropic line off `X`, leaving `W₀`, let `B` split `b` planes
off `W₀`, leaving `W`, and let `D` split `X` over `W₁`. For `Ψ ∈ M`, let `Ψ' y = Ψ (g y)`, with `g`
the component of `x⁻¹ ν x` at `𝔠.ramifiedPlaces`. Then `Ψ' ∈ M`, and the partial mean of `𝒟 Ψ'` at
`x` equals that of `𝒟 Ψ` at `ν⁻¹ x`. -/
lemma New.Exchange.IsEquivariantLift.partialMean_shear
    {M : Submodule ℂ (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ)}
    {𝒟 : (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E r → ℂ}
    (h_lift : IsEquivariantLift 𝔠 X M 𝒟) {W₀ : Space E ((b ⊕ b) ⊕ a) (hyperbolicSigns b ⊕ᵥ t)}
    (A : X.Splitting W₀ Unit) (B : W₀.Splitting W b) (D : X.Splitting W₁ b) (T : Matrix b b E)
    {Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ} (hΨ : Ψ ∈ M) {ν : G E r}
    {u : Matrix m Unit (𝔸 E)} {c : Matrix Unit m (𝔸 E)} {N : Matrix m m (𝔸 E)}
    (hν : ν.adeleMatrix = 1 + ((idemAdele 𝔠.ramifiedPlaces : 𝔸 E) • (u * c) -
      star (idemAdele 𝔠.ramifiedPlaces : 𝔸 E) • N))
    (hc : c * u = 0) (x : G E r) :
    let Ψ' (y : Matrix m b (LocProd 𝔠.ramifiedPlaces)) : ℂ :=
      Ψ (y + (x⁻¹.adeleMatrix * u).map (componentsAt 𝔠) *
        ((c * x.adeleMatrix).map (componentsAt 𝔠) * y))
    Ψ' ∈ M ∧ A.partialMean B D T (𝒟 Ψ') x = A.partialMean B D T (𝒟 Ψ) (ν⁻¹ * x) := by
  intro Ψ'
  obtain ⟨h_mem, h_shift⟩ : Ψ' ∈ M ∧ ∀ y : G E r, 𝒟 Ψ' (y * x) = 𝒟 Ψ (y * (ν⁻¹ * x)) :=
    h_lift.apply_shear hΨ hν hc x
  have h_assoc (y y' : G E r) : 𝒟 Ψ' (y * (y' * x)) = 𝒟 Ψ (y * (y' * (ν⁻¹ * x))) := by
    simpa only [mul_assoc] using h_shift (y * y')
  exact ⟨h_mem, by simp only [partialMean, centreCoeff, h_assoc]⟩

/-- Let `𝒟` be an equivariant lift on `M`. Let `A` split one isotropic line off `X`, `B` split `b`
planes off what remains and `D` split `X` over `W₁`, and let the adelic isotropic frame `kAdelic` of
`D` be the image under the embedding `A.iAdelic` of that of `B`. At each point `x`, the map
`Ψ ↦ A.partialMean B D T (𝒟 Ψ) x` on `M` is the restriction of a linear form `L`, and `L` is
invariant on `M` under composition with `y ↦ y + u w l y` for all rows `w`. Here `u` and `l` are the
components at the ramified places of `x⁻¹ A.kAdelic` (the isotropic vector of `A`) and of
`D.lCoord x`. -/
lemma New.Exchange.IsEquivariantLift.exists_linear_partialMean
    {M : Submodule ℂ (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ)}
    {𝒟 : (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E r → ℂ}
    (h_lift : IsEquivariantLift 𝔠 X M 𝒟) {W₀ : Space E ((b ⊕ b) ⊕ a) (hyperbolicSigns b ⊕ᵥ t)}
    {A : X.Splitting W₀ Unit} {B : W₀.Splitting W b} {D : X.Splitting W₁ b}
    (hD : D.kAdelic = A.iAdelic * B.kAdelic) (T : Matrix b b E) (x : G E r) :
    ∃ L : (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] ℂ, ∀ Ψ ∈ M,
      L Ψ = A.partialMean B D T (𝒟 Ψ) x ∧
      ∀ w : Matrix Unit b (LocProd 𝔠.ramifiedPlaces),
        L (fun y : Matrix m b (LocProd 𝔠.ramifiedPlaces) ↦
          Ψ (y + (x⁻¹.adeleMatrix * A.kAdelic).map (componentsAt 𝔠) *
            (w * ((D.lCoord * x.adeleMatrix).map (componentsAt 𝔠) * y)))) = L Ψ := by
  let L₀ : M →ₗ[ℂ] ℂ :=
    { toFun Ψ := A.partialMean B D T (𝒟 Ψ) x
      map_add' Ψ Φ := by
        simpa using partialMean_add hD (h_lift.isAutFunction Ψ.2) (h_lift.isAutFunction Φ.2) x
      map_smul' := by simp [partialMean, centreCoeff, ← quotMean_const_mul, mul_left_comm] }
  obtain ⟨L, hL₀ : L ∘ₗ M.subtype = L₀⟩ := L₀.exists_extend
  have hL (Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) (hΨ : Ψ ∈ M) :
      L Ψ = A.partialMean B D T (𝒟 Ψ) x := LinearMap.congr_fun hL₀ ⟨Ψ, hΨ⟩
  refine ⟨L, fun Ψ hΨ ↦ ⟨hL Ψ hΨ, fun w ↦ ?_⟩⟩
  -- Lift `w` to an adelic row `N`. The shift `ν` by the part of `N` on `𝔠.ramifiedPlaces` acts on
  -- the datum by the given map, and it fixes the partial mean.
  obtain ⟨N, rfl⟩ : ∃ N : Matrix Unit b (𝔸 E), N.map (componentsAt 𝔠) = w :=
    ⟨w.map (0, adeleOfLocal _ ·), ext fun i j ↦ evalPlaces_adeleOfLocal _ (w i j)⟩
  let e : 𝔸 E := idemAdele 𝔠.ramifiedPlaces
  let ν : G E r := A.symm.lineShift B (e • N)
  have h_coord : D.lCoord = B.lCoord * A.iCoord := lCoord_eq_lCoord_mul_iCoord hD
  have h_mat : ν.adeleMatrix =
      1 + (e • (A.kAdelic * (N * D.lCoord)) - star e • (D.kAdelic * (Nᴴ * A.lCoord))) := by
    simp [ν, lineShift, hD, h_coord, comp_kAdelic, fromBlocks_conjTranspose, sub_eq_add_neg,
      Matrix.mul_add, Matrix.add_mul, fromCols_mul_fromBlocks, fromCols_mul_fromRows,
      Matrix.mul_assoc]
  obtain ⟨h_mem, h_mean⟩ := h_lift.partialMean_shear A B D T hΨ h_mat
    (by simp [h_coord, Matrix.mul_assoc]) x
  simp only [Matrix.mul_assoc N, Matrix.map_mul, Matrix.mul_assoc (N.map _)] at h_mem h_mean ⊢
  -- the shift `ν` fixes the partial mean
  rw [hL _ h_mem, hL _ hΨ, h_mean,
    ← partialMean_lineShift_symm_mul hD (h_lift.isAutFunction hΨ) (e • N) (ν⁻¹ * x),
    mul_inv_cancel_left]

/-- Invariance under shears. Let `𝒟` be an equivariant lift on `M` and `f = 𝒟 Ψ₀`, where `Ψ₀ ∈ M` is
the standard datum of the adapted splitting `D` (frame orthonormal at infinity and integral at the
finite places): `y ↦ χ⁻¹(det (dualL y))` on integral `y` with unit determinant, 0 elsewhere, for the
dual block `dualL` of the frame of `D` read at the ramified places and `χ = 𝔠.semilocalChar`. Let
`A` split one isotropic line off `X`, leaving the sum `hyperbolicSum b W` of `b` hyperbolic planes
and `W`, so that the frame of `D` is the image under `A` of the frame of the tautological splitting
`removePlanes b W` of those planes (`hA`). Let `S` be the set of finite places outside
`𝔠.ramifiedPlaces` and its conjugate (`hS`), and let `g` fix the frame of `D` at all places outside
`S`. Then, for every `T`, the partial mean of `f` takes the same value at `g` and `ν * g`, for each
`ν` that is `1 + u c` at `𝔠.ramifiedPlaces` and `1` away from `𝔠.ramifiedPlaces` and its conjugate,
where `u` is the isotropic vector of `A` and `c u = 0`. -/
lemma New.Exchange.IsEquivariantLift.shearInvariant_stdColDatum
    {M : Submodule ℂ (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ)}
    {𝒟 : (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E r → ℂ}
    (h_lift : IsEquivariantLift 𝔠 X M 𝒟) (D : X.Splitting W₁ b) [IsBaseAdapted D]
    (h_frame : stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL ∈ M) (T : Matrix b b E)
    (A : X.Splitting (hyperbolicSum b W) Unit)
    (hA : D.kAdelic = A.iAdelic * (removePlanes b W).kAdelic)
    {S : Set (FinPlace E)} (hS : S = (𝔠.ramifiedPlaces : Set (FinPlace E)).conjClosureᶜ) (g : G E r)
    (hg : g ∈ D.frameStabilizer (1 - idemAdele S.conjClosure)) :
    A.ShearInvariant (removePlanes b W) D T
      (𝒟 (stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL))
      (idemAdele (star (𝔠.ramifiedPlaces : Set (FinPlace E)))) g := by
  -- The partial mean at `ν * g` is a linear form `Λ` in the datum, and `ν` acts on the datum by a
  -- shear. The maps `y ↦ y + k w dualL y` along the line `k` of `A` fix `Λ`, so the shear fixes its
  -- value at `Ψ` (`map_shear_stdColDatum_eq`).
  intro ν c N hc hν
  -- At `𝔠.ramifiedPlaces`, neither `g` nor `ν` changes the coordinates that the datum reads.
  let e : 𝔸 E := idemAdele S.conjClosure
  have lCoord_g : (1 - e) • D.lCoord = (1 - e) • (D.lCoord * g.adeleMatrix) := by
    -- conjugate-transpose `g * (1 - e) • k = (1 - e) • k` and use that `g` is unitary
    have h_conj : (g.adeleMatrix * (1 - e) • D.kAdelic)ᴴ * (stdForm E r * g.adeleMatrix) =
        ((1 - e) • D.kAdelic)ᴴ * (stdForm E r * g.adeleMatrix) := by
      rw [mem_frameStabilizer.1 hg]
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc g.adeleMatrixᴴ,
      conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix] at h_conj
    simpa only [e, conjTranspose_smul, star_sub, star_one, star_idemAdele_conjClosure,
      Matrix.smul_mul,
      ← Matrix.mul_assoc, lCoord] using h_conj
  have h_coord : D.lCoord = (removePlanes b W).lCoord * A.iCoord := lCoord_eq_lCoord_mul_iCoord hA
  have L'_eq :
      (adaptedFrame 𝔠.readsAt D).dualL = (D.lCoord * (ν * g).adeleMatrix).map (componentsAt 𝔠) := by
    rw [h_coord]
    funext i j ⟨u, hu⟩
    have h_entry : (D.lCoord i j).2 u = ((D.lCoord * g.adeleMatrix) i j).2 u := by
      simpa [e, hS, 𝔠.star_notMem, hu] using congrArg (fun Y ↦ (Y i j).2 u) lCoord_g
    -- at `u` the matrix of `ν` is `1 + A.kAdelic * c`, and `A.iCoord * A.kAdelic = 0`
    simpa [lCoord.eq_1 D, componentsAt, adaptedFrame, 𝔠.star_notMem, hu, hν, hA,
      Matrix.mul_assoc, add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub] using h_entry
  let Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ :=
    stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL
  let k : Matrix m Unit (LocProd 𝔠.ramifiedPlaces) :=
    ((ν * g)⁻¹.adeleMatrix * A.kAdelic).map (componentsAt 𝔠)
  let Ψ' (y : Matrix m b (LocProd 𝔠.ramifiedPlaces)) : ℂ :=
    Ψ (y + k * ((c * (ν * g).adeleMatrix).map (componentsAt 𝔠) * y))
  obtain ⟨Λ, hΛ⟩ := h_lift.exists_linear_partialMean hA T (ν * g)
  obtain ⟨Ψ'_mem : Ψ' ∈ M, mean_shear⟩ :=
    h_lift.partialMean_shear A (removePlanes b W) D T h_frame
      (by simpa [Prod.star_def, star_idem] using hν) hc (ν * g)
  have Λ_translate (Φ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) (hΦ : Φ ∈ M)
      (w : Matrix Unit b (LocProd 𝔠.ramifiedPlaces)) :
      Λ (fun y ↦ Φ (y + k * (w * ((adaptedFrame 𝔠.readsAt D).dualL * y)))) = Λ Φ := by
    simpa only [L'_eq] using (hΛ Φ hΦ).2 w
  obtain ⟨L'_mul_k, c_mul_k⟩ : (adaptedFrame 𝔠.readsAt D).dualL * k = 0 ∧
      (c * (ν * g).adeleMatrix).map (componentsAt 𝔠) * k = 0 := by
    simp [k, L'_eq, h_coord, hc, ← Matrix.map_mul, ← adeleMatrix_mul, ← (adeleMatrix _).mul_assoc,
      Matrix.mul_assoc]
  have Λ_shear : Λ Ψ' = Λ Ψ :=
    map_shear_stdColDatum_eq (adaptedFrame 𝔠.readsAt D).blockRelations.isIntMatrix_dualL L'_mul_k
      c_mul_k
      h_lift.le_schwartzBruhat Λ_translate h_frame Ψ'_mem
  calc A.partialMean (removePlanes b W) D T (𝒟 Ψ) (ν * g)
      = Λ Ψ' := by rw [Λ_shear, (hΛ Ψ h_frame).1]
    _ = A.partialMean (removePlanes b W) D T (𝒟 Ψ') (ν * g) := (hΛ Ψ' Ψ'_mem).1
    _ = A.partialMean (removePlanes b W) D T (𝒟 Ψ) (ν⁻¹ * (ν * g)) := mean_shear
    _ = _ := by rw [inv_mul_cancel_left]

end PartialMeans

/-- Self-dual lattices suffice. Let `𝒟` be an equivariant lift on `M` (a linear map from data at the
ramified places `S = 𝔠.ramifiedPlaces` to functions on `U(X)`, automorphic and `S`-equivariant on
`M`). Let `D` and `D₁` be adapted splittings of `X` over `W₁` along `b` lines and of `W₁` over `W`
along one line; the extra line `D₁` gives the shears under which the partial means are invariant.
Let `f = 𝒟 Ψ₀` for the standard datum `Ψ₀ ∈ M`: `y ↦ χ⁻¹(det (dualL y))` at integral `y` with unit
determinant, 0 elsewhere, for the dual block `dualL` of the frame of `D` read at `S` and
`χ = 𝔠.semilocalChar`. Suppose that `f` vanishes at self-dual lattices along `D`, tested on the
pairs of the hermitian space `V'` with form `V'.J`. Then `𝒟` maps to zero every locally constant
datum `Ψ` that has a matched function `Φ`. -/
theorem New.Exchange.IsEquivariantLift.apply_eq_zero_of_areMatched
    {E : Type} [Field E] [CMType E] [H : WeilData E] {n a b m : Type}
    [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype m] [DecidableEq m] {s : n → ℤˣ} {t : a → ℤˣ} {r : m → ℤˣ}
    {μ : NumberField.InfinitePlace E → ℤ} {𝔠 : SplitTameChar E μ}
    {X : Space E m r} {W₁ : Space E n s} {W : Space E a t}
    {M : Submodule ℂ (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ)}
    {𝒟 : (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E r → ℂ}
    (h_lift : IsEquivariantLift 𝔠 X M 𝒟) (D : X.Splitting W₁ b) (D₁ : W₁.Splitting W Unit)
    [IsBaseAdapted D] [IsBaseAdapted D₁] {t' : b → ℤˣ} (V' : Space E b t')
    (h_van : D.VanishesAtSelfDual V'
      (𝒟 (stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL)))
    (h_frame : stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL ∈ M)
    {p : Type} [Fintype p] {σ : b ⊕ p ≃ m} {Φ : Matrix p m (LocProd 𝔠.ramifiedPlaces) → ℂ}
    {Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hΨ : IsLocallyConstant Ψ) (hΦΨ : AreMatched O σ 𝔠.semilocalChar Φ Ψ) :
    𝒟 Ψ = 0 := by
  -- It is enough that the coefficients along `D` of the image under `𝒟` of the standard datum of
  -- the frame vanish at the indices `T` for which `invDifferentIdele⁻¹ T` is unimodular at
  -- `𝔠.ramifiedPlaces`.
  refine h_lift.apply_eq_zero_of_centreCoeff_eq_zero D h_frame hΨ hΦΨ fun T hT hP g₀ hg₀ ↦ ?_
  let f : G E r → ℂ := 𝒟 (stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL)
  have h_aut : IsAutFunction X f := h_lift.isAutFunction h_frame
  -- The index is skew-hermitian and invertible. By the invariance under shears it suffices to
  -- show vanishing at the points of the parabolic where the Gram matrix is unimodular; there
  -- `centreCoeff_eq_zero_of_orthonormal` applies.
  obtain ⟨-, hdet_unit⟩ := isPrimitiveMatrix_iff_int_and_unit_det.1 hP
  have hdet : T.det ≠ 0 := fun h_zero ↦ by
    simp [← mapMatrix_apply, ← map_det, h_zero] at hdet_unit
  -- Remove the extra line first: `A` splits `X` over `W` plus `b` planes, and the
  -- frame of `D` is that of these planes.
  obtain ⟨A : X.Splitting (hyperbolicSum b W) Unit, hA, hA_comp, -⟩ :=
    exists_isBaseAdapted_comp_removePlanes (D.comp D₁) (.sumComm ..)
  have hD_frame : D.kAdelic = A.iAdelic * (removePlanes b W).kAdelic := by
    have h_cols : (A.comp (removePlanes b W)).kAdelic =
        (D.comp D₁).kAdelic.submatrix _root_.id (Equiv.sumComm Unit b) := by
      rw [kAdelic, hA_comp]; rfl
    simp only [comp_kAdelic] at h_cols
    exact (congrArg toCols₂ h_cols).symm
  -- Take for `S` the places outside `𝔠.ramifiedPlaces` and its conjugate, and the shears for
  -- `star 𝔠.ramifiedPlaces`.
  set S : Set (FinPlace E) := (𝔠.ramifiedPlaces : Set (FinPlace E)).conjClosureᶜ
  have h_level : HasLevel f (stdLevel E m ⊓ supportedOn m S) :=
    supportedOn_compl.substr (h_lift.invariant_off _ h_frame)
  have hg₀_supp : g₀ ∈ supportedOn m S := supportedOn_compl.ge hg₀
  refine centreCoeff_eq_zero_of_unimodular h_level h_aut A _ hD_frame hdet (.star 𝔠.nonempty)
    (h_lift.shearInvariant_stdColDatum D h_frame T A hD_frame rfl)
    (h_lift.shearInvariant_stdColDatum D h_frame T A.symm hD_frame rfl)
    (fun x γ hx hγ ↦ ?_) (mem_frameStabilizer_of_mem_supportedOn hg₀_supp)
  obtain ⟨C_int, C', C'_int, hC'⟩ := hγ
  -- Let `τ` be the normalised index `invDifferentIdele⁻¹ T`, and write `x` as a point
  -- `D.radicalElement l z * D.levi (q₀, g)` of the parabolic.
  let τ : GL b (𝔸 E) :=
    (invDifferentIdele E)⁻¹ • (GeneralLinearGroup.mkOfDetNeZero T hdet).map toAdele
  have hτ : τ.1ᴴ = τ := by simp [τ, hT, Units.smul_def, star_invDifferentIdele_inv, Matrix.map_neg]
  obtain ⟨l, z, q₀, g, rfl, hq₀, -⟩ := D.exists_eq_radicalElement_mul_levi hx
  -- The Gram matrix `siegelBracket T q₀` is `siegelBracket T γ` on `S` and `τ` off `S`, so it is
  -- unimodular at all finite places.
  let e : 𝔸 E := idemAdele S.conjClosure
  let Q : Matrix b b (𝔸 E) := e • siegelBracket T γ + (1 - e) • τ.1
  have Q_prim : IsPrimitiveMatrix (Ô E) (Q.map snd) := by
    have τ_inv_int := ((isPrimitiveMatrix_iff_mem_intGL (τ.map _)).1 hP).isIntMatrix_inv
    refine ⟨𝔠.isIntMatrix_glue_hermitian (S := S) rfl hτ C_int hP.1, _,
        𝔠.isIntMatrix_glue_hermitian (S := S) rfl ?_ C'_int τ_inv_int, ?_⟩
    -- the inverse glues `C'` and `τ⁻¹`: show that `τ⁻¹` is hermitian and compute the product
    · simp [hτ, conjTranspose_nonsing_inv]
    · simp [Q, e, ← coe_snd, ← Matrix.map_mul, sub_mul, hC', mul_add, add_mul, smul_smul, mul_sub]
  have Q_eq : Q = siegelBracket T q₀.1 := by
    simp [Q, e, S, hq₀, siegelBracket, τ, mul_comm, smul_smul, Units.smul_def, mul_sub, add_mul,
      mul_add]
  have Q_herm : (Q.map snd)ᴴ = Q.map snd := by
    simp [Q, e, ← conjTranspose_map _ snd_star, siegelBracket, hτ, hT, mul_assoc,
      star_invDifferentIdele_inv, Matrix.map_neg]
  -- a unimodular hermitian matrix over `Ô E` has an integral orthonormal basis `k`
  obtain ⟨k, k_int, h_orth⟩ := exists_orthonormal_Ô ⟨Q_herm, isPrimitiveMatrix_iff.1 Q_prim⟩
  -- With `T = j • β` and `q₀ = scaleIdele • q`, the columns of `q * k` are orthonormal for `β`.
  obtain ⟨β, rfl⟩ : ∃ β : Matrix b b E, H.j • β = T := MulAction.surjective₀ H.j_ne_zero T
  obtain ⟨q, rfl⟩ : ∃ q : GL b (𝔸 E), scaleIdele E • q = q₀ := MulAction.surjective _ q₀
  have δ_eq : (scaleIdele E).1 * (toAdele H.j * star (scaleIdele E).1) = invDifferentIdele E := by
    simp [invDifferentIdele, mul_left_comm, mul_assoc]
  have hβ_det : β.det ≠ 0 := by simpa [j_ne_zero] using hdet
  have h_orth_β : k.valᴴ * ((q.valᴴ * (β.map toAdele * q.val)).map Prod.snd * k.val) = 1 := by
    simpa [Q_eq, siegelBracket, δ_eq, Units.smul_def, map_smul', smul_smul, mul_assoc] using h_orth
  exact D.centreCoeff_eq_zero_of_orthonormal V' h_aut h_van hβ_det k_int h_orth_β l z g

end StandardCoefficients
