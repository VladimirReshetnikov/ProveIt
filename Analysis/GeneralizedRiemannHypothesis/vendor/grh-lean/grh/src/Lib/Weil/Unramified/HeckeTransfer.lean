import Lib.ClassField.Avatar.HeckeBaseChange
import Lib.General.Combinatorics
import Lib.General.LinearAlgebra.BlockEmbeddings
import Lib.Weil.DualPair.FiniteAction
import Lib.Weil.Lift

/-!
# Hecke polynomials pass through a theta lift

Let `w` be a split place of norm q, let S and T be hermitian spaces of ranks n and n + k, and let
the characters `a`, `b` be unramified at `w`. On the vacuum at `w` of the Weil representation
`New.pairWeil S T a b`, the Hecke operators of S and of T count subspaces of the kernels of an
integral matrix and of its transpose modulo `w`. By the q-binomial theorem the Hecke polynomial for
T at `w` is then the rescaled polynomial for S at w̄ times ∏_{l<k}(1 − q^l X), which is
`New.SiegelWeil.qPochhammer q k X`. This identity passes to theta lifts.

## Main definitions and results

* `New.AutChar.frobValue`: the complex number `χ(ϖ_w) q_w^(N/2)`, with
  `χ = New.AutChar.spaceChar a N` and `N = Fintype.card n`.
* `New.SiegelWeil.heckePolyOp_pairWeilTarget`: the identity on the vacuum.
  `New.SiegelWeil.hecke_transfer_of_equivariant` is its image under an equivariant linear map.
* `New.SiegelWeil.hecke_transfer_of_pairing`, `New.SiegelWeil.lift_swap_heckePolyOp`: the transfer
  through an equivariant bilinear map and through the transposed theta lift.
* `New.SiegelWeil.hasHeckePolynomial_of_pairing`, `New.SiegelWeil.hasHeckePolynomial_formLift`: the
  Hecke polynomial of a lift.
* `New.SiegelWeil.hasHeckePolynomial_qPochhammer`: the Hecke polynomial of a fixed vector.

Notions from other files:
* `New.WeilData`: Weil data on a stably unramified E. They consist of ȷ in E with ȷ = −ȷ̄, Im τȷ > 0
  for every τ in the CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed
  integers Ô are self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at
  uniformisers of the places w with w = w̄.
* `New.ofSplitPlace`: the map GL_n(E_w) → G_f, g ↦ the unitary element that is g at w and 1 off w,
  w̄.
* `New.LocField`: the completion E_w of E at the finite place w.

## Relation to the literature

Known result: the unramified theta correspondence for GL_n, stated for operators. Compare R. Howe,
θ-series and invariant theory, Corvallis 1979; S. Rallis, Langlands' functoriality and the Weil
representation, Amer. J. Math. 104 (1982); S. Kudla, On the local theta-correspondence, Invent.
Math. 83 (1986).
-/

/-!
## The value at a uniformiser of the character attached to a character of [U(1)]

In this section, `a` is a character of `[U(1)]` (`New.AutChar`), `n` is a finite index type of
cardinality `N`, and `w` is a finite place.
-/

/-- The complex number χ(ϖ_w)·q_w^{N/2}, where N is the cardinality of n,
χ = `New.AutChar.spaceChar` a N is the Hecke character x ↦ a(x/x̄)υ(x)^{−N} and ϖ_w the chosen
uniformiser at w. -/
noncomputable def New.AutChar.frobValue {E : Type} [Field E] [CMType E] [WeilData E] (a : AutChar E)
    (n : Type*) [Fintype n] (w : FinPlace E) : ℂ :=
  (a.spaceChar (Fintype.card n)).atUniformizer w * √w.q ^ Fintype.card n

/-!
## Transfer of Hecke polynomials through the Weil representation

The Hecke polynomial `New.heckePolyOp π hw X` is the operator ∑_i (−X)^i q^(i choose 2) T_{w,i};
`New.heckePolyCoeff X U` = (−X)^i q^(i choose 2) for a subspace U of dimension i, and
`New.basicCosetRep U` is a coset representative in T_{w,i} with kernel U mod w.

Here `hw` is a proof that w is split.

`New.pairWeil S T a b` is the Weil representation of U(S) × U(T) twisted by the characters a, b; a
vacuum at w is a datum fixed by `projOn {w}`, the averaging operator over integral vectors at w and
w̄; K_w = `New.maxCompactAt n w` is the part above w and w̄ of the maximal compact subgroup.
-/

namespace New

open Matrix Fintype WeilData AutChar HeckeChar Valued Space G CharUnramifiedAt
open Finset hiding card

section Transfer

variable {E n m W Z : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] {w : FinPlace E} [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
  {π : Representation ℂ (Gf E n) W} {a b : AutChar E} {k : ℕ}

/-! ### Hecke polynomials as sums over subspaces of the residue space -/

lemma FinPlace.coe_q_eq_sq_sqrt : (w.q : ℂ) = √w.q ^ 2 := mod_cast by simp

/-- A Hecke character unramified at w takes at x ∈ E_w^× the value χ(ϖ_w)^(ord_w x). -/
lemma CharUnramifiedAt.apply_locFullIdele {χ : HeckeChar E} (h : CharUnramifiedAt (finPart χ) w)
    (x : (LocField w)ˣ) :
    χ.val (locFullIdele w x) = χ.atUniformizer w ^ (-(v x.val).log) := by
  -- Both sides are values of the finite part of `χ` at ideles concentrated at `w`.
  have h_locIdele : unitsMapNonUnital (singleAdele w) x = locIdele w x := rfl
  simpa [HeckeChar.atUniformizer, HeckeChar.finPart, locFullIdele, h_locIdele]
    using congrArg Units.val (h.apply_locIdele_eq_zpow x)

omit [DecidableEq n] in
/-- If the `i`-th term is the sum of `y U` over the subspaces `U` of 𝔽_w^n of dimension `i`, then
the sum `New.heckePolyEval` is the sum of `heckePolyCoeff X U • y U` over all subspaces. -/
lemma heckePolyEval_sum_finrank_eq (y : Submodule (ResField w) (n → ResField w) → W) (X : ℂ) :
    heckePolyEval n w (fun i : ℕ ↦ ∑ U ∈ {U : Submodule (ResField w) (n → ResField w) |
        Module.finrank (ResField w) U = i}, y U) X =
      ∑ U : Submodule (ResField w) (n → ResField w), heckePolyCoeff X U • y U := by
  have h_dim (U : Submodule (ResField w) (n → ResField w)) :
      Module.finrank (ResField w) U ∈ range (card n + 1) :=
    mem_range_succ_iff.mpr (U.finrank_le.trans_eq (Module.finrank_pi _))
  rw [← sum_fiberwise_of_maps_to fun U _ ↦ h_dim U, heckePolyEval]
  simp only [smul_sum]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun U hU ↦ ?_
  rw [heckePolyCoeff, (mem_filter.mp hU).right, card_ResField]

/-- On K_w-fixed vectors the Hecke polynomials at a split place w and at its conjugate are sums over
the subspaces U of 𝔽_w^n, with coefficients `New.heckePolyCoeff` and coset representatives the
transpose, respectively the inverse, of γ_U = `New.basicCosetRep U`. -/
lemma heckePolyOp_eq_sum (hw : w.IsSplit) {v : W} (hv : v ∈ sphericalAt π w) (X : ℂ) :
    heckePolyOp π hw X v =
      ∑ U : Submodule (ResField w) (n → ResField w),
        heckePolyCoeff X U • π (ofSplitPlace hw (transposeGL (basicCosetRep U))) v ∧
    heckePolyOp π hw.star X v =
      ∑ U : Submodule (ResField w) (n → ResField w),
        heckePolyCoeff X U • π (ofSplitPlace hw (basicCosetRep U)⁻¹) v := by
  have hv_level : v ∈ levelSpace (π.comp (ofSplitPlace hw)) (localIntGL n w) :=
    (mem_sphericalAt_iff hw).mp hv
  -- The operators `T_{w,i}` and `T_{w̄,i}` are sums over the subspaces `U` of dimension `i`.
  have h_at (i : ℕ) : heckeSplit π hw i v =
      ∑ U ∈ {U : Submodule (ResField w) (n → ResField w) | Module.finrank (ResField w) U = i},
        π (ofSplitPlace hw (transposeGL (basicCosetRep U))) v :=
    heckeGL_eq_sum hv_level
  have h_at_star (i : ℕ) : heckeSplit π hw.star i v =
      ∑ U ∈ {U : Submodule (ResField w) (n → ResField w) | Module.finrank (ResField w) U = i},
        π (ofSplitPlace hw (basicCosetRep U)⁻¹) v :=
    (heckeSplit_star hw i hv).trans (heckeFun_basicDoubleCoset_inv hv_level)
  simp only [← heckePolyEval_sum_finrank_eq]
  simp [heckePolyOp, heckePolyEval, h_at, h_at_star]

@[simp]
lemma HeckeChar.norm_atUniformizer (χ : HeckeChar E) (w : FinPlace E) : ‖χ.atUniformizer w‖ = 1 :=
  Circle.norm_coe _

/-- If the base change of a is unramified at the split place w, then a ∘ det is trivial on K_w. -/
lemma CharUnramifiedAt.det_maxCompactAt_eq_one (ha : CharUnramifiedAt a.baseChange.finPart w)
    (hw : w.IsSplit) {g : Gf E n} {s : n → ℤˣ} (hg : g ∈ maxCompactAt n w) :
    a.val (detFin s g) = 1 := by
  obtain ⟨hg_Kf, hg_supp⟩ : g ∈ stdLevel E n ∧ g ∈ Gf.supportedOn n {w} := Subgroup.mem_inf.mp hg
  ext
  rw [detFin_of_mem_supportedOn, detOn_eq_prod, prod_singleton,
    ← AutChar.baseChange_apply_coe_toFun,
    ha.apply_locFullIdele]
  · -- The determinant of `g` at `w` is a unit, as `g` lies in `stdLevel`.
    simp [mem_intGL_iff_det.mp (mem_stdLevel_iff.mp hg_Kf w)]
  · simp [hw]
  · simpa using hg_supp

namespace SiegelWeil

/-! ### The Hecke polynomials on the vacuum -/

/-- The product of `1 - q ^ j * X` over `j < k + l` splits into the first `k` factors and the
product of length `l` at `q ^ k * X`. -/
lemma qPochhammer_add (q k l : ℕ) (X : ℂ) :
    qPochhammer q (k + l) X = qPochhammer q k X * qPochhammer q l ((q : ℂ) ^ k * X) := by
  simp only [qPochhammer, prod_range_add, pow_add, mul_assoc, mul_left_comm ((q : ℂ) ^ k)]

open Classical in
/-- The `q`-binomial theorem weighted by integrality at `w`. Let `y` be a matrix over `E_w` with
columns indexed by `ι₂`, `c : ℂ`, and `γ_U = basicCosetRep U`. The sum over the subspaces `U` of
`𝔽_w^ι₂` of `heckePolyCoeff X U * c ^ dim U` times the indicator that `y γ_U⁻¹` is integral is
`qPochhammer q (card ι₂ - r) (X * c)` times the indicator that `y` is integral, where `r` is the
rank of `y` modulo `w`. -/
private lemma sum_heckePolyCoeff_mul_ite_integral_eq {ι₁ ι₂ : Type} [Fintype ι₂] [DecidableEq ι₂]
    (X c : ℂ) (y : Matrix ι₁ ι₂ (LocField w)) :
    ∑ U : Submodule (ResField w) (ι₂ → ResField w),
        heckePolyCoeff X U * (c ^ Module.finrank (ResField w) U *
          if ∀ (i : ι₁) (j : ι₂), v ((y * (basicCosetRep U)⁻¹.val) i j) ≤ 1 then 1 else 0) =
      qPochhammer w.q (card ι₂ - (y.map residueOrZero).rank) (X * c) *
        if ∀ (i : ι₁) (j : ι₂), v (y i j) ≤ 1 then 1 else 0 := by
  -- Only the subspaces `U` of the kernel of `y` modulo `w` contribute, and only for integral `y`.
  have h_integral (U : Submodule (ResField w) (ι₂ → ResField w)) :
      (∀ (i : ι₁) (j : ι₂), v ((y * (basicCosetRep U)⁻¹.val) i j) ≤ 1) ↔
        (∀ (i : ι₁) (j : ι₂), v (y i j) ≤ 1) ∧ U ≤ residueKer y := by
    rw [v_mul_inv_le_one_iff (basicCosetRep_mem_and_residueKer_eq U).left,
      (basicCosetRep_mem_and_residueKer_eq U).right]
  have h_coeff (U : Submodule (ResField w) (ι₂ → ResField w)) :
      heckePolyCoeff X U * c ^ Module.finrank (ResField w) U = heckePolyCoeff (X * c) U := by
    simp only [heckePolyCoeff, ← neg_mul, mul_pow, mul_right_comm]
  have h_binom : ∑ U : Submodule (ResField w) (ι₂ → ResField w) with U ≤ residueKer y,
      heckePolyCoeff (X * c) U =
        qPochhammer w.q (card ι₂ - (y.map residueOrZero).rank) (X * c) := by
    rw [q_binomial_submodule, card_ResField, card_sub_rank_eq_finrank_ker]
  simp only [h_integral, ← mul_assoc, h_coeff]
  by_cases hy : ∀ (i : ι₁) (j : ι₂), v (y i j) ≤ 1
  · simp only [← h_binom, sum_filter, ite_eq_left hy, and_iff_right hy, mul_one, mul_boole]
  · simp [hy]

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- An adelic matrix lies in the box of vectors integral at w if and only if its component at w has
integral entries. -/
lemma matrixToVec_mem_integralBox_singleton (y : Matrix m n (𝔸f E)) :
    matrixToVec y ∈ integralBox (m × n) {w} ↔ ∀ (i : m) (j : n), v (y.map (evalAt w) i j) ≤ 1 := by
  simp [mem_integralBox, idem_mul_mem_Ô, matrixToVec, evalAt_apply]

variable [WeilData E]
  {s : n → ℤˣ} {t : m → ℤˣ} {S : Space E n s} {T : Space E m t} {f : 𝒮 (S.hom T)} {p : ℂ → ℂ}

omit [DecidableEq n] in
/-- Let the base change of a be unramified at w, let χ = `a.spaceChar N` with N the cardinality of
n, and let x ∈ E_w^× have order i. Then χ(x)·|x|^(−N/2) = z^i with z = `a.frobValue n w`. -/
lemma spaceChar_div_sqrt_ideleAbs_pow (ha : CharUnramifiedAt a.baseChange.finPart w)
    {x : (LocField w)ˣ} {i : ℕ} (hx : v x.val = WithZero.exp (-(i : ℤ))) :
    (a.spaceChar (card n)).val (locFullIdele w x) / (√(ideleAbs (locFullIdele w x)) : ℂ) ^ card n =
      a.frobValue n w ^ i := by
  have h_char : (a.spaceChar (card n)).val (locFullIdele w x) =
      (a.spaceChar (card n)).atUniformizer w ^ i := by
    simp [AutChar.spaceChar, ha.apply_locFullIdele, (charUnramifiedAt_upsilon w).apply_locFullIdele,
      hx, atUniformizer, mul_pow, pow_right_comm]
  have h_abs : √(ideleAbs (locFullIdele w x)) = (√w.q ^ i)⁻¹ := by
    simp [ideleAbs_locFullIdele, norm_locField_eq_q_zpow, hx, Real.sqrt_eq_rpow,
      ← Real.rpow_pow_comm, Real.inv_rpow]
  simp [h_char, h_abs, frobValue, mul_pow, pow_right_comm]

/-- Translates of the vacuum by the group of T. Let w be split, the base change of a unramified at
w, and f a vacuum at w. Let U be a subspace of 𝔽_w^m of dimension i and γ_U = `New.basicCosetRep U`.
Then γ_Uᵀ sends f to `schrodingerOp {w} Ψ f` (`New.Space.schrodingerOp`), where Ψ is the function
x ↦ z^i·𝟙(xᵀγ_U⁻¹) on finite adelic matrices, read at w. Here 𝟙 is the indicator of the integral
matrices over E_w and z = `a.frobValue n w`. -/
lemma pairWeil_transposeGL_basicCosetRep (ha : CharUnramifiedAt a.baseChange.finPart w)
    (hw : w.IsSplit) (hf : (S.hom T).projOn {w} f = f)
    (U : Submodule (ResField w) (m → ResField w)) :
    pairWeil S T a b ((1, 1), 1, ofSplitPlace hw (transposeGL (basicCosetRep U))) f =
      (S.hom T).schrodingerOp {w}
        (fun x : m × n → 𝔸f E ↦ a.frobValue n w ^ Module.finrank (ResField w) U *
          if ∀ (i : n) (j : m),
            v ((((vecToMatrix x).map (evalAt w))ᵀ * (basicCosetRep U)⁻¹.val) i j) ≤ 1
          then 1 else 0) f := by
  classical
  set γ : GL m (LocField w) := basicCosetRep U
  obtain ⟨⟨-, -, hγ_det : v γ.det.val = WithZero.exp (-(Module.finrank (ResField w) U : ℤ))⟩, -⟩ :=
    basicCosetRep_mem_and_residueKer_eq U
  have h_det : v (transposeGL γ).det.val = WithZero.exp (-(Module.finrank (ResField w) U : ℤ)) := by
    simpa using hγ_det
  have h_local : (ofSplitPlace hw (transposeGL γ))⁻¹.val.val.map (evalAt w) = γ⁻¹.valᵀ := by
    rw [← map_inv]
    exact congrArg Units.val (atPlace_ofSplitPlace hw (transposeGL γ)⁻¹)
  have h_integral (x : m × n → 𝔸f E) :
      matrixToVec ((ofSplitPlace hw (transposeGL γ))⁻¹.val.val * vecToMatrix x) ∈
          integralBox (m × n) {w} ↔
        ∀ (i : n) (j : m), v ((((vecToMatrix x).map (evalAt w))ᵀ * γ⁻¹.val) i j) ≤ 1 := by
    rw [matrixToVec_mem_integralBox_singleton, Matrix.map_mul, h_local, forall_comm,
      ← transpose_transpose (_ * _), transpose_mul, transpose_transpose]
    rfl
  -- Write `f` as `schrodingerOp {w} Ψ f` with `Ψ` the indicator of the matrices integral at `w`;
  -- `pairWeil_schrodingerOp_of_mem_supportedOn` moves `Ψ`, with a scalar that depends on `det γ`.
  nth_rw 1 [← hf]
  simp (disch := simp [hw]) only [← schrodingerOp_boxIndicator, ← coe_singleton, detOn_eq_prod,
    pairWeil_schrodingerOp_of_mem_supportedOn, smul_schrodingerOp]
  congr 2 with x
  simp only [← h_integral, ← spaceChar_div_sqrt_ideleAbs_pow ha h_det]
  simp [boxIndicator]

/-- Translates of the vacuum by the group of S. Let w be split, the base change of b unramified at
w, and f a vacuum at w. Let U be a subspace of 𝔽_w^n of dimension i and γ_U = `New.basicCosetRep U`.
Then γ_U⁻¹ sends f to `schrodingerOp {w} Ψ f` (`New.Space.schrodingerOp`), where Ψ is the function
x ↦ z^i·𝟙(xγ_U⁻¹) on finite adelic matrices, read at w. Here 𝟙 is the indicator of the integral
matrices over E_w and z = `b.frobValue m w`. -/
lemma pairWeil_basicCosetRep_inv (hb : CharUnramifiedAt b.baseChange.finPart w)
    (hw : w.IsSplit) (hf : (S.hom T).projOn {w} f = f)
    (U : Submodule (ResField w) (n → ResField w)) :
    pairWeil S T a b ((1, ofSplitPlace hw (basicCosetRep U)⁻¹), 1, 1) f =
      (S.hom T).schrodingerOp {w}
        (fun x : m × n → 𝔸f E ↦ b.frobValue m w ^ Module.finrank (ResField w) U *
          if ∀ (i : m) (j : n),
            v (((vecToMatrix x).map (evalAt w) * (basicCosetRep U)⁻¹.val) i j) ≤ 1
          then 1 else 0) f := by
  classical
  set γ : GL n (LocField w) := basicCosetRep U
  obtain ⟨⟨-, -, hγ_det : v γ.det.val = WithZero.exp (-(Module.finrank (ResField w) U : ℤ))⟩, -⟩ :=
    basicCosetRep_mem_and_residueKer_eq U
  have h_local : (ofSplitPlace hw γ⁻¹).val.val.map (evalAt w) = γ⁻¹.val :=
    congrArg Units.val (atPlace_ofSplitPlace hw γ⁻¹)
  have h_integral (x : m × n → 𝔸f E) :
      matrixToVec (vecToMatrix x * (ofSplitPlace hw γ⁻¹).val.val) ∈ integralBox (m × n) {w} ↔
        ∀ (i : m) (j : n), v (((vecToMatrix x).map (evalAt w) * γ⁻¹.val) i j) ≤ 1 := by
    rw [matrixToVec_mem_integralBox_singleton, Matrix.map_mul, h_local]
  -- Write `f` as `schrodingerOp {w} Ψ f` with `Ψ` the indicator of the matrices integral at `w`;
  -- `pairWeil_schrodingerOp_of_mem_supportedOn` moves `Ψ`, with a scalar that depends on `det γ`.
  nth_rw 1 [← hf]
  simp (disch := simp [hw]) only [← schrodingerOp_boxIndicator, ← coe_singleton, detOn_eq_prod,
    pairWeil_schrodingerOp_of_mem_supportedOn, smul_schrodingerOp]
  congr 2 with x
  simp only [← h_integral, ← spaceChar_div_sqrt_ideleAbs_pow hb hγ_det]
  simp [boxIndicator, div_eq_mul_inv]

/-- Let w be split of norm q, let the base changes of a and b be unramified at w, and let f be a
vacuum at w (fixed by `projOn {w}`). Let γ_U = `basicCosetRep U`, the representative, with kernel U
mod w, of a coset in the double coset of diag(ϖ1_j, 1), where j = dim U. Let `segmentDatum d c` be
`schrodingerOp {w} Ψ f` (`New.Space.schrodingerOp`), where Ψ(x) is ∏_{l<r}(1 − q^l cX) with
r = d − rank(x mod w) if the matrix x is integral at w, and 0 otherwise. Then the sum over the
subspaces U of 𝔽_w^m of `heckePolyCoeff X U` = (−X)^j q^(j choose 2) times the `pairWeil` action of
γ_Uᵀ at w in the group of T sends f to `segmentDatum d c` with d = `card m` and
c = `a.frobValue n w` = χ(ϖ_w)q^{N/2}, where N = `card n` and χ is x ↦ a(x/x̄)υ(x)^{−N}.

The same holds in the group of S with the subspaces of 𝔽_w^n, with γ_U⁻¹, d = `card n` and
c = `b.frobValue m w`. -/
lemma sum_heckePolyCoeff_smul_pairWeil
    (ha : CharUnramifiedAt a.baseChange.finPart w) (hb : CharUnramifiedAt b.baseChange.finPart w)
    (hw : w.IsSplit) (hf : (S.hom T).projOn {w} f = f) (X : ℂ) :
    let segmentDatum (d : ℕ) (c : ℂ) : 𝒮 (S.hom T) :=
      schrodingerOp (S.hom T) {w}
        (residueDatum (fun () ↦ w) fun x : Unit → Matrix m n (ResField w) ↦
          qPochhammer w.q (d - (x ()).rank) (X * c)) f
    ∑ U : Submodule (ResField w) (m → ResField w),
        heckePolyCoeff X U •
          pairWeil S T a b ((1, 1), 1, ofSplitPlace hw (transposeGL (basicCosetRep U))) f =
      segmentDatum (card m) (a.frobValue n w) ∧
    ∑ U : Submodule (ResField w) (n → ResField w),
        heckePolyCoeff X U • pairWeil S T a b ((1, ofSplitPlace hw (basicCosetRep U)⁻¹), 1, 1) f =
      segmentDatum (card n) (b.frobValue m w) := by
  -- Read an adelic matrix `x` at `w`. The translates of `f` are given by
  -- `pairWeil_transposeGL_basicCosetRep` and `pairWeil_basicCosetRep_inv`; summing them over the
  -- subspaces `U` is the `q`-binomial theorem, for the matrix `loc x` or its transpose.
  let loc (x : m × n → 𝔸f E) : Matrix m n (LocField w) := (vecToMatrix x).map (evalAt w)
  -- `y * (basicCosetRep U)⁻¹` is integral if and only if `y` is integral and `U` lies in the kernel
  -- of `y` modulo `w`; the dimension of that kernel is the width of `y` minus its rank.
  have h_binom {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
      (y : Matrix I J (LocField w)) (c : ℂ) :
      ∑ U : Submodule (ResField w) (J → ResField w),
          heckePolyCoeff X U * (c ^ Module.finrank (ResField w) U *
            if ∀ (i : I) (j : J), v ((y * (basicCosetRep U)⁻¹.val) i j) ≤ 1 then 1 else 0) =
        if ∀ (i : I) (j : J), v (y i j) ≤ 1 then
          qPochhammer w.q (card J - (y.map residueOrZero).rank) (X * c) else 0 := by
    rw [← mul_boole]
    convert sum_heckePolyCoeff_mul_ite_integral_eq X c y
  have h_dat (d : ℕ) (c : ℂ) :
      residueDatum (fun () ↦ w) (fun x ↦ qPochhammer w.q (d - (x ()).rank) (X * c)) =
        fun x ↦ if ∀ (i : m) (j : n), v (loc x i j) ≤ 1 then
          qPochhammer w.q (d - ((loc x).map residueOrZero).rank) (X * c) else 0 := by
    ext x
    simp [residueDatum, loc, vecToMatrix, ← evalAt_apply, mem_LocInt]
  simp only [pairWeil_transposeGL_basicCosetRep ha hw hf, pairWeil_basicCosetRep_inv hb hw hf,
    h_dat, smul_schrodingerOp, ← _root_.sum_apply, ← map_sum]
  constructor
  · congr with x
    simpa [loc, transpose_map, forall_comm (α := n)] using h_binom (loc x)ᵀ (a.frobValue n w)
  · congr with x
    simpa [loc] using h_binom (loc x) (b.frobValue m w)

/-- The local identity behind the transfer, in the group of T. Let w be split of norm q, let the
base changes of a and b be unramified at w, and let f be a vacuum at w. Write
γ_U = `New.basicCosetRep U`. The sum over the subspaces U of 𝔽_w^m of `heckePolyCoeff X U` times
the action of γ_Uᵀ sends f to `schrodingerOp {w} Ψ f` (`New.Space.schrodingerOp`). Here Ψ(x) is
∏_{l<r}(1 − q^l X α) if the matrix x is integral at w, and 0 otherwise, where α = `a.frobValue n w`
and r is `card m` minus the rank of x modulo w. -/
lemma sum_heckePolyCoeff_smul_pairWeil_transposeGL
    (ha : CharUnramifiedAt a.baseChange.finPart w) (hb : CharUnramifiedAt b.baseChange.finPart w)
    (hw : w.IsSplit) (hf : (S.hom T).projOn {w} f = f) (X : ℂ) :
    ∑ U : Submodule (ResField w) (m → ResField w),
        heckePolyCoeff X U •
          pairWeil S T a b ((1, 1), 1, ofSplitPlace hw (transposeGL (basicCosetRep U))) f =
      schrodingerOp (S.hom T) {w}
        (residueDatum (fun () ↦ w) fun x : Unit → Matrix m n (ResField w) ↦
          qPochhammer w.q (card m - (x ()).rank) (X * a.frobValue n w))
        f :=
  (sum_heckePolyCoeff_smul_pairWeil ha hb hw hf X).left

/-- The local identity behind the transfer, in the group of S. Let w be split of norm q, let the
base changes of a and b be unramified at w, and let f be a vacuum at w. Write
γ_U = `New.basicCosetRep U`. The sum over the subspaces U of 𝔽_w^n of `heckePolyCoeff X U` times
the action of γ_U⁻¹ sends f to `schrodingerOp {w} Ψ f` (`New.Space.schrodingerOp`). Here Ψ(x) is
∏_{l<r}(1 − q^l X β) if the matrix x is integral at w, and 0 otherwise, where β = `b.frobValue m w`
and r is `card n` minus the rank of x modulo w. -/
lemma sum_heckePolyCoeff_smul_pairWeil_inv
    (ha : CharUnramifiedAt a.baseChange.finPart w) (hb : CharUnramifiedAt b.baseChange.finPart w)
    (hw : w.IsSplit) (hf : (S.hom T).projOn {w} f = f) (X : ℂ) :
    ∑ U : Submodule (ResField w) (n → ResField w),
        heckePolyCoeff X U • pairWeil S T a b ((1, ofSplitPlace hw (basicCosetRep U)⁻¹), 1, 1) f =
      schrodingerOp (S.hom T) {w}
        (residueDatum (fun () ↦ w) fun x : Unit → Matrix m n (ResField w) ↦
          qPochhammer w.q (card n - (x ()).rank) (X * b.frobValue m w))
        f :=
  (sum_heckePolyCoeff_smul_pairWeil ha hb hw hf X).right

/-- The Weil representation `New.pairWeil S T a b` restricted to the finite adelic points of the
unitary group of S. -/
noncomputable def pairWeilSource (S : Space E n s) (T : Space E m t) (a b : AutChar E) :
    Representation ℂ (Gf E n) (𝒮 (S.hom T)) :=
  ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp <| (pairWeil S T a b).comp <|
    (MonoidHom.inl (G E s) (G E t)).comp (MonoidHom.inr (GInf E s) (Gf E n))

/-- The Weil representation `New.pairWeil S T a b` restricted to the finite adelic points of the
unitary group of T. -/
noncomputable def pairWeilTarget (S : Space E n s) (T : Space E m t) (a b : AutChar E) :
    Representation ℂ (Gf E m) (𝒮 (S.hom T)) :=
  ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp <| (pairWeil S T a b).comp <|
    (MonoidHom.inr (G E s) (G E t)).comp (MonoidHom.inr (GInf E t) (Gf E m))

lemma pairWeilSource_apply (g : Gf E n) :
    pairWeilSource S T a b g f = pairWeil S T a b ((1, g), 1, 1) f :=
  rfl

lemma pairWeilTarget_apply (h : Gf E m) :
    pairWeilTarget S T a b h f = pairWeil S T a b ((1, 1), 1, h) f :=
  rfl

/-- Let S and T be hermitian spaces of ranks n and m = n + k, and let a, b be automorphic characters
whose base changes are unramified at the split place w of norm q. Let f in 𝒮(Hom(S, T)) be fixed by
`projOn {w}`. Then f is spherical at w for the Weil action `New.pairWeil` S T a b, (g, h) ↦ a(det h)
b(det g)⁻¹ ω(x ↦ hxg⁻¹), restricted to the finite unitary groups of T (`pairWeilTarget`) and of S
(`pairWeilSource`). Moreover P^T_w(X/α) f = ∏_{l<k}(1 − q^l X) · P^S_{w̄}(q^k X/β) f, where P is the
Hecke polynomial `New.heckePolyOp`, ∑_i (−X)^i q^(i choose 2) T_i, at w (for T) and at w̄ (for S).
Here α = `a.frobValue n w` and β = `b.frobValue m w`, where `c.frobValue N w` = χ(ϖ_w) q^{N/2} with
χ(x) = c(x/x̄) υ(x)^{−N}. -/
lemma heckePolyOp_pairWeilTarget (hk : card m = card n + k)
    (ha : CharUnramifiedAt a.baseChange.finPart w) (hb : CharUnramifiedAt b.baseChange.finPart w)
    (hw : w.IsSplit) (hf : (S.hom T).projOn {w} f = f) :
    f ∈ sphericalAt (pairWeilSource S T a b) w ∧
    f ∈ sphericalAt (pairWeilTarget S T a b) w ∧
    ∀ X : ℂ,
      heckePolyOp (pairWeilTarget S T a b) hw (X / a.frobValue n w) f =
        qPochhammer w.q k X •
          heckePolyOp (pairWeilSource S T a b) hw.star (w.q ^ k * X / b.frobValue m w) f := by
  -- The maximal compact groups fix the vacuum, as the characters are unramified.
  have ⟨source_sph, target_sph⟩ : f ∈ sphericalAt (pairWeilSource S T a b) w ∧
      f ∈ sphericalAt (pairWeilTarget S T a b) w := by
    simp [pairWeilSource_apply, pairWeilTarget_apply, ha, hb,
      pairWeil_eq_smul_of_projOn_eq {w} hf, det_maxCompactAt_eq_one _ hw]
  refine ⟨source_sph, target_sph, fun X ↦ ?_⟩
  -- By the two local identities both Hecke polynomials send `f` to a datum `N d Y`.
  let N (d : ℕ) (Y : ℂ) : 𝒮 (S.hom T) :=
    schrodingerOp (S.hom T) {w}
      (residueDatum (fun () ↦ w) fun x : Unit → Matrix m n (ResField w) ↦
        qPochhammer w.q (d - (x ()).rank) Y) f
  have hT (Y : ℂ) :
      heckePolyOp (pairWeilTarget S T a b) hw Y f = N (card m) (Y * a.frobValue n w) :=
    (heckePolyOp_eq_sum hw target_sph Y).left.trans
      (sum_heckePolyCoeff_smul_pairWeil_transposeGL ha hb hw hf Y)
  have hS (Y : ℂ) :
      heckePolyOp (pairWeilSource S T a b) hw.star Y f = N (card n) (Y * b.frobValue m w) :=
    (heckePolyOp_eq_sum hw source_sph Y).right.trans
      (sum_heckePolyCoeff_smul_pairWeil_inv ha hb hw hf Y)
  -- Modulo `w`, the kernel of `xᵀ` has `k` dimensions more than the kernel of `x`.
  have h_split (x : Matrix m n (ResField w)) :
      qPochhammer w.q (card m - x.rank) X =
        qPochhammer w.q k X * qPochhammer w.q (card n - x.rank) (w.q ^ k * X) := by
    rw [hk, add_comm (card n), Nat.add_sub_assoc x.rank_le_card_width, qPochhammer_add]
  have hα_ne : a.frobValue n w ≠ 0 := by simp [frobValue, atUniformizer]
  have hβ_ne : b.frobValue m w ≠ 0 := by simp [frobValue, atUniformizer]
  rw [hT, hS, div_mul_cancel₀ X hα_ne, div_mul_cancel₀ (w.q ^ k * X) hβ_ne, smul_schrodingerOp]
  congr! 2
  ext x
  simp only [residueDatum, h_split, Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero]

/-! ### Transfer through equivariant maps and lifts -/

/-- Hecke transfer through an equivariant map. Let w be split, let S have rank n and T rank
m = n + k, let a and b be unramified at w, and let f be a vacuum at w. Let Λ be linear with
Λ(ω(g,h)f) = π(g)ρ(h)Λf for all finite adelic g, h. Then Λf is K_w-fixed for π and ρ, and
P_w^ρ(X)Λf = ∏_{l<k}(1 − q^l αX)·P_{w̄}^π(q^k αβ⁻¹X)Λf, where P is the Hecke polynomial
`New.heckePolyOp`, q the norm of w, α = `a.frobValue n w` and β = `b.frobValue m w`. -/
lemma hecke_transfer_of_equivariant (hk : card m = card n + k)
    (ha : CharUnramifiedAt a.baseChange.finPart w) (hb : CharUnramifiedAt b.baseChange.finPart w)
    (hw : w.IsSplit) (hf : (S.hom T).projOn {w} f = f) (Λ : 𝒮 (S.hom T) →ₗ[ℂ] W)
    (π : Representation ℂ (Gf E n) W) (ρ : Representation ℂ (Gf E m) W)
    (hΛ : ∀ (g : Gf E n) (h : Gf E m), Λ (pairWeil S T a b ((1, g), 1, h) f) = π g (ρ h (Λ f))) :
    Λ f ∈ sphericalAt π w ∧
    Λ f ∈ sphericalAt ρ w ∧
    ∀ X : ℂ,
      heckePolyOp ρ hw X (Λ f) =
        qPochhammer w.q k (a.frobValue n w * X) •
          heckePolyOp π hw.star (w.q ^ k * a.frobValue n w / b.frobValue m w * X) (Λ f) := by
  -- Apply `Λ` to the identities of `heckePolyOp_pairWeilTarget` for the vacuum.
  obtain ⟨source_sph, target_sph, h_vacuum⟩ := heckePolyOp_pairWeilTarget hk ha hb hw hf
  have hπ (g : Gf E n) : π g (Λ f) = Λ (pairWeilSource S T a b g f) := by
    simp [pairWeilSource_apply, hΛ]
  have hρ (h : Gf E m) : ρ h (Λ f) = Λ (pairWeilTarget S T a b h f) := by
    simp [pairWeilTarget_apply, hΛ]
  have π_sph : Λ f ∈ sphericalAt π w := fun κ ↦ by rw [hπ, source_sph κ, map_smul]
  have ρ_sph : Λ f ∈ sphericalAt ρ w := fun κ ↦ by rw [hρ, target_sph κ, map_smul]
  refine ⟨π_sph, ρ_sph, fun X ↦ ?_⟩
  have hT (Y : ℂ) :
      heckePolyOp ρ hw Y (Λ f) = Λ (heckePolyOp (pairWeilTarget S T a b) hw Y f) := by
    simp only [heckePolyOp_eq_sum hw ρ_sph, heckePolyOp_eq_sum hw target_sph, hρ, map_sum, map_smul]
  have hS (Y : ℂ) :
      heckePolyOp π hw.star Y (Λ f) = Λ (heckePolyOp (pairWeilSource S T a b) hw.star Y f) := by
    simp only [heckePolyOp_eq_sum hw π_sph, heckePolyOp_eq_sum hw source_sph, hπ, map_sum, map_smul]
  have hα_ne : a.frobValue n w ≠ 0 := by simp [frobValue, atUniformizer]
  rw [hT, hS, ← map_smul, div_mul_eq_mul_div, mul_assoc, ← h_vacuum, mul_div_cancel_left₀ X hα_ne]

/-- Hecke transfer through a pairing. Let w be split of norm q, S of rank n, T of rank m = n + k, a,
b unramified at w, and f a vacuum at w. Let B be bilinear on M × W, where M is a space of data that
contains f, and suppose that for finite g, h the translate ω(g,h)f lies in M and
ρ(h)B(f,v) = B(ω(g,h)f, π(g)v). If v is K_w-fixed, then B(f,v) is K_w-fixed and
P_w^ρ(X) B(f,v) = ∏_{l<k}(1 − q^l αX) · B(f, P_w^π(q^k αβ⁻¹X) v), where P is the Hecke polynomial
`New.heckePolyOp`, α = `a.frobValue n w` and β = `b.frobValue m w` (`New.AutChar.frobValue`). -/
lemma hecke_transfer_of_pairing (hk : card m = card n + k)
    (ha : CharUnramifiedAt a.baseChange.finPart w) (hb : CharUnramifiedAt b.baseChange.finPart w)
    (hw : w.IsSplit) (hf : (S.hom T).projOn {w} f = f)
    {ρ : Representation ℂ (Gf E m) Z} {M : Submodule ℂ (𝒮 (S.hom T))} (B : M →ₗ[ℂ] W →ₗ[ℂ] Z)
    (hfM : f ∈ M)
    (hB : ∀ (g : Gf E n) (h : Gf E m) (v : W), ∃ Ψ : M,
      Ψ.val = pairWeil S T a b ((1, g), 1, h) f ∧ ρ h (B ⟨f, hfM⟩ v) = B Ψ (π g v))
    {v : W} (hv : v ∈ sphericalAt π w) :
    B ⟨f, hfM⟩ v ∈ sphericalAt ρ w ∧
    ∀ X : ℂ,
      heckePolyOp ρ hw X (B ⟨f, hfM⟩ v) =
        qPochhammer w.q k (a.frobValue n w * X) •
          B ⟨f, hfM⟩ (heckePolyOp π hw (w.q ^ k * a.frobValue n w / b.frobValue m w * X) v) := by
  -- The Hecke operators of `T` on `B f v`, and those of `S` on `v`, move to the datum `f`, the
  -- latter from `w` to `w̄`; there the identity for the vacuum applies. As `hB` is known only at
  -- `f`, extend `B` to all data and view it as a map into `W →ₗ[ℂ] Z`, on which `π` acts through
  -- the source and `ρ` through the target. By `hB` this map is equivariant at `f`.
  obtain ⟨B, rfl⟩ : ∃ B' : 𝒮 (S.hom T) →ₗ[ℂ] W →ₗ[ℂ] Z, B'.comp M.subtype = B := B.exists_extend
  have h_equiv (g : Gf E n) (h : Gf E m) :
      B (pairWeil S T a b ((1, g), 1, h) f) = π.linHom 1 g (Representation.linHom 1 ρ h (B f)) := by
    -- `hB` at `g`, `h`, with the datum `Ψ` replaced by its value.
    have h_pair (u : W) : ρ h (B f u) = B (pairWeil S T a b ((1, g), 1, h) f) (π g u) := by
      obtain ⟨Ψ, hΨ_val, hΨ_eq⟩ := hB g h u
      simpa [← hΨ_val] using hΨ_eq
    ext u
    simp [h_pair]
  obtain ⟨π_sph, ρ_sph, h_hecke⟩ :
      B f ∈ sphericalAt (π.linHom 1) w ∧ B f ∈ sphericalAt (Representation.linHom 1 ρ) w ∧
        ∀ X : ℂ, heckePolyOp (Representation.linHom 1 ρ) hw X (B f) =
          qPochhammer w.q k (a.frobValue n w * X) •
            heckePolyOp (π.linHom 1) hw.star (w.q ^ k * a.frobValue n w / b.frobValue m w * X)
              (B f) :=
    hecke_transfer_of_equivariant hk ha hb hw hf B (π.linHom 1) (Representation.linHom 1 ρ) h_equiv
  refine ⟨fun g ↦ LinearMap.congr_fun (ρ_sph g) v, fun X ↦ ?_⟩
  -- The adjoint of the Hecke polynomial of `π` at `w̄` is the one at `w`.
  have h_adjoint (Y : ℂ) :
      heckePolyOp (π.linHom 1) hw.star Y (B f) v = B f (heckePolyOp π hw Y v) :=
    (heckePolyOp_adjoint hw .applyₗ hv π_sph (by simp) Y).symm
  -- Evaluation at `v` commutes with the Hecke polynomial of `ρ`, which acts on the values only.
  calc heckePolyOp ρ hw X (B f v)
      = heckePolyOp (Representation.linHom 1 ρ) hw X (B f) v :=
        (map_heckePolyOp (LinearMap.applyₗ v) X (by simp)).symm
    _ = qPochhammer w.q k (a.frobValue n w * X) •
          B f (heckePolyOp π hw (w.q ^ k * a.frobValue n w / b.frobValue m w * X) v) := by
      rw [h_hecke, LinearMap.smul_apply, h_adjoint]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Hecke transfer through the transposed theta lift, which sends functions on the group of T to
functions on the group of S. Let w be split of norm q, S of rank n, T of rank m = n + k, and a, b
unramified at w̄. Let f be a vacuum at w̄, that is, fixed by the averaging operator `projOn {w̄}`
over integral vectors at w and w̄, and let y be automorphic of rapid decay on the group of T and,
for right translation `finRightRep` by the finite adelic group, K_w-fixed. Then the lift F of y is
K_w-fixed, and the lift of P_w(X) y is ∏_{l<k}(1 − q^l αX) · P_w(q^k αβ⁻¹X) F. Here
P_w(X) = ∑_{i ≤ rank} (−X)^i q^{i choose 2} T_{w,i} is `New.heckePolyOp`,
α = `a.frobValue n (star w)` and β = `b.frobValue m (star w)` (χ(ϖ_{w̄}) q^{N/2} for the Hecke
character χ attached to a, resp. b, in rank N = n, resp. m). -/
lemma lift_swap_heckePolyOp (hk : card m = card n + k) (hw : w.IsSplit)
    (ha : CharUnramifiedAt a.baseChange.finPart (star w))
    (hb : CharUnramifiedAt b.baseChange.finPart (star w))
    (hf : (S.hom T).projOn {star w} f = f) {y : G E t → ℂ} (hy_rapid : y ∈ T.rapidFunctions)
    (hy_sph : y ∈ sphericalAt (finRightRep E t) w) :
    lift (pairThetaKer S T a b).swap f y ∈ sphericalAt (finRightRep E s) w ∧
    ∀ X : ℂ,
      lift (pairThetaKer S T a b).swap f (heckePolyOp (finRightRep E t) hw X y) =
        qPochhammer w.q k (a.frobValue n (star w) * X) •
          heckePolyOp (finRightRep E s) hw
            (w.q ^ k * a.frobValue n (star w) / b.frobValue m (star w) * X)
            (lift (pairThetaKer S T a b).swap f y) := by
  -- The groups change roles. The Hecke polynomial of `T` moves from `y` to the datum `f`, from `w`
  -- to `star w`, where the identity for the vacuum turns it into the polynomial of `S` at `w`.
  set Θ : ThetaKernel (𝒮 (S.hom T)) T S := (pairThetaKer S T a b).swap
  let ρ : Representation ℂ (Gf E m) T.rapidFunctions.toSubmodule :=
    T.rapidFunctions.toRepresentation
  lift y to T.rapidFunctions.toSubmodule using hy_rapid
  -- The map `Θ.liftBilin` that sends a datum to the operator `y ↦ lift Θ f y` is equivariant.
  have h_equiv (g : Gf E n) (h : Gf E m) :
      Θ.liftBilin (pairWeil S T a b ((1, g), 1, h) f) =
        Representation.linHom 1 (finRightRep E s) g (ρ.linHom 1 h (Θ.liftBilin f)) := by
    ext ⟨v, hv_aut, hv_rapid⟩ x
    change lift Θ (Θ.ω ((1, h), (1, g)) f) v x =
      lift Θ f (fun u : G E t ↦ v (u * (1, h⁻¹))) (x * (1, g))
    rw [Θ.lift_equivariant (hv_aut.comp_mul_right (1, h⁻¹)) f (1, h) (1, g) x]
    simp [mul_assoc, Prod.mk_one_one]
  obtain ⟨h_source, h_target, h_transfer⟩ :=
    hecke_transfer_of_equivariant hk ha hb hw.star hf Θ.liftBilin
      (Representation.linHom 1 (finRightRep E s)) (ρ.linHom 1) h_equiv
  rw [sphericalAt, maxCompactAt, Gf.supportedOn_star] at h_source h_target
  have h_sph : Θ.liftBilin f y ∈ sphericalAt (finRightRep E s) w :=
    fun κ ↦ LinearMap.congr_fun (h_source κ) y
  refine ⟨h_sph, fun X ↦ ?_⟩
  set X' : ℂ := w.q ^ k * a.frobValue n (star w) / b.frobValue m (star w) * X
  have hy_sph' : y ∈ sphericalAt ρ w := fun κ ↦ Subtype.ext (hy_sph κ)
  have h_coe : heckePolyOp (finRightRep E t) hw X y = ↑(heckePolyOp ρ hw X y) :=
    (map_heckePolyOp (Submodule.subtype _) X fun _ _ ↦ rfl).symm
  -- Evaluation of an operator at a function is an invariant pairing.
  have h_adjoint : Θ.liftBilin f (heckePolyOp ρ hw X y) =
      heckePolyOp (ρ.linHom 1) hw.star X (Θ.liftBilin f) y :=
    heckePolyOp_adjoint hw .applyₗ hy_sph' h_target (by simp) X
  have h_vacuum : heckePolyOp (ρ.linHom 1) hw.star X (Θ.liftBilin f) =
      qPochhammer w.q k (a.frobValue n (star w) * X) •
        heckePolyOp (Representation.linHom 1 (finRightRep E s)) hw X' (Θ.liftBilin f) := by
    simpa [X'] using h_transfer X
  -- Evaluation at `y` commutes with the action of the group of `S` on the values.
  have h_eval : heckePolyOp (Representation.linHom 1 (finRightRep E s)) hw X' (Θ.liftBilin f) y =
      heckePolyOp (finRightRep E s) hw X' (Θ.liftBilin f y) :=
    map_heckePolyOp (.applyₗ y) X' (by simp)
  rw [h_coe]
  change Θ.liftBilin f (heckePolyOp ρ hw X y) =
    qPochhammer w.q k (a.frobValue n (star w) * X) •
      heckePolyOp (finRightRep E s) hw X' (Θ.liftBilin f y)
  rw [h_adjoint, h_vacuum, LinearMap.smul_apply, h_eval]

/-- Let S and T be hermitian spaces of ranks n and m = n + k, and let a, b be automorphic characters
whose base changes are unramified at the split place w of norm q. Let f in 𝒮(Hom(S, T)) be fixed by
`projOn {w}`, and let ω = `New.pairWeil` S T a b, (g, h) ↦ a(det h) b(det g)⁻¹ ω(x ↦ hxg⁻¹). Let B :
M × W → Z be bilinear, where M is a submodule containing f, with ω(g, h)f ∈ M and ρ(h)B(f,
v) = B(ω(g, h)f, π(g)v) for finite g, h. If v is spherical at w and each Hecke polynomial
`New.heckePolyOp`(X) acts on it by p(X), then B(f, v) is spherical at w with eigenvalue
∏_{l<k}(1 − q^l αX) · p(q^k αβ⁻¹X). Here α = `a.frobValue n w`, β = `b.frobValue m w`, and
`c.frobValue N w` = χ(ϖ_w) q^{N/2} with χ(x) = c(x/x̄) υ(x)^{−N}. -/
lemma hasHeckePolynomial_of_pairing (hk : card m = card n + k)
    (ha : CharUnramifiedAt a.baseChange.finPart w) (hb : CharUnramifiedAt b.baseChange.finPart w)
    (hw : w.IsSplit) (hf : (S.hom T).projOn {w} f = f)
    {ρ : Representation ℂ (Gf E m) Z} {M : Submodule ℂ (𝒮 (S.hom T))} (B : M →ₗ[ℂ] W →ₗ[ℂ] Z)
    (hfM : f ∈ M)
    (hB : ∀ (g : Gf E n) (h : Gf E m) (v : W), ∃ Ψ : M,
      Ψ.val = pairWeil S T a b ((1, g), 1, h) f ∧ ρ h (B ⟨f, hfM⟩ v) = B Ψ (π g v))
    {v : W} (hv : HasHeckePolynomial π hw p v) :
    HasHeckePolynomial ρ hw
      (fun X : ℂ ↦
        qPochhammer w.q k (a.frobValue n w * X) *
          p (w.q ^ k * a.frobValue n w / b.frobValue m w * X))
      (B ⟨f, hfM⟩ v) := by
  obtain ⟨hv_sph, hv_hecke⟩ := hv
  obtain ⟨h_sph, h_hecke⟩ := hecke_transfer_of_pairing hk ha hb hw hf B hfM hB hv_sph
  exact ⟨h_sph, by simpa [hv_hecke, mul_smul] using h_hecke⟩

/-- Let w be split with norm q, let S have rank n and T rank m = n + k, and let a and b be
unramified at w. Let f in 𝒮(Hom(S, T)) be fixed by P^{w} (`projOn {w}`) and be an arrow e → e'
(`New.IsArrow`) for the theta kernel `pairThetaKer S T a b`, where e, e' are functions on G_∞. If
the form y of type e is spherical at w with Hecke eigenvalue p(X), so is its lift `formLift … f y`
(the theta lift, a pairing of data and forms, equivariant for `formRep` because f is an arrow), with
eigenvalue ∏_{l<k}(1 − q^l αX)·p(q^k αβ⁻¹X), where α = `a.frobValue n w` and
β = `b.frobValue m w`. -/
lemma hasHeckePolynomial_formLift (hk : card m = card n + k)
    (ha : CharUnramifiedAt a.baseChange.finPart w) (hb : CharUnramifiedAt b.baseChange.finPart w)
    (hw : w.IsSplit) (hf : (S.hom T).projOn {w} f = f)
    {e : GInf E s → ℂ} {e' : GInf E t → ℂ} {y : S.Form e}
    (hA : IsArrow (pairThetaKer S T a b) e e' f) (hy : HasHeckePolynomial (S.formRep e) hw p y) :
    HasHeckePolynomial (T.formRep e') hw
      (fun X : ℂ ↦
        qPochhammer w.q k (a.frobValue n w * X) *
          p (w.q ^ k * a.frobValue n w / b.frobValue m w * X))
      (formLift (pairThetaKer S T a b) e e' f y) := by
  -- The theta lift is a pairing defined on all data, invariant by `IsArrow.formRep_formLift`.
  exact hasHeckePolynomial_of_pairing hk ha hb hw hf
    ((formLift (pairThetaKer S T a b) e e').domRestrict ⊤) Submodule.mem_top
    (by simp [← hA.formRep_formLift]) hy

end SiegelWeil

/-! ### The Hecke polynomial of a character -/

/-- Let w be a split place of norm q, and let ρ be a character of [U(1)] whose base change
x ↦ ρ(x/x̄) is unramified at w. A vector v on which the finite adelic unitary group of rank n acts
by g ↦ ρ(det g) is spherical at w, and the Hecke polynomial acts on it by ∏_{l<n}(1 − q^l cX), where
c is the value of the base change of ρ at the uniformiser of w. In rank one this is 1 − cX. -/
lemma SiegelWeil.hasHeckePolynomial_of_apply_eq_smul_det (hw : w.IsSplit) {s : n → ℤˣ}
    {ρ : AutChar E} (hρ : CharUnramifiedAt ρ.baseChange.finPart w) {v : W}
    (hv : ∀ g : Gf E n, π g v = (ρ.val (detFin s g) : ℂ) • v) :
    HasHeckePolynomial π hw
      (fun X : ℂ ↦ qPochhammer w.q (card n) (ρ.baseChange.atUniformizer w * X)) v := by
  -- The coset representative of `U` scales `v` by `c ^ dim U`, so the Hecke polynomial at `X` acts
  -- by the sum of its coefficients at `c * X`, which the `q`-binomial theorem evaluates.
  set c : ℂ := ρ.baseChange.atUniformizer w
  have h_sph : v ∈ sphericalAt π w := fun k ↦ by
    simp [hv, hρ.det_maxCompactAt_eq_one hw k.property]
  have h_rep (U : Submodule (ResField w) (n → ResField w)) :
      (ρ.val (detFin s (ofSplitPlace hw (transposeGL (basicCosetRep U)))) : ℂ) =
        c ^ Module.finrank (ResField w) U := by
    -- The determinant of the representative has order `dim U` at `w`.
    obtain ⟨⟨-, -, h_det⟩, -⟩ := basicCosetRep_mem_and_residueKer_eq U
    rw [detFin_of_mem_supportedOn, detOn_eq_prod, prod_singleton,
      ← AutChar.baseChange_apply_coe_toFun,
      hρ.apply_locFullIdele]
    · simp [h_det, c]
    · simp [hw]
    · simp
  have h_coeff (X : ℂ) (U : Submodule (ResField w) (n → ResField w)) :
      heckePolyCoeff X U * c ^ Module.finrank (ResField w) U = heckePolyCoeff (c * X) U := by
    rw [heckePolyCoeff, heckePolyCoeff, ← mul_neg, mul_pow]
    ring
  refine ⟨h_sph, fun X ↦ ?_⟩
  have h_binom :
      ∑ U : Submodule (ResField w) (n → ResField w), heckePolyCoeff (c * X) U =
        qPochhammer w.q (card n) (c * X) := by
    simpa [card_ResField] using q_binomial_submodule n (ResField w) ⊤ (c * X)
  calc heckePolyOp π hw X v
      = ∑ U : Submodule (ResField w) (n → ResField w),
          heckePolyCoeff X U • π (ofSplitPlace hw (transposeGL (basicCosetRep U))) v :=
        (heckePolyOp_eq_sum hw h_sph X).left
    _ = ∑ U : Submodule (ResField w) (n → ResField w), heckePolyCoeff (c * X) U • v := by
        simp only [hv, h_rep, smul_smul, h_coeff]
    _ = qPochhammer w.q (card n) (c * X) • v := by rw [← sum_smul, h_binom]

/-- At a split place w of norm q, a vector fixed by the finite adelic unitary group of rank n is
spherical, and the Hecke polynomial acts on it by ∏_{l<n}(1 − q^l X). -/
lemma SiegelWeil.hasHeckePolynomial_qPochhammer (hw : w.IsSplit) {v : W}
    (hv : ∀ g : Gf E n, π g v = v) :
    HasHeckePolynomial π hw (qPochhammer w.q (card n)) v := by
  simpa [atUniformizer] using
    hasHeckePolynomial_of_apply_eq_smul_det hw (ρ := 1) (s := 1) (fun u _ ↦ by simp)
      (by simpa using hv)

end Transfer

/-! ### A maximum principle -/

/-- Maximum principle. Let v be a real function bounded above, let finitely many a_i satisfy
∑|a_i| < l, and let l·v(g) ≤ ∑|a_i| v(r(g,i)) for all g. Then v ≤ 0. -/
lemma SiegelWeil.maximum_principle {G ι : Type*} [Fintype ι] {v : G → ℝ}
    (hv_bdd : BddAbove (Set.range v)) {l : ℝ} (a : ι → ℂ) (r : G → ι → G)
    (h_sum_lt : ∑ i : ι, ‖a i‖ < l) (h_le : ∀ g : G, l * v g ≤ ∑ i : ι, ‖a i‖ * v (r g i))
    (g : G) : v g ≤ 0 := by
  -- Taking the supremum over `g` gives `l * sup v ≤ (∑ i, ‖a i‖) * sup v`, so `sup v ≤ 0`.
  have : Nonempty G := ⟨g⟩
  have hl_nonneg : 0 ≤ l := le_trans (by positivity) h_sum_lt.le
  have h_sup : l * ⨆ g, v g ≤ (∑ i, ‖a i‖) * ⨆ g, v g := by
    rw [Real.mul_iSup_of_nonneg hl_nonneg]
    refine ciSup_le fun g ↦ ?_
    grw [h_le g, le_ciSup hv_bdd, ← sum_mul]
  nlinarith [le_ciSup hv_bdd g]

end New
