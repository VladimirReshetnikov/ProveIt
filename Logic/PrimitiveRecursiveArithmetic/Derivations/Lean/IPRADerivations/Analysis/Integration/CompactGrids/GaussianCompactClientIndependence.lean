import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence

/-!
# Original compact names for locally equivalent evaluator clients

Both original evaluator clients have their own legitimate modulus and
top budget. A local same-time agreement concerns only their unchanged
point evaluators. The original meshes refine to their actual product;
finite sums and the actual quadrature weight compare the two clients
there. Genuine regularity then removes the fixed observation envelope.
No equality or equivalence of compact outputs is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactClientIndependence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (inside evaluatorName nameData evaluator_at grid grid_inside sampleBody sampleData
  sample_body_at quadrature sample mesh precision)
open GaussianCompactMeshIndependence (commonPrecision arbitrary_refinement)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def agreementBody (F G : PR 3) (a C E x y t : PTm n) : Fm PTm n :=
  inside a C E t ⟶ crossEquivalent (evaluatorName F) (evaluatorName G) (nameData t x) (nameData t y)
def localAgreement (F G : PR 3) (a C E x y : PTm n) : Fm PTm n := .all
  (agreementBody F G (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift x) (Syn.shift y) (var 0))
def input (F G : PR 3) (a C E L T M S x y : PTm n) : Fm PTm n :=
  GaussianCompactRiemannName.input F a C E L T x ⋏
    (GaussianCompactRiemannName.input G a C E M S y ⋏ localAgreement F G a C E x y)

@[simp] theorem subst_agreementBody {m : ℕ} (σ : Fin n → PTm m) (F G : PR 3) (a C E x y t : PTm n) :
    (agreementBody F G a C E x y t).subst σ = agreementBody F G (Syn.subst σ a) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ t) := by simp [agreementBody]
@[simp] theorem subst_localAgreement {m : ℕ} (σ : Fin n → PTm m) (F G : PR 3) (a C E x y : PTm n) :
    (localAgreement F G a C E x y).subst σ = localAgreement F G (Syn.subst σ a) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ x) (Syn.subst σ y) := by
  simp [localAgreement,Syn.subst_shift,Syn.shift_subst,Syn.up]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (F G : PR 3) (a C E L T M S x y : PTm n) :
    (input F G a C E L T M S x y).subst σ = input F G (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E)
      (Syn.subst σ L) (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ S) (Syn.subst σ x) (Syn.subst σ y) := by simp [input]

theorem agreement_at (F G : PR 3) (a C E x y p q t : PTm n)
    (h : Γ ⊢[PRAAx] localAgreement F G a C E x y) (ht : Γ ⊢[PRAAx] inside a C E t) : Γ ⊢[PRAAx]
    distanceBounded (ap3 F p t x) (ap3 G q t y) (unit p+unit q) (unit p*unit q) := by
  have rule : Γ ⊢[PRAAx] agreementBody F G a C E x y t := by
    simpa only [localAgreement,subst_agreementBody,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE t
  exact distance_congr (evaluator_at F p t x) (evaluator_at G q t y) (.eqRefl _) (.eqRefl _)
    (cross_at _ _ _ _ p q (rule.impE ht))

theorem client_cell (F G : PR 3) (i p q N a C E x y : PTm n)
    (h : Γ ⊢[PRAAx] localAgreement F G a C E x y) (ha : Γ ⊢[PRAAx] le one a)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (sampleBody F) i (sampleData p N a C E x))
      (inst2 (sampleBody G) i (sampleData q N a C E y)) (unit p+unit q) (unit p*unit q) :=
  distance_congr (sample_body_at F i p N a C E x).eqSymm (sample_body_at G i q N a C E y).eqSymm
    (.eqRefl _) (.eqRefl _) (agreement_at F G a C E x y p q (grid i N a C E) h
      (grid_inside i N a C E ha hE hN (le_of_lt hi)))

private theorem weighted_distance (f g : PTm 2) (N x y C E A D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.termsDistance f g N x y A D) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRationalRiemannRefinement.leftSum f N x C E)
      (GaussianRationalRiemannRefinement.leftSum g N y C E) (C*A) (E*D) := by
  have en := positive_product E N hE hN
  have raw := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ en hD
    (GaussianRationalRiemannRefinement.weight_bound C E N hE hN)
    (GaussianRationalRiemannRefinement.sum_distance f g N x y A D hD h)
  have old := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (GaussianRationalRiemannRefinement.weight C E N) _ _).eqSymm
    (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ en hD) (positive_product _ _ hE hD)
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) old

theorem quadrature_distance (F G : PR 3) (p q N a C E x y : PTm n)
    (h : Γ ⊢[PRAAx] localAgreement F G a C E x y) (ha : Γ ⊢[PRAAx] le one a)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F p N a C E x) (quadrature G q N a C E y)
      (C*(unit p+unit q)) (E*(unit p*unit q)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] localAgreement F G (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift x) (Syn.shift y) :=
    by simpa only [Fm.shift,Syn.shift,subst_localAgreement] using h.shift
  have as : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using ha.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have cells : Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.termsDistance (sampleBody F) (sampleBody G) N
      (sampleData p N a C E x) (sampleData q N a C E y) (unit p+unit q) (unit p*unit q) := by
    refine .allI (.impI ?_)
    simpa only [GaussianRationalRiemannRefinement.termsDistance,GaussianCompactRiemannName.subst_sampleData,
      GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul,Syn.shift] using
      client_cell F G (var 0) (Syn.shift p) (Syn.shift q) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift x) (Syn.shift y) hs.wk as.wk es.wk ns.wk Prf.hyp0
  exact weighted_distance (sampleBody F) (sampleBody G) N _ _ C E _ _ hN hE
    (positive_product _ _ (unit_positive p) (unit_positive q)) cells

theorem sample_distance (F G : PR 3) (p a C E L T M S x y : PTm n)
    (h : Γ ⊢[PRAAx] input F G a C E L T M S x y) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a C E L T x) (sample G p a C E M S y) (num 8) (unit (p+num 6)) := by
  let Q := commonPrecision p T S
  let N := mesh p L T*mesh p M S
  let K := unit (p+num 6)
  let V := unit Q
  have hK := unit_positive (Γ := Γ) (p+num 6)
  have hV := unit_positive (Γ := Γ) Q
  have hE := h.andE₁.andE₂.andE₁
  have nL := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p L T
  have nR := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p M S
  have left := distance_congr (GaussianCompactRiemannName.quadrature_index_congr F Q
    (mesh p M S*mesh p L T) N a C E x (by dsimp only [N]; ipra_ring)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (arbitrary_refinement F p Q (mesh p M S) a C E L T x h.andE₁ nR (le_add_right _ _))
  have right := arbitrary_refinement G p Q (mesh p L T) a C E M S y h.andE₂.andE₁ nL (le_add_left _ _)
  have raw := quadrature_distance F G Q Q N a C E x y h.andE₂.andE₂ h.andE₁.andE₁ hE (positive_product _ _ nL nR)
  have later := GaussianCompactRiemannName.dyadic_monotone (Γ := Γ) (precision p T) Q (le_add_right _ _)
  have budget : Γ ⊢[PRAAx] le (K*T) V := le_trans (GaussianCompactRiemannName.precision_lower p T) later
  have width : Γ ⊢[PRAAx] le (C*K) (E*V) :=
    le_trans (mul_le_mul_right K h.andE₁.andE₂.andE₂.andE₁)
      (le_congr (by ipra_ring) (mul_comm _ _) (mul_le_mul_right E budget))
  have middle : Γ ⊢[PRAAx] distanceBounded (quadrature F Q N a C E x) (quadrature G Q N a C E y) two K :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE (positive_product _ _ hV hV)) hK
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*V) width)) raw
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ (quadrature F Q N a C E x) _ _ _ K hK (distance_symmetric _ _ _ _ hK left)
      (distance_triangle_same _ (quadrature G Q N a C E y) _ _ _ K hK middle right))

theorem diagonal_distance (F G : PR 3) (p a C E L T M S x y : PTm n)
    (h : Γ ⊢[PRAAx] input F G a C E L T M S x y) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a C E L T x) (sample G p a C E M S y) (num 8) (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _)
    (le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (num 8) (GaussianCompactRiemannName.dyadic_monotone p (p+num 6) (le_add_right _ _))))
    (sample_distance F G p a C E L T M S x y h)

theorem name_independence (F G : PR 3) (a C E L T M S x y : PTm n)
    (h : Γ ⊢[PRAAx] input F G a C E L T M S x y) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF G)
      (GaussianCompactRiemannName.data a C E L T x) (GaussianCompactRiemannName.data a C E M S y) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 8)
    (GaussianCompactRiemannName.name_regular F a C E L T x h.andE₁)
    (GaussianCompactRiemannName.name_regular G a C E M S y h.andE₂.andE₁)
  have hs : Γ.map Fm.shift ⊢[PRAAx] input F G (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L)
      (Syn.shift T) (Syn.shift M) (Syn.shift S) (Syn.shift x) (Syn.shift y) :=
    by simpa only [Fm.shift,Syn.shift,subst_input] using h.shift
  refine .allI ?_
  have raw := diagonal_distance F G (var 0) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L)
    (Syn.shift T) (Syn.shift M) (Syn.shift S) (Syn.shift x) (Syn.shift y) hs
  have actual := distance_congr (GaussianCompactRiemannName.name_at F (var 0) _ _ _ _ _ _).eqSymm
    (GaussianCompactRiemannName.name_at G (var 0) _ _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) raw
  simpa only [GaussianCompactRiemannName.subst_data,PTm.subst_num,Syn.shift] using actual

theorem actual_original_compact_client_independence_closed (F G : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (input F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        crossEquivalent (GaussianCompactRiemannName.nameF F) (GaussianCompactRiemannName.nameF G)
          (GaussianCompactRiemannName.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 7))
          (GaussianCompactRiemannName.data (var 0) (var 1) (var 2) (var 5) (var 6) (var 8))) :=
  closeUniv 9 (.impI (name_independence F G _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactClientIndependence
