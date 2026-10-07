/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
import OAI.Combinatorics.Progressions.Linear.HomogeneousLieSpan
import OAI.Combinatorics.Progressions.Linear.MarkedLieSpan

namespace OAI

section

namespace Erdos3.FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x) (marked : X → Bool)

noncomputable def markedLayer (d k l : ℕ) : Submodule ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  markedLieSpan (of X s r w hw) w marked d k l

theorem markedLayer_antitone {d e k m l n : ℕ} (hde : d ≤ e) (hkm : k ≤ m) (hln : l ≤ n) :
    markedLayer X s r w hw marked e m n ≤ markedLayer X s r w hw marked d k l :=
  markedLieSpan_antitone _ _ _ hde hkm hln

theorem markedLayer_lie_mem {d e k m l n : ℕ} {x y : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ markedLayer X s r w hw marked d k l)
    (hy : y ∈ markedLayer X s r w hw marked e m n) :
    ⁅x, y⁆ ∈ markedLayer X s r w hw marked (d + e) (k + m) (l + n) :=
  markedLieSpan_lie_mem _ _ _ hx hy

theorem markedLayer_zero : markedLayer X s r w hw marked 0 0 0 = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := projection_surjective X s r w hw x
  obtain ⟨z, rfl⟩ := FreeNilpotentLieAlgebra.mk_surjective X s y
  let φ := (projection X s r w hw).comp (FreeNilpotentLieAlgebra.mk X s)
  change φ z ∈ markedLayer X s r w hw marked 0 0 0
  apply freeLie_linear_induction (fun z => φ z ∈ markedLayer X s r w hw marked 0 0 0)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro c a ha
    rw [map_smul]
    exact Submodule.smul_mem _ c ha
  · intro a
    rw [map_lieTreeEval]
    change lieTreeEval (of X s r w hw) a ∈ markedLayer X s r w hw marked 0 0 0
    exact Submodule.subset_span ⟨a, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩

noncomputable def markedLayerIdeal (d k l : ℕ) : LieIdeal ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  { markedLayer X s r w hw marked d k l with
    lie_mem := by
      intro x y hy
      have hx : x ∈ markedLayer X s r w hw marked 0 0 0 := by
        rw [markedLayer_zero]
        trivial
      change ⁅x, y⁆ ∈ markedLayer X s r w hw marked d k l
      simpa only [Nat.zero_add] using markedLayer_lie_mem X s r w hw marked hx hy }

theorem markedLayer_le_degreeRank (hr : r ≤ s) (d k l : ℕ) :
    markedLayer X s r w hw marked d k l ≤ (filtration X s r w hw hr).layer d l :=
  markedLieSpan_le_layer (filtration X s r w hw hr) _ _ _
    (of_mem_layer X s r w hw hr) d k l

theorem markedLayer_marked_terminal (hr : r ≤ s) (d l : ℕ) :
    markedLayer X s r w hw marked d (s + 1) l = ⊥ :=
  markedLieSpan_marked_terminal (filtration X s r w hw hr) _ _ _ hw
    (of_mem_layer X s r w hw hr) d l

theorem markedLayer_degree_terminal (hr : r ≤ s) (k l : ℕ) :
    markedLayer X s r w hw marked (s + 1) k l = ⊥ := by
  apply bot_unique
  exact (markedLayer_le_degreeRank X s r w hw marked hr (s + 1) k l).trans
    ((filtration X s r w hw hr).layer_eq_bot_of_past_top (Or.inl (by omega))).le

theorem of_mem_markedLayer (x : X) :
    of X s r w hw x ∈ markedLayer X s r w hw marked (w x) (if marked x then 1 else 0) 1 :=
  markedLieSpan_leaf _ _ _ x

end Erdos3.FreeDegreeRankLieAlgebra

end

section

namespace Erdos3.FreeDegreeRankLieAlgebra

open VectorPolynomial

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (hr : r ≤ s) {σ : Type*} (g : X → σ →₀ ℕ)

noncomputable def gradingHom :
    FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆
      VectorPolynomial σ ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  lift ((filtration X s r w hw hr).polynomialFiltration (σ := σ)) w hw
    (fun x => monomial (g x) (of X s r w hw x)) (fun x => by
      apply (filtration X s r w hw hr).monomial_mem_polynomialFiltration
      rw [(filtration X s r w hw hr).rank_zero_eq_one]
      exact of_mem_layer X s r w hw hr x)

@[simp] theorem gradingHom_of (x : X) :
    gradingHom X s r w hw hr g (of X s r w hw x) = monomial (g x) (of X s r w hw x) := by
  simp only [gradingHom, lift_of]

theorem gradingHom_tree (a : FreeMagma X) :
    gradingHom X s r w hw hr g (lieTreeEval (of X s r w hw) a) =
      monomial (lieTreeMultidegree g a) (lieTreeEval (of X s r w hw) a) := by
  induction a using FreeMagma.rec with
  | of x => exact gradingHom_of X s r w hw hr g x
  | mul a b ha hb =>
    change gradingHom X s r w hw hr g
      ⁅lieTreeEval (of X s r w hw) a, lieTreeEval (of X s r w hw) b⁆ = _
    rw [LieHom.map_lie, ha, hb, lie_monomial]
    rfl

theorem gradingHom_eval_one (x : FreeDegreeRankLieAlgebra X s r w hw) :
    eval (fun _ : σ => (1 : ℚ)) (gradingHom X s r w hw hr g x) = x := by
  have h : (evalLie (fun _ : σ => (1 : ℚ))).comp (gradingHom X s r w hw hr g) =
      (LieHom.id : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw) := by
    apply hom_ext w hw
    intro y
    change eval (fun _ : σ => (1 : ℚ)) (gradingHom X s r w hw hr g (of X s r w hw y)) = _
    rw [gradingHom_of]
    simp
  exact LieHom.congr_fun h x

theorem gradingHom_injective : Function.Injective (gradingHom X s r w hw hr g) := by
  intro x y h
  have he := congrArg (eval (fun _ : σ => (1 : ℚ))) h
  simpa only [gradingHom_eval_one] using he

noncomputable def gradingExpansion : LieGradingExpansion (of X s r w hw) g where
  expand := (gradingHom X s r w hw hr g).toLinearMap
  expand_tree := gradingHom_tree X s r w hw hr g
  eval_one := gradingHom_eval_one X s r w hw hr g

include hr in
theorem homogeneousSpan_inter (S T : Set (σ →₀ ℕ)) :
    homogeneousLieSpan (of X s r w hw) g (S ∩ T) =
      homogeneousLieSpan (of X s r w hw) g S ⊓ homogeneousLieSpan (of X s r w hw) g T :=
  (gradingExpansion X s r w hw hr g).span_inter S T

end Erdos3.FreeDegreeRankLieAlgebra

end

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem NilpotentLieFiltration.top_rank_map_mem_degreeLengthSpan {s k : ℕ}
    (F : NilpotentLieFiltration L s) (φ : L →ₗ⁅ℚ⁆ M) (v : X → M) (w : X → ℕ)
    (hspan : ∀ d, 0 < d → ∀ x ∈ F.layer d, φ x ∈ weightedLieDegreeLengthSpan v w d 1)
    {x : L} (hx : x ∈ F.rankLayer s k) :
    φ x ∈ weightedLieDegreeLengthSpan v w s k := by
  rw [NilpotentLieFiltration.rankLayer, F.terminal, bot_sup_eq] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hkl, a, rfl⟩ := hx
    exact weightedLieDegreeLengthSpan_antitone v w le_rfl hkl
      (a.map_eval_mem_degreeLengthSpan φ v w hspan)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem FreeWeightedNilpotentLieAlgebra.lift_layer_mem_degreeLengthSpan {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : X → ℕ) (hw : ∀ i, 0 < w i)
    (f : X → L) (hf : ∀ i, f i ∈ F.layer (w i))
    {d : ℕ} {x : FreeWeightedNilpotentLieAlgebra X s w}
    (hx : x ∈ (filtration X s w hw).layer d) :
    lift F w f hf x ∈ weightedLieDegreeLengthSpan f w d 1 := by
  obtain ⟨a, ha, rfl⟩ := hx
  change FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot a ∈
    weightedLieDegreeLengthSpan f w d 1
  have h := weightedLieUpperSpan_map_le_degreeLengthSpan
    (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot)
    (FreeNilpotentLieAlgebra.of X s) w d ⟨a, ha, rfl⟩
  change FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot a ∈
    weightedLieDegreeLengthSpan
      (fun i => FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot
        (FreeNilpotentLieAlgebra.of X s i)) w d 1 at h
  have heq : (fun i => FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot
      (FreeNilpotentLieAlgebra.of X s i)) = f :=
    funext (fun i => FreeNilpotentLieAlgebra.lift_of f F.lowerCentralSeries_eq_bot i)
  rw [heq] at h
  exact h

theorem FreeDegreeRankLieAlgebra.lift_top_mem_degreeLengthSpan {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ i, 0 < w i)
    (f : X → L) (hf : ∀ i, f i ∈ F.layer (w i) 0)
    {x : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ (filtration X s r w hw F.rank_le_degree).layer s r) :
    lift F w hw f hf x ∈ weightedLieDegreeLengthSpan f w s r := by
  obtain ⟨a, ha, rfl⟩ := hx
  change FreeWeightedNilpotentLieAlgebra.lift F.associatedDegree w f hf a ∈
    weightedLieDegreeLengthSpan f w s r
  exact (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).top_rank_map_mem_degreeLengthSpan
    (FreeWeightedNilpotentLieAlgebra.lift F.associatedDegree w f hf) f w
    (fun _ _ _ h => FreeWeightedNilpotentLieAlgebra.lift_layer_mem_degreeLengthSpan
      F.associatedDegree w hw f hf h) ha

theorem FreeDegreeRankLieAlgebra.lift_top_frequency_zero
    {A : Type*} [AddCommGroup A] [Module ℚ A] {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ i, 0 < w i)
    (f : X → L) (hf : ∀ i, f i ∈ F.layer (w i) 0) (η : L →ₗ[ℚ] A)
    (hzero : ∀ a : FreeMagma X, lieTreeWeight w a = s → a.length = r → η (lieTreeEval f a) = 0)
    {x : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ (filtration X s r w hw F.rank_le_degree).layer s r) :
    η (lift F w hw f hf x) = 0 := by
  exact weightedLieDegreeLengthSpan_top_le_ker F f w
    (fun i => by rw [← F.rank_zero_eq_one]; exact hf i) η hzero
    (lift_top_mem_degreeLengthSpan F w hw f hf hx)

end Erdos3

end

section

namespace Erdos3

def markedGradeRegion (d k l : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {α | d ≤ α 0 ∧ k ≤ α 1 ∧ l ≤ α 2}

theorem markedGradeRegion_inter (d k l e m n : ℕ) :
    markedGradeRegion (max d e) (max k m) (max l n) =
      markedGradeRegion d k l ∩ markedGradeRegion e m n := by
  ext α
  simp only [markedGradeRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, max_le_iff]
  tauto

namespace FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (marked : X → Bool)

theorem markedLayer_eq_homogeneousSpan (d k l : ℕ) :
    markedLayer X s r w hw marked d k l =
      homogeneousLieSpan (of X s r w hw) (markedGeneratorGrade w marked) (markedGradeRegion d k l) := by
  unfold markedLayer markedLieSpan homogeneousLieSpan
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, markedGradeRegion, markedTreeGrade_weight,
    markedTreeGrade_count, markedTreeGrade_length, and_assoc]

theorem markedLayer_inf (hr : r ≤ s) (d k l e m n : ℕ) :
    markedLayer X s r w hw marked d k l ⊓ markedLayer X s r w hw marked e m n =
      markedLayer X s r w hw marked (max d e) (max k m) (max l n) := by
  rw [markedLayer_eq_homogeneousSpan, markedLayer_eq_homogeneousSpan,
    markedLayer_eq_homogeneousSpan, markedGradeRegion_inter,
    homogeneousSpan_inter X s r w hw hr]

theorem markedLayer_separate_inter (hr : r ≤ s) (d k l : ℕ) :
    markedLayer X s r w hw marked d 0 l ⊓ markedLayer X s r w hw marked 0 k 0 =
      markedLayer X s r w hw marked d k l := by
  rw [markedLayer_inf X s r w hw marked hr]
  simp only [Nat.max_zero, Nat.zero_max]

theorem topLayer_eq_markedLayer (hr : r ≤ s) :
    (filtration X s r w hw hr).layer s r = markedLayer X s r w hw marked s 0 r := by
  apply le_antisymm
  · intro x hx
    change x ∈ markedLieSpan (of X s r w hw) w marked s 0 r
    rw [markedLieSpan_zero_marked]
    let F := filtration X s r w hw hr
    have hf (i : X) : of X s r w hw i ∈ F.layer (w i) 0 := by
      rw [F.rank_zero_eq_one]
      exact of_mem_layer X s r w hw hr i
    have hid : lift F w hw (of X s r w hw) hf =
        (LieHom.id : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw) := by
      apply hom_ext w hw
      intro i
      rw [lift_of]
      rfl
    have h := lift_top_mem_degreeLengthSpan F w hw (of X s r w hw) hf hx
    simpa only [hid, LieHom.id_apply] using h
  · exact markedLayer_le_degreeRank X s r w hw marked hr s 0 r

theorem topLayer_inter_markedIdeal (hr : r ≤ s) (k : ℕ) :
    (filtration X s r w hw hr).layer s r ⊓ (markedLayerIdeal X s r w hw marked 0 k 0).toSubmodule =
      markedLayer X s r w hw marked s k r := by
  change (filtration X s r w hw hr).layer s r ⊓ markedLayer X s r w hw marked 0 k 0 = _
  rw [topLayer_eq_markedLayer X s r w hw marked hr,
    markedLayer_separate_inter X s r w hw marked hr]

end FreeDegreeRankLieAlgebra
end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

def coefficientLayerIndex : D.CoefficientAlphabet → Fin s := Sum.elim (fun x => x.1) (fun x => x.1)

def coefficientIsDependent : D.CoefficientAlphabet → Bool := Sum.elim (fun _ => false) (fun _ => true)

theorem coefficientWeight_eq_layerIndex (x : D.CoefficientAlphabet) :
    D.coefficientWeight x = (D.coefficientLayerIndex x).val + 1 := by
  cases x <;> rfl

theorem coefficientFreeGenerator_mem_combined (x : D.CoefficientAlphabet) :
    D.coefficientFreeGenerator x ∈ D.coefficientFreeSpan (D.coefficientLayerIndex x) := by
  cases x with
  | inl x => exact D.commonFreeSpan_le_coefficientFreeSpan x.1 (Submodule.subset_span ⟨x.2, rfl⟩)
  | inr x => exact D.dependentFreeSpan_le_coefficientFreeSpan x.1 (Submodule.subset_span ⟨x.2, rfl⟩)

theorem coefficientFreeGenerator_mem_dependent (x : D.CoefficientAlphabet)
    (hx : D.coefficientIsDependent x = true) :
    D.coefficientFreeGenerator x ∈ D.dependentFreeSpan (D.coefficientLayerIndex x) := by
  cases x with
  | inl x => cases hx
  | inr x => exact Submodule.subset_span ⟨x.2, rfl⟩

noncomputable def dependentWordLayer (d k l : ℕ) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra.markedLayer D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos D.coefficientIsDependent d k l

noncomputable def dependentWordIdeal (d k l : ℕ) : LieIdeal ℚ D.CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra.markedLayerIdeal D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos D.coefficientIsDependent d k l

theorem dependentWordLayer_zero : D.dependentWordLayer 0 0 0 = ⊤ :=
  FreeDegreeRankLieAlgebra.markedLayer_zero _ _ _ _ _ _

theorem dependentWordLayer_antitone {d e k m l n : ℕ} (hde : d ≤ e) (hkm : k ≤ m) (hln : l ≤ n) :
    D.dependentWordLayer e m n ≤ D.dependentWordLayer d k l :=
  markedLieSpan_antitone _ _ _ hde hkm hln

theorem dependentWordLayer_lie_mem {d e k m l n : ℕ} {x y : D.CoefficientFreeLieAlgebra}
    (hx : x ∈ D.dependentWordLayer d k l) (hy : y ∈ D.dependentWordLayer e m n) :
    ⁅x, y⁆ ∈ D.dependentWordLayer (d + e) (k + m) (l + n) :=
  markedLieSpan_lie_mem _ _ _ hx hy

theorem dependentWordLayer_le_degreeRank (d k l : ℕ) :
    D.dependentWordLayer d k l ≤ D.coefficientFreeFiltration.layer d l :=
  markedLieSpan_le_layer D.coefficientFreeFiltration _ _ _
    D.coefficientFreeGenerator_mem_layer d k l

theorem dependentWordLayer_marked_terminal (d l : ℕ) :
    D.dependentWordLayer d (s + 1) l = ⊥ :=
  markedLieSpan_marked_terminal D.coefficientFreeFiltration _ _ _
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer d l

theorem commonFreeSpan_le_dependentWordLayer (d : Fin s) :
    D.commonFreeSpan d ≤ D.dependentWordLayer (d.val + 1) 0 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact markedLieSpan_leaf D.coefficientFreeGenerator D.coefficientWeight
    D.coefficientIsDependent (Sum.inl ⟨d, i⟩)

theorem dependentFreeSpan_le_dependentWordLayer (d : Fin s) :
    D.dependentFreeSpan d ≤ D.dependentWordLayer (d.val + 1) 1 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact markedLieSpan_leaf D.coefficientFreeGenerator D.coefficientWeight
    D.coefficientIsDependent (Sum.inr ⟨d, i⟩)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
