import DiophantineConsistency.PRAWitnessFixpointGraph
/-! # Witness bounds for Foundation's vector graphs

`nth` is defined by a fixpoint over triples `⟪v, i, x⟫` whose stage is an
unbounded witness. Its construction queries `⟪sndIdx v, i, x⟫` for
`⟪v, i + 1, x⟫`, a strictly smaller triple, so it is rank-finite for the
identity rank (`nth_rankFinite`; Foundation only records `Finite`), and every
element appears by stage `x + 1`. The core is bounded throughout, so
`PRAWitnessFixpointGraph.wb_fixpointDef` gives witness bounds for `Nth.graphDef`
in every candidate-PRA model, and the triple witness of `nthDef` is bounded
by its components. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessVectors
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic

section sigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `nth` queries strictly smaller triples. -/
theorem nth_rankFinite : PRAFixpointRank.RankFinite (Nth.adjointruction (V := V)) (fun x => x) := by
  rintro v C x (h | ⟨w, i, y, rfl, hC⟩)
  · exact Or.inl h
  · refine Or.inr ⟨w, i, y, rfl, hC, ?_⟩
    exact lt_of_le_of_lt (pair_le_pair_left (sndIdx_le_self w) _)
      (pair_lt_pair_right w (pair_lt_pair_left (lt_add_one i) y))

instance idDefinable : 𝚺₁-Function₁ (fun x : V => x) := by definability

/-- A vector recursion whose step does not decrease the value queries strictly
smaller pairs. -/
theorem vecRec_rankFinite {β : VecRec.Blueprint 0} (c : VecRec.Construction V β)
    (hadj : ∀ x xs ih, ih ≤ c.adjoin ![] x xs ih) :
    PRAFixpointRank.RankFinite c.adjointruction (fun x => x) := by
  rintro v C pr (h | ⟨x, xs, ih, rfl, hC⟩)
  · exact Or.inl h
  · refine Or.inr ⟨x, xs, ih, rfl, hC, ?_⟩
    have hv : v = ![] := funext fun i => i.elim0
    subst hv
    exact lt_of_le_of_lt (pair_le_pair_right xs (hadj x xs ih)) (pair_lt_pair_left (lt_adjoin' x xs) _)

end sigma1

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_nth_core_sigma : WB M Nth.blueprint.core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_fstIdxDef (M := M); have := wb_sndIdxDef (M := M); have := wb_pair₃Def (M := M)
  have := wb_bitDef (M := M)
  simp only [Nth.blueprint, HierarchySymbol.Semiformula.ofZero,
    HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_nth_core_neg_pi : WB M (∼Nth.blueprint.core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_neg_fstIdxDef (M := M); have := wb_neg_sndIdxDef (M := M)
  have := wb_neg_pair₃Def (M := M); have := wb_neg_bitDef (M := M)
  have := wb_fstIdxDef (M := M); have := wb_sndIdxDef (M := M); have := wb_pair₃Def (M := M)
  have := wb_bitDef (M := M)
  simp only [Nth.blueprint, HierarchySymbol.Semiformula.ofZero,
    HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi,
    HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

/-- **`nth`'s graph has bounded witnesses.** -/
theorem wb_nth_graph : WB M Nth.graphDef.val := by
  refine PRAWitnessFixpointGraph.wb_fixpointDef Nth.blueprint wb_nth_core_sigma wb_nth_core_neg_pi
    ‘#0 + 1’ ?_
  intro V _ _ e s L hL hx
  have h := PRAWitnessFixpointGraph.stage_bound_of_rank (Nth.adjointruction (V := V)) (fun x => x)
    (fun _ => le_rfl) nth_rankFinite (fun x => x + 1) (fun _ => le_rfl) (fun i => e i.succ) (e 0)
    s L hL hx
  exact ⟨_, by simpa using h.1, h.2⟩

/-- The polynomial dominating a triple code `⟪a, b, c⟫` (context `c :> a :> b`). -/
noncomputable def triplePoly : ArithmeticSemiterm Empty 3 :=
  ‘(#1 + (#2 + #0 + 1) * (#2 + #0 + 1) + 1) * (#1 + (#2 + #0 + 1) * (#2 + #0 + 1) + 1)’

omit [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem pair3_le_triplePoly [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (a b c : M) :
    ⟪a, b, c⟫ ≤ triplePoly.val ![c, a, b] Empty.elim := by
  have h1 : ⟪b, c⟫ ≤ (b + c + 1) * (b + c + 1) := by simpa [sq] using pair_polybound b c
  have h2 : ⟪a, ⟪b, c⟫⟫ ≤ (a + ⟪b, c⟫ + 1) * (a + ⟪b, c⟫ + 1) := by simpa [sq] using pair_polybound a ⟪b, c⟫
  have h3 : a + ⟪b, c⟫ + 1 ≤ a + (b + c + 1) * (b + c + 1) + 1 := by
    simpa [add_assoc] using add_le_add_left (add_le_add_right h1 1) a
  simpa [triplePoly] using le_trans h2 (mul_le_mul' h3 h3)

/-- **`nthDef` has bounded witnesses.** -/
theorem wb_nthDef : WB M nthDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hg := wb_nth_graph (M := M)
  have := wb_pair₃Def (M := M)
  simp only [nthDef, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_term triplePoly (fun e pr hpr => ?_) (by wb_auto)
  have he : e = ![e 0, e 1, e 2] := by
    funext j; revert j; simp [Fin.forall_fin_succ]
  rw [he] at hpr ⊢
  set y := e 0
  set v := e 1
  set i := e 2
  have hpr' : pr = ⟪v, i, y⟫ := by
    have h := hpr
    simp at h
    exact h.1
  rw [hpr']
  exact pair3_le_triplePoly v i y

/-! ### Length -/

private theorem wb_len_core (neg : Bool) :
    WB M (if neg then ∼Len.blueprint.blueprint.core.pi.val
      else Len.blueprint.blueprint.core.sigma.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_pairDef (M := M); have := wb_adjoinDef (M := M); have := wb_memRel (M := M)
  have := wb_neg_pairDef (M := M); have := wb_neg_memRel (M := M)
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  have : WB M (∼memRelOpr.sentence) := wb_neg_memRel (M := M)
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    simp only [VecRec.Blueprint.blueprint, Len.blueprint, HierarchySymbol.Semiformula.sigma_mkDelta,
      HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi,
      HierarchySymbol.Semiformula.val_mkSigma]
    wb_auto
    · exact wb_exs_term ‘0’ (fun e y h => by simp at h; simp [h.1]) (by wb_auto)
    · refine wb_exs_term ‘(#2 + #1 + 1) * (#2 + #1 + 1) + 1’ (fun e y h => ?_) ?_
      · simp [adjoinDef] at h
        rw [h.1.2]
        have hp : ⟪e 2, e 1⟫ ≤ (e 2 + e 1 + 1) * (e 2 + e 1 + 1) := by
          simpa [sq] using pair_polybound (e 2) (e 1)
        simpa using add_le_add_right hp 1
      · refine wb_and (by wb_auto) (wb_exs_term ‘#1 + 1’ (fun e y h => by simp at h; simp [h.1]) (by wb_auto))

theorem wb_len_core_sigma : WB M Len.blueprint.blueprint.core.sigma.val := by
  simpa using wb_len_core (M := M) false

theorem wb_len_core_neg_pi : WB M (∼Len.blueprint.blueprint.core.pi.val) := by
  simpa using wb_len_core (M := M) true

/-- **`len`'s graph has bounded witnesses.** -/
theorem wb_len_graph : WB M Len.blueprint.graphDef.val := by
  refine PRAWitnessFixpointGraph.wb_fixpointDef Len.blueprint.blueprint wb_len_core_sigma
    wb_len_core_neg_pi ‘#0 + 1’ ?_
  intro V _ _ e s L hL hx
  have h := PRAWitnessFixpointGraph.stage_bound_of_rank (Len.adjointruction (V := V)).adjointruction
    (fun x => x) (fun _ => le_rfl)
    (vecRec_rankFinite Len.adjointruction (fun _ _ ih => le_of_lt (lt_add_one ih)))
    (fun x => x + 1) (fun _ => le_rfl) (fun i => e i.succ) (e 0) s L hL hx
  exact ⟨_, by simpa using h.1, h.2⟩

/-- **`lenDef` has bounded witnesses.** -/
theorem wb_lenDef : WB M lenDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hg := wb_len_graph (M := M); have := wb_pairDef (M := M)
  simp only [lenDef, VecRec.Blueprint.resultDef, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_term ‘(#1 + #0 + 1) * (#1 + #0 + 1)’ (fun e y h => ?_) (by wb_auto)
  simp at h
  rw [h.1]
  simpa [sq] using pair_polybound (e 1) (e 0)

end models
end DiophantineConsistency.PRAWitnessVectors
