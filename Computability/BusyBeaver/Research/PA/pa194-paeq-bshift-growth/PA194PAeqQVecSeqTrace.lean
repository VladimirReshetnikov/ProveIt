import PA194PAeqQVecGrowth

/-! Coded qVec histories exist at all model-internal lengths in IΣ₁.
These are HFS sequences, distinct from the HFS vectors used for terms. -/
set_option autoImplicit false
namespace PA194PAeqQVecSeqTrace
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out seed. out = seed”
noncomputable def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index seed. !(qVecGraph PA194PAeq.language) out previous”
noncomputable def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero p := p 0
  succ _ _ previous := qVec PA194PAeq.language previous
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

def boundSuccDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index seed. ∃ d, !exponentialDef (22 * previous + 22) d ∧
    !exponentialDef ((previous + 8 + 4) * d) out”
def boundBlueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := boundSuccDef

noncomputable def boundConstruction : PR.Construction V boundBlueprint where
  zero p := p 0
  succ _ _ previous := PRAWitnessCodeGrowth.tau (previous + 8) (22 * previous + 22)
  zero_defined := .mk fun e => by simp [boundBlueprint, zeroDef]
  succ_defined := .mk fun e => by simp [boundBlueprint, boundSuccDef, PRAWitnessCodeGrowth.tau, ← exponential_graph, numeral_eq_natCast]

theorem exists_bound_trace (seed limit : V) :
    ∃ s : V, (boundConstruction (V := V)).CSeq ![seed] s ∧ limit + 1 = lh s :=
  PR.Construction.CSeq.exists _ _ _

theorem exists_trace (seed limit : V) :
    ∃ s : V, (construction (V := V)).CSeq ![seed] s ∧ limit + 1 = lh s :=
  PR.Construction.CSeq.exists _ _ _

theorem trace_start (seed s : V) (h : (construction (V := V)).CSeq ![seed] s) :
    znth s 0 = seed := by
  have hm := h.zero
  have hm' : ⟪(0 : V), seed⟫ ∈ s := by simpa [construction] using hm
  exact h.seq.znth_eq_of_mem hm'

theorem trace_step (seed limit s i : V) (h : (construction (V := V)).CSeq ![seed] s)
    (hl : limit + 1 = lh s) (hi : i < limit) :
    znth s (i + 1) = qVec PA194PAeq.language (znth s i) := by
  have hlt : i < lh s := by rw [← hl]; exact lt_trans hi (by simp)
  have hm := h.succ i (by simp [← hl, hi]) (znth s i) (h.seq.znth hlt)
  have hm' : ⟪i + 1, qVec PA194PAeq.language (znth s i)⟫ ∈ s := by simpa [construction] using hm
  exact h.seq.znth_eq_of_mem hm'

theorem bound_start (seed s : V) (h : (boundConstruction (V := V)).CSeq ![seed] s) :
    znth s 0 = seed := by
  have hm := h.zero
  have hm' : ⟪(0 : V), seed⟫ ∈ s := by simpa [boundConstruction] using hm
  exact h.seq.znth_eq_of_mem hm'

theorem bound_step (seed limit s i : V) (h : (boundConstruction (V := V)).CSeq ![seed] s)
    (hl : limit + 1 = lh s) (hi : i < limit) :
    znth s (i + 1) = PRAWitnessCodeGrowth.tau (znth s i + 8) (22 * znth s i + 22) := by
  have hlt : i < lh s := by rw [← hl]; exact lt_trans hi (by simp)
  have hm := h.succ i (by simp [← hl, hi]) (znth s i) (h.seq.znth hlt)
  have hm' : ⟪i + 1, PRAWitnessCodeGrowth.tau (znth s i + 8) (22 * znth s i + 22)⟫ ∈ s := by
    simpa [boundConstruction] using hm
  exact h.seq.znth_eq_of_mem hm'

theorem trace_bounded (seed limit qs bs : V)
    (hq : (construction (V := V)).CSeq ![seed] qs)
    (hb : (boundConstruction (V := V)).CSeq ![seed] bs)
    (hlq : limit + 1 = lh qs) (hlb : limit + 1 = lh bs) :
    ∀ i ≤ limit, znth qs i ≤ znth bs i := by
  intro i
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _
    simp [trace_start seed qs hq, bound_start seed bs hb]
  case succ i ih =>
    intro hi
    have hlt : i < limit := lt_iff_succ_le.mpr hi
    have hprev := ih (le_trans le_self_add hi)
    rw [trace_step seed limit qs i hq hlq hlt, bound_step seed limit bs i hb hlb hlt]
    exact le_trans (PA194PAeqQVecGrowth.qVec_le (znth qs i))
      (PRAWitnessCodeGrowth.tau_mono (add_le_add hprev le_rfl)
        (add_le_add (mul_le_mul' le_rfl hprev) le_rfl))

/-- The internal qVec iterate is bounded by the internal majorant iterate,
including at nonstandard model indices. -/
theorem result_bound (seed limit : V) :
    (construction (V := V)).result ![seed] limit ≤
      (boundConstruction (V := V)).result ![seed] limit := by
  obtain ⟨qs, hq, hlq⟩ := exists_trace seed limit
  obtain ⟨bs, hb, hlb⟩ := exists_bound_trace seed limit
  have hqmem := hq.seq.znth (show limit < lh qs by rw [← hlq]; simp)
  have hbmem := hb.seq.znth (show limit < lh bs by rw [← hlb]; simp)
  have heq : znth qs limit = (construction (V := V)).result ![seed] limit :=
    ((construction (V := V)).result_graph ![seed] _ _).mpr ⟨qs, hq, hqmem⟩
  have heb : znth bs limit = (boundConstruction (V := V)).result ![seed] limit :=
    ((boundConstruction (V := V)).result_graph ![seed] _ _).mpr ⟨bs, hb, hbmem⟩
  simpa [heq, heb] using trace_bounded seed limit qs bs hq hb hlq hlb limit le_rfl

#print axioms result_bound
#print axioms exists_trace
#print axioms exists_bound_trace
#print axioms trace_bounded
end PA194PAeqQVecSeqTrace
