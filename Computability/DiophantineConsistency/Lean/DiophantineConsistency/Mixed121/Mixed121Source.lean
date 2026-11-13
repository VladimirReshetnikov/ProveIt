import DiophantineConsistency.Mixed121.Mixed121Clean
import DiophantineConsistency.Compact44.CyclicPhaseTransport
import DiophantineConsistency.Compact44.CyclicAnyPhase

/-! # Safe temporal sources at the 121x8801 ports

This is the 121x8801 counterpart of Compact44's `CleanPhaseChoice`,
`CleanTargetPhase`, `CleanPhaseNeighbors` and `CleanSafeSource`, with the
Mixed121 hull `Mixed121Clean.Bad`. The accepted proof bodies are kept. Only the
period `8807` becomes `8801`, and the width `67` becomes `121`. The two clause
targets still differ by `1102`, and both contain the safe cells' predecessors
`1064` and `1065`.

`graph_safe_sources` is the counterpart of
`FixedGraphSafeSource.graph_safe_sources_facts`. For every temporal phase
`D`, one of the two clause targets gives a cell `k` with `C_k = 0`, and its
two cyclic predecessors are Boolean. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Source
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open ArithmeticStandardCasts Mixed121Clean
open CompactHeterogeneousCarry CompactGenericAlignedMass Mixed121Rotation Mixed121Flatten
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem choose_phase (x : V) (hx : x<8801) :
    ¬Bad x ∨ ¬Bad ((x+1102)%8801) := by
  by_cases h : Bad x
  · right
    intro hy
    exact model_disjoint x hx ⟨h,hy⟩
  · exact Or.inl h

theorem choose_shifted (q : V) :
    ¬Bad (cyc 8801 4393 q) ∨ ¬Bad ((cyc 8801 4393 q+1102)%8801) :=
  choose_phase _ (cyc_lt (by norm_num) _ _)

theorem outside_exceptions (x : V) (h : ¬Bad x) :
    x≠1063 ∧ x≠1064 ∧ x≠1065 := by
  constructor
  · intro hx; apply h; left; rw [hx]; all_goals norm_num
  constructor
  · intro hx; apply h; left; rw [hx]; all_goals norm_num
  · intro hx; apply h; left; exact le_of_eq hx

private theorem cast_sub (a b : ℕ) (h : b≤a) : ((a-b:ℕ):V)=(a:V)-(b:V) := by
  apply eq_tsub_of_add_eq
  exact_mod_cast (Nat.sub_add_cancel h)

private theorem cyc_cast (t q : ℕ) :
    cyc (8801:V) (t:V) (q:V) = (((t+8801-q%8801)%8801:ℕ):V) := by
  have hle : q%8801≤t+8801 := by have := Nat.mod_lt q (by omega : 0<8801); omega
  have hc : ((t+8801-q%8801:ℕ):V)=(t:V)+8801-((q%8801:ℕ):V) := by
    rw [cast_sub _ _ hle, Nat.cast_add]; simp only [Nat.cast_ofNat]
  have hm : (q:V)%8801 = ((q%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) q 8801).symm
  unfold cyc
  rw [hm, ←hc]
  simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) (t+8801-q%8801) 8801).symm

theorem finite_relation (q : ℕ) :
    (5495+8801-q%8801)%8801 = (((4393+8801-q%8801)%8801)+1102)%8801 := by
  have := Nat.mod_lt q (by omega : 0<8801)
  omega

theorem target_relation (q : V) :
    cyc 8801 5495 q = (cyc 8801 4393 q+1102)%8801 := by
  have hq : q%8801<8801 := mod_lt _ (by norm_num)
  obtain ⟨j,hj,hjv⟩ := CleanGeometry.bounded_standard 8801 (q%8801) hq
  rw [←cyc_mod 8801 5495 q (by norm_num), ←cyc_mod 8801 4393 q (by norm_num), hjv]
  have hc1 : cyc (8801:V) 5495 (j:V) = (((5495+8801-j%8801)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cyc_cast (V:=V) 5495 j)
  have hc2 : cyc (8801:V) 4393 (j:V) = (((4393+8801-j%8801)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cyc_cast (V:=V) 4393 j)
  rw [hc1,hc2]
  have h := congrArg (fun n : ℕ => (n:V)) (finite_relation j)
  simpa only [cast_mod, Nat.cast_add, Nat.cast_ofNat] using h

theorem target_choice (q : V) :
    ¬Bad (cyc 8801 4393 q) ∨ ¬Bad (cyc 8801 5495 q) := by
  rw [target_relation]
  exact choose_shifted q

theorem finite_neighbors (j : ℕ) (hj : j<8801) (hb : ¬BadNat j) :
    (j+8801-1)%8801≠1063 ∧ (j+8801-2)%8801≠1063 := by
  unfold BadNat at hb
  omega

theorem model_neighbors (x : V) (hx : x<8801) (hb : ¬Bad x) :
    cyc 8801 x 1≠1063 ∧ cyc 8801 x 2≠1063 := by
  obtain ⟨j,hj,hjv⟩ := CleanGeometry.bounded_standard 8801 x hx
  have hb' : ¬BadNat j := by intro h; apply hb; rw [hjv,bad_cast]; exact h
  have hn := finite_neighbors j hj hb'
  have hc1 : cyc (8801:V) (j:V) 1 = (((j+8801-1)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat, Nat.cast_one, Nat.reduceMod] using (cyc_cast (V:=V) j 1)
  have hc2 : cyc (8801:V) (j:V) 2 = (((j+8801-2)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat, Nat.cast_one, Nat.reduceMod] using (cyc_cast (V:=V) j 2)
  rw [hjv,hc1,hc2]
  constructor
  · intro he
    apply hn.1
    exact_mod_cast he
  · intro he
    apply hn.2
    exact_mod_cast he

theorem safe_source (N C k : V) (hN : 0<N) (hk : k<8801*N) (hsafe : ¬Bad (k%8801))
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0)
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1) :
    dig 121 C k=0 ∧ dig 121 C (cyc (8801*N) k 1)≤1 ∧
      dig 121 C (cyc (8801*N) k 2)≤1 := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  have hp := model_neighbors (k%8801) (mod_lt _ (by norm_num)) hsafe
  refine ⟨hzero k hk hsafe, ?_, ?_⟩
  · apply hbool _ (cyc_lt hn _ _)
    rw [CyclicPhaseTransport.cyc_period 8801 N k 1 (by norm_num) hN (by norm_num)]
    exact hp.1
  · apply hbool _ (cyc_lt hn _ _)
    rw [CyclicPhaseTransport.cyc_period 8801 N k 2 (by norm_num) hN (by norm_num)]
    exact hp.2

theorem choose_source (N C q k₁ k₂ : V) (hN : 0<N)
    (hk₁ : k₁<8801*N) (hk₂ : k₂<8801*N)
    (hphase₁ : k₁%8801=cyc 8801 4393 q) (hphase₂ : k₂%8801=cyc 8801 5495 q)
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0)
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1) :
    ∃ k, (k=k₁ ∨ k=k₂) ∧ k<8801*N ∧ dig 121 C k=0 ∧
      dig 121 C (cyc (8801*N) k 1)≤1 ∧ dig 121 C (cyc (8801*N) k 2)≤1 := by
  rcases target_choice q with h₁ | h₂
  · have hs : ¬Bad (k₁%8801) := by rw [hphase₁]; exact h₁
    exact ⟨k₁,Or.inl rfl,hk₁,safe_source N C k₁ hN hk₁ hs hzero hbool⟩
  · have hs : ¬Bad (k₂%8801) := by rw [hphase₂]; exact h₂
    exact ⟨k₂,Or.inr rfl,hk₂,safe_source N C k₂ hN hk₂ hs hzero hbool⟩

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

theorem graph_safe_sources (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
        (coefficient (fun x => (alignedCoeff selectors copies x : V)))
        (word 121 (8801*N) C bandOffsets
          (Mixed121Temporal.temporalWord (8801*N) (R-121*(8801*N)) C)) ∧
      (∀ D : V, ∃ k, (k=cyc (8801*N) 4393 D ∨ k=cyc (8801*N) 5495 D) ∧
         k<8801*N ∧ dig 121 C k=0 ∧
         dig 121 C (cyc (8801*N) k 1)≤1 ∧ dig 121 C (cyc (8801*N) k 2)≤1) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,h0,hzero,hbool⟩ :=
    Mixed121Clean.graph_support_carry v hv hz
  dsimp only at *
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,?_⟩
  intro D
  let k₁ := cyc (8801*N) 4393 D
  let k₂ := cyc (8801*N) 5495 D
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  have hp₁ : k₁%8801=cyc 8801 4393 D := by
    dsimp [k₁]
    rw [CyclicAnyPhase.cyc_period 8801 N 4393 D (by norm_num) hN,
      mod_eq_self_of_lt (by norm_num : (4393:V)<8801)]
  have hp₂ : k₂%8801=cyc 8801 5495 D := by
    dsimp [k₂]
    rw [CyclicAnyPhase.cyc_period 8801 N 5495 D (by norm_num) hN,
      mod_eq_self_of_lt (by norm_num : (5495:V)<8801)]
  exact choose_source N _ D k₁ k₂ hN (cyc_lt hn _ _) (cyc_lt hn _ _) hp₁ hp₂ hzero hbool
end Mixed121Source
#print axioms Mixed121Source.target_choice
#print axioms Mixed121Source.model_neighbors
#print axioms Mixed121Source.choose_source
#print axioms Mixed121Source.graph_safe_sources
