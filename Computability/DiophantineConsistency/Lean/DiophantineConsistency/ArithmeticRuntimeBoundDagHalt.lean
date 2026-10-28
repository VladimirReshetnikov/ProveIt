import DiophantineConsistency.ArithmeticRuntimeBoundDagRootC
import DiophantineConsistency.ArithmeticEnumBoundSoundness
import BusyBeaver.ZFC.ArithmeticDagRuntimePerm222

/-! # Enumerator halt ⇒ DagPerm halt within an explicit elementary bound

Every configuration of the actual enumerator up to internal time `n` is below
`tower (100*n) 8` (`ArithmeticEnumBoundSoundness`), so its DagPerm boundary record
has register mass below `tower (100*n) 9`, and one root execution costs at most
`T = tower (100*n) (9+KR) = 2^(2^(100*n+23609))` control steps
(`ArithmeticRuntimeBoundDagMacros.root_stepB`). A Σ1 induction over enumerator
time carries a control clock at most `m*T`; at the halting time `n` the related
pair is impossible, so the DagPerm seed has halted by `n*T`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticRuntimeBoundDagHalt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticDagMacrosPerm222
open ArithmeticDagRootPerm222 (boundary)
open ArithmeticEnumBoundTower ArithmeticRuntimeBoundDagMacros
open DiophantineConsistency.ArithmeticCommandStepPerm222 (stateValue)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The explicit DagPerm clock bound `n * 2^(2^(100*n+23609))`. -/
noncomputable def Bdag (n : V) : V := n * Exp.exp (Exp.exp (100 * n + 23609))

theorem tower_KR (n : V) : tower (100 * n) (9 + KR) = Exp.exp (Exp.exp (100 * n + 23609)) := by
  simp only [tower, KR, KC, KAX]
  norm_num

theorem boundary_sz_le (pl np t S d h : V) :
    sz (boundary pl np t S d h) ≤
      ArithmeticEnumStepPerm222.liveValue pl np (stateValue t S d h) * 6 + 0 := by
  set l := ArithmeticEnumStepPerm222.liveValue pl np (stateValue t S d h)
  have hw : stateValue t S d h ≤ cantor pl (cantor np (stateValue t S d h)) :=
    le_trans (components_le np _).2 (components_le pl _).2
  have hl : cantor pl (cantor np (stateValue t S d h)) ≤ l := le_self_add
  have hwl : stateValue t S d h ≤ l := le_trans hw hl
  have hpl : pl ≤ l := le_trans (components_le pl _).1 hl
  have hnp : np ≤ l := le_trans (le_trans (components_le np _).1 (components_le pl _).2) hl
  have ht : t ≤ l := le_trans (components_le t _).1 hwl
  have hS : S ≤ l := le_trans (le_trans (components_le S _).1 (components_le t _).2) hwl
  have hd : d ≤ l := le_trans (le_trans (components_le d h).1
    (le_trans (components_le S _).2 (components_le t _).2)) hwl
  have hh : h ≤ l := le_trans (le_trans (components_le d h).2
    (le_trans (components_le S _).2 (components_le t _).2)) hwl
  calc sz (boundary pl np t S d h) = np + t + S + d + h + pl := by
        simp only [sz, boundary]; ring
    _ ≤ l + l + l + l + l + l := _root_.add_le_add (_root_.add_le_add (_root_.add_le_add
        (_root_.add_le_add (_root_.add_le_add hnp ht) hS) hd) hh) hpl
    _ = l * 6 + 0 := by ring

/-- **Enumerator halt ⇒ DagPerm halt, with an explicit clock.** -/
theorem dag_halts_le_of_enum_halts (n : V)
    (hn : ArithmeticEnumRunPerm222.run n (ArithmeticEnumStepPerm222.liveValue 0 4 0) = 0) :
    ∃ ta ≤ Bdag n, ArithmeticDagControlPerm222.run ta (ArithmeticControlFile.liveValue 1
      (ArithmeticControlFile.fileValue ![0,0,0,0,0,0,4,0,0])) = 0 := by
  obtain ⟨T, hT⟩ : ∃ T : V, T = tower (100 * n) (9 + KR) := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : V, I = ArithmeticEnumStepPerm222.liveValue 0 4 0 := ⟨_, rfl⟩
  obtain ⟨C0, hC0⟩ : ∃ C0 : V, C0 = ArithmeticDagRuntimePerm222.controlOf 0 4 0 0 0 0 := ⟨_, rfl⟩
  have hwork : stateValue (0 : V) 0 0 0 = 0 := by simp [stateValue, cantor, triangle]
  have hconf : ∀ m, m ≤ n → ArithmeticEnumRunPerm222.run m I ≤ tower (100 * n) 8 := by
    intro m hm
    have hg := ArithmeticEnumBoundSoundness.good_run m _ ArithmeticEnumBoundSoundness.good_initial
    rw [← hI] at hg
    refine le_trans hg.1 ?_
    rw [ArithmeticEnumBoundSoundness.soundBound_eq]
    exact tower_base_mono (mul_le_mul_of_nonneg_left hm (Arithmetic.zero_le 100)) 8
  have hstep : ∀ m, m < n → ∀ b, ArithmeticDagRuntimePerm222.Related
      (ArithmeticEnumRunPerm222.run m I) b →
      (∃ k ≤ T, ArithmeticDagControlPerm222.run k b = 0) ∨
      ∃ k ≤ T, ArithmeticDagRuntimePerm222.Related (ArithmeticEnumRunPerm222.run (m+1) I)
        (ArithmeticDagControlPerm222.run k b) := by
    intro m hm b hr
    obtain ⟨pl, np, t, S, d, h, hl, rfl⟩ := hr
    have hl8 : ArithmeticEnumStepPerm222.liveValue pl np (stateValue t S d h) ≤
        tower (100 * n) 8 := hl ▸ hconf m (le_of_lt hm)
    have hs : sz (boundary pl np t S d h) ≤ tower (100 * n) 9 :=
      le_trans (boundary_sz_le pl np t S d h)
        (lin_le' (by norm_num) hl8 (by norm_num) (by norm_num))
    rcases root_stepB (L := 9) (by norm_num) pl np t S d h hs with
      ⟨_, y, hy⟩ | ⟨pl', np', t', S', d', h', he, hrn, _⟩
    · obtain ⟨k, hk, hk0⟩ := root_reach_haltB hy
      exact Or.inl ⟨k, by rw [hT]; exact hk, hk0⟩
    · obtain ⟨k, hk, hkr⟩ := root_reach_normalB hrn
      refine Or.inr ⟨k, by rw [hT]; exact hk, pl', np', t', S', d', h', ?_, hkr⟩
      rw [ArithmeticEnumRunPerm222.run_succ, hl, he]
  have clocks : ∀ m, m ≤ n → ∃ c ≤ m * T,
      ArithmeticDagRuntimePerm222.Related (ArithmeticEnumRunPerm222.run m I)
        (ArithmeticDagControlPerm222.run c C0) ∨ ArithmeticDagControlPerm222.run c C0 = 0 := by
    intro m
    induction m using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      intro _
      refine ⟨0, by simp, .inl ?_⟩
      rw [ArithmeticEnumRunPerm222.run_zero, ArithmeticDagControlPerm222.run_zero, hI, hC0]
      exact ⟨0, 4, 0, 0, 0, 0, by rw [hwork], rfl⟩
    case succ m ih =>
      intro hm1
      have hmn : m < n := lt_of_lt_of_le (lt_add_one m) hm1
      obtain ⟨c, hc, hq⟩ := ih (le_of_lt hmn)
      have hcT : ∀ k, k ≤ T → c + k ≤ (m+1) * T := fun k hk => by
        rw [add_mul, one_mul]; exact _root_.add_le_add hc hk
      rcases hq with hr | h0
      · rcases hstep m hmn _ hr with ⟨k, hk, hk0⟩ | ⟨k, hk, hk'⟩
        · exact ⟨c + k, hcT k hk, .inr (by rw [ArithmeticDagControlPerm222.run_add, hk0])⟩
        · exact ⟨c + k, hcT k hk, .inl (by rw [ArithmeticDagControlPerm222.run_add]; exact hk')⟩
      · exact ⟨c, le_trans (le_trans hc (by rw [add_mul, one_mul]; exact le_self_add)) le_rfl,
          .inr h0⟩
  obtain ⟨c, hc, hq⟩ := clocks n le_rfl
  have hz : ArithmeticDagControlPerm222.run c C0 = 0 := by
    rcases hq with hr | h0
    · rw [← hI] at hn
      exact absurd hn (ArithmeticDagRuntimePerm222.related_live hr)
    · exact h0
  have hseed : C0 = ArithmeticControlFile.liveValue 1
      (ArithmeticControlFile.fileValue ![0,0,0,0,0,0,4,0,0]) := by
    rw [hC0]
    simp only [ArithmeticDagRuntimePerm222.controlOf, ArithmeticDagRuntimePerm222.enc_boundary]
  refine ⟨c, ?_, by rw [← hseed]; exact hz⟩
  rw [Bdag, ← tower_KR, ← hT]
  exact hc

end DiophantineConsistency.ArithmeticRuntimeBoundDagHalt
