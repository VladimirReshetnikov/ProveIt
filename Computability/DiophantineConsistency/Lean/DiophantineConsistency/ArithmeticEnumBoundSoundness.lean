import DiophantineConsistency.ArithmeticEnumBoundTower
import DiophantineConsistency.ArithmeticEnumSoundnessPerm222

/-! # Halting enumerator ⇒ a refutation below an explicit two-level tower

`ArithmeticEnumSoundnessPerm222` carries an existential certificate bound
`CertifiedWorking w = ∃ B, WorkingB B w` through the run. Here the same actual
command effects are re-certified with an explicit bound: if the configuration
code and the certificate bound are both below `tower j n`, one enumerator step
keeps both below `tower j (n+100)`. Hence at internal time `time` the whole
configuration and every accepted proof witness on its stack are below
`2^(2^(100*time+8))`, and a halt at `time` exposes an accepted C222 refutation
code below that bound. The run, checker and halting predicate are the actual
represented ones; no existing statement is changed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticEnumBoundSoundness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticCode254
open ArithmeticHistory222 (value value_defined_delta)
open ArithmeticProofConstructors222 ArithmeticStackCertificate222
open ArithmeticCommandPreservationPerm222 ArithmeticCommandStepPerm222
open ArithmeticCommandWordPerm222 (first_le second_le second2_le tail_le)
open ArithmeticEnumStepPerm222 ArithmeticEnumRunPerm222
open ArithmeticEnumBoundTower
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho8)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Size of codes -/

theorem cantor_le_tower_of {x y j : V} {m m' : ℕ} (hm : 2 ≤ m') (hmm : m ≤ m')
    (hx : x ≤ tower j m) (hy : y ≤ tower j m') : cantor x y ≤ tower j (m'+2) :=
  cantor_le_tower hm (le_tower_of hx hmm) hy

theorem stateValue_le {t s d h j : V} {m : ℕ} (hm : 2 ≤ m)
    (ht : t ≤ tower j m) (hs : s ≤ tower j m) (hd : d ≤ tower j m) (hh : h ≤ tower j m) :
    stateValue t s d h ≤ tower j (m+6) := by
  have h1 := cantor_le_tower hm hd hh
  have h2 := cantor_le_tower_of (by omega) (by omega) hs h1
  exact cantor_le_tower_of (by omega) (by omega) ht h2

theorem template_le (e : ArithmeticTemplates254.Circuit) (hd : depth e ≤ 20)
    {a b c u j : V} {m : ℕ} (hm : 2 ≤ m) (ha : a ≤ tower j m) (hb : b ≤ tower j m)
    (hc : c ≤ tower j m) (hu : u ≤ tower j m) : e.eval a b c u ≤ tower j (m+60) :=
  le_tower_of (eval_le_tower e hm ha hb hc hu) (by omega)

theorem tagged0_le {x y j : V} {m : ℕ} (hm : 2 ≤ m) (k : V) (hk : k ≤ 3)
    (hx : x ≤ tower j m) (hy : y ≤ tower j m) : tagged k x y ≤ tower j (m+3) :=
  tagged_le_tower hm hk hx hy

theorem rho1_le {a b j : V} {m : ℕ} (hm : 2 ≤ m) (ha : a ≤ tower j m) (hb : b ≤ tower j m) :
    rho1 a b ≤ tower j (m+60) := by
  have h1 : (1 : V) ≤ tower j m := one_le_tower j m
  have e1 : weq a b ≤ tower j (m+3) := tagged_le_tower hm (by norm_num) ha hb
  have e2 : wim (weq a b) 1 ≤ tower j (m+6) :=
    tagged_le_tower (by omega) (by norm_num) e1 (le_tower_of h1 (by omega))
  have e3 : wal a (wim (weq a b) 1) ≤ tower j (m+9) :=
    tagged_le_tower (by omega) (by norm_num) (le_tower_of ha (by omega)) e2
  have e4 : rho1 a b ≤ tower j (m+12) :=
    tagged_le_tower (by omega) (by norm_num) e3 (le_tower_of h1 (by omega))
  exact le_tower_of e4 (by omega)

theorem gate_le {a b c j : V} {m : ℕ} (hm : 2 ≤ m) (ha : a ≤ tower j m) (hb : b ≤ tower j m)
    (hc : c ≤ tower j m) : gateValue a b c ≤ tower j (m+60) := by
  classical
  unfold gateValue
  split
  · exact Arithmetic.zero_le _
  · exact template_le ArithmeticSeedTemplates222.bundleTemplate (by decide) hm ha hb hc
      (Arithmetic.zero_le _)

theorem axStack_le {a h b c u t s j : V} {m : ℕ} (hm : 2 ≤ m)
    (ha : a ≤ tower j m) (hh : h ≤ tower j m) (hb : b ≤ tower j m) (hc : c ≤ tower j m)
    (hu : u ≤ tower j m) (ht : t ≤ tower j m) (hs : s ≤ tower j m) :
    axStackValue a h b c u t s ≤ tower j (m+80) := by
  have z : (0 : V) ≤ tower j m := Arithmetic.zero_le _
  have r1 := rho1_le hm ha hb
  have r2 : rho2 a b c ≤ tower j (m+60) := template_le _ (by decide) hm ha hb hc z
  have r3 : rho3 a b c ≤ tower j (m+60) := template_le _ (by decide) hm ha hb hc z
  have r4 : rho4 a b c ≤ tower j (m+60) := template_le _ (by decide) hm ha hb hc z
  have r5 : rho5 a b c ≤ tower j (m+60) := template_le _ (by decide) hm ha hb hc z
  have r6 : rho6 a c ≤ tower j (m+60) := template_le _ (by decide) hm ha hc z z
  have rG : ArithmeticTemplates222.growG a b c ≤ tower j (m+60) :=
    template_le _ (by decide) hm ha hb hc z
  have r8 : rho8 a b c u ≤ tower j (m+60) := template_le _ (by decide) hm ha hb hc hu
  have rW : wal u h ≤ tower j (m+60) :=
    le_tower_of (tagged_le_tower hm (by norm_num) hu hh) (by omega)
  have q0 := cantor_le_tower_of (m := m) (m' := m+60) (by omega) (by omega) ht
    (le_tower_of hs (by omega))
  have q1 := cantor_le_tower_of (by omega) (by omega) rW q0
  have q2 := cantor_le_tower_of (by omega) (by omega) r8 q1
  have q3 := cantor_le_tower_of (by omega) (by omega) rG q2
  have q4 := cantor_le_tower_of (by omega) (by omega) r6 q3
  have q5 := cantor_le_tower_of (by omega) (by omega) r5 q4
  have q6 := cantor_le_tower_of (by omega) (by omega) r4 q5
  have q7 := cantor_le_tower_of (by omega) (by omega) r3 q6
  have q8 := cantor_le_tower_of (by omega) (by omega) r2 q7
  have q9 := cantor_le_tower_of (by omega) (by omega) r1 q8
  exact q9

/-- Every successful command result, shifted down by one, stays below `n+90`. -/
theorem effect_sub_one_le {j : V} {n : ℕ} (hn : 2 ≤ n) (k p q t s d h : V)
    (hk : k ≤ tower j n) (hp : p ≤ tower j n) (hq : q ≤ tower j n) (ht : t ≤ tower j n)
    (hs : s ≤ tower j n) (hd : d ≤ tower j n) (hh : h ≤ tower j n) :
    effectValue k p q t s d h - 1 ≤ tower j (n+90) := by
  classical
  have z : (0 : V) ≤ tower j n := Arithmetic.zero_le _
  have hdp : d + p ≤ tower j (n+1) := add_le_tower' hn hd hp
  by_cases hk0 : k = 0
  · by_cases hc : h = 1
    · rw [effectValue, if_pos hk0, if_pos hc]
      simp
    · rw [effectValue, if_pos hk0, if_neg hc, someState_sub_one]
      exact le_tower_of (stateValue_le hn ht (le_trans (second_le s) hs) hd
        (le_trans (first_le s) hs)) (by omega)
  · by_cases hk1 : k = 1
    · rw [effectValue, if_neg hk0, if_pos hk1, someState_sub_one]
      have hts := cantor_le_tower hn ht hs
      exact le_tower_of (stateValue_le (m := n+2) (by omega) (le_tower_of hh (by omega)) hts
        (le_tower_of hd (by omega)) (le_tower_of hh (by omega))) (by omega)
    · by_cases hk2 : k = 2
      · by_cases hm : wim t (d+p) = h
        · rw [effectValue, if_neg hk0, if_neg hk1, if_pos hk2, if_pos hm, someState_sub_one]
          have h0s := cantor_le_tower hn z hs
          exact le_tower_of (stateValue_le (m := n+2) (by omega) (le_tower_of hdp (by omega)) h0s
            (le_tower_of hdp (by omega)) (le_tower_of z (by omega))) (by omega)
        · rw [effectValue, if_neg hk0, if_neg hk1, if_pos hk2, if_neg hm, someState_sub_one]
          exact le_tower_of (stateValue_le (m := n+1) (by omega) (le_tower_of z (by omega))
            (le_tower_of hs (by omega)) hdp (le_tower_of z (by omega))) (by omega)
      · rw [effectValue, if_neg hk0, if_neg hk1, if_neg hk2, someState_sub_one]
        have hdq : d + q ≤ tower j (n+1) := add_le_tower' hn hd hq
        have hhp : h + p ≤ tower j (n+1) := add_le_tower' hn hh hp
        have hc3 : k - 3 ≤ tower j (n+1) := le_tower_of (le_trans tsub_le_self hk) (by omega)
        have hd1 : d ≤ tower j (n+1) := le_tower_of hd (by omega)
        have hg := gate_le (m := n+1) (by omega) hdq hhp hc3
        have hst := axStack_le (m := n+1) (by omega) hdq (le_tower_of hh (by omega)) hhp hc3 hd1
          (le_tower_of ht (by omega)) (le_tower_of hs (by omega))
        exact le_tower_of (stateValue_le (m := n+1+80) (by omega) (le_tower_of hg (by omega)) hst
          (le_tower_of z (by omega)) (le_tower_of z (by omega))) (by omega)

/-! ## Explicit certificate bounds -/

/-- The literal gate witness used by `gate_witness`, now as a named code. -/
noncomputable def gateWitness (a b c : V) : V :=
  if c = a ∨ c = b then 1 else node 11 (cantor a (cantor b c))

theorem gateWitness_value (a b c : V) : value (gateWitness a b c) = gateValue a b c + 1 := by
  classical
  by_cases hc : c = a ∨ c = b
  · simpa [gateWitness, gateValue, hc] using (value_truth (V := V))
  · simpa [gateWitness, gateValue, hc] using value_bundle a b c
      (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))

/-- The ten accepted witnesses created by one AX command. -/
noncomputable def axWitnesses (a b c u ph : V) : List V :=
  [gateWitness a b c, node 3 (cantor a b), node 4 (cantor a (cantor b c)),
    node 5 (cantor a (cantor b c)), node 6 (cantor a (cantor b c)),
    node 7 (cantor a (cantor b c)), node 8 (cantor a c), node 9 (cantor a (cantor b c)),
    node 10 (cantor a (cantor b (cantor c u))), node 2 (cantor u ph)]

/-- The proof of `certified_ax`, retaining its concrete bound. -/
theorem ax_working {B t s h : V} (a b c u ph : V) (hph : value ph = h+1)
    (ht : ProvB B t) (hs : StackB B s) :
    WorkingB (witnessBound B (axWitnesses a b c u ph))
      (stateValue (gateValue a b c) (axStackValue a h b c u t s) 0 0) := by
  set ps := axWitnesses a b c u ph
  set C := witnessBound B ps
  have hBC : B ≤ C := old_le_witnessBound B ps
  have hC : 1 ≤ C := le_trans hs.1 hBC
  have hgate : ProvB C (gateValue a b c) :=
    prov_at_witnessBound (p := gateWitness a b c) (by simp [ps, axWitnesses])
      (gateWitness_value a b c)
  have h1 : ProvB C (rho1 a b) :=
    prov_at_witnessBound (p := node 3 (cantor a b)) (by simp [ps, axWitnesses]) (value_r1 a b)
  have h2 : ProvB C (rho2 a b c) :=
    prov_at_witnessBound (p := node 4 (cantor a (cantor b c))) (by simp [ps, axWitnesses])
      (value_r2 a b c)
  have h3 : ProvB C (ArithmeticTemplates254.rho3 a b c) :=
    prov_at_witnessBound (p := node 5 (cantor a (cantor b c))) (by simp [ps, axWitnesses])
      (value_r3 a b c)
  have h4 : ProvB C (ArithmeticTemplates254.rho4 a b c) :=
    prov_at_witnessBound (p := node 6 (cantor a (cantor b c))) (by simp [ps, axWitnesses])
      (value_r4 a b c)
  have h5 : ProvB C (ArithmeticTemplates254.rho5 a b c) :=
    prov_at_witnessBound (p := node 7 (cantor a (cantor b c))) (by simp [ps, axWitnesses])
      (value_r5 a b c)
  have h6 : ProvB C (rho6 a c) :=
    prov_at_witnessBound (p := node 8 (cantor a c)) (by simp [ps, axWitnesses]) (value_r6 a c)
  have h7 : ProvB C (ArithmeticTemplates222.growG a b c) :=
    prov_at_witnessBound (p := node 9 (cantor a (cantor b c))) (by simp [ps, axWitnesses])
      (value_growG a b c)
  have h8 : ProvB C (rho8 a b c u) :=
    prov_at_witnessBound (p := node 10 (cantor a (cantor b (cantor c u))))
      (by simp [ps, axWitnesses]) (value_r8 a b c u)
  have hG : ProvB C (wal u h) :=
    prov_at_witnessBound (p := node 2 (cantor u ph)) (by simp [ps, axWitnesses])
      (value_gen u h ph hph)
  have hstack : StackB C (axStackValue a h b c u t s) := by
    exact stack_cons h1 (stack_cons h2 (stack_cons h3 (stack_cons h4
      (stack_cons h5 (stack_cons h6 (stack_cons h7 (stack_cons h8
        (stack_cons hG (stack_cons (prov_weaken hBC ht) (stack_weaken hBC hs))))))))))
  exact (working_state C _ _ _ _).mpr ⟨hgate, prov_truth hC, hstack⟩

/-- The proof of `certified_mp_success`, retaining its concrete bound. -/
theorem mp_working {B t s h : V} (b pt ph : V) (hpt : value pt = t+1) (hph : value ph = h+1)
    (hs : StackB B s) (hm : wim t b = h) :
    WorkingB (extendBound B (node 1 (cantor b (cantor pt ph))))
      (stateValue b (cantor 0 s) b 0) := by
  set p := node 1 (cantor b (cantor pt ph))
  have hv : value p = b+1 := value_mp b t h pt ph hpt hph hm.symm
  set C := extendBound B p
  have hC : 1 ≤ C := one_le_extendBound B p
  have hsC : StackB C s := stack_weaken (old_le_extendBound B p) hs
  exact (working_state C _ _ _ _).mpr
    ⟨prov_extend hv, prov_truth hC, stack_cons (prov_truth hC) hsC⟩

theorem witnessBound_le {B j : V} {m : ℕ} (hm : 2 ≤ m) (hB : B ≤ tower j m) :
    ∀ ps : List V, (∀ p ∈ ps, p ≤ tower j m) → witnessBound B ps ≤ tower j (m + ps.length)
  | [], _ => by simpa [witnessBound] using hB
  | p::ps, h => by
    have ih := witnessBound_le hm hB ps (fun q hq => h q (List.mem_cons_of_mem p hq))
    have hp := le_tower_of (h p (List.mem_cons_self ..)) (show m ≤ m + ps.length by omega)
    have := add_le_tower (by omega) ih hp
    have e : m + (p::ps).length = m + ps.length + 1 := by
      simp only [List.length_cons, Nat.add_assoc]
    rw [e]
    simpa [witnessBound, extendBound] using this

theorem axWitnesses_le {a b c u ph j : V} {m : ℕ} (hm : 2 ≤ m) (ha : a ≤ tower j m)
    (hb : b ≤ tower j m) (hc : c ≤ tower j m) (hu : u ≤ tower j m) (hph : ph ≤ tower j m) :
    ∀ p ∈ axWitnesses a b c u ph, p ≤ tower j (m+8) := by
  classical
  have cab := cantor_le_tower hm ha hb
  have cbc := cantor_le_tower hm hb hc
  have cac := cantor_le_tower hm ha hc
  have cuph := cantor_le_tower hm hu hph
  have cabc := cantor_le_tower_of (by omega) (by omega) ha cbc
  have ccu := cantor_le_tower hm hc hu
  have cbcu := cantor_le_tower_of (by omega) (by omega) hb ccu
  have cabcu := cantor_le_tower_of (by omega) (by omega) ha cbcu
  have nd : ∀ (t x : V) (k : ℕ), t ≤ 11 → x ≤ tower j (m+k) → k ≤ 7 →
      node t x ≤ tower j (m+8) := fun t x k ht hx hk =>
    le_tower_of (node_le_tower (by omega) ht hx) (by omega)
  have hg : gateWitness a b c ≤ tower j (m+8) := by
    unfold gateWitness
    split
    · exact numeral_le_tower j (by omega) (by norm_num)
    · exact nd 11 _ 4 le_rfl cabc (by omega)
  intro p hp
  simp only [axWitnesses, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg
  · exact nd 3 _ 2 (by norm_num) cab (by omega)
  · exact nd 4 _ 4 (by norm_num) cabc (by omega)
  · exact nd 5 _ 4 (by norm_num) cabc (by omega)
  · exact nd 6 _ 4 (by norm_num) cabc (by omega)
  · exact nd 7 _ 4 (by norm_num) cabc (by omega)
  · exact nd 8 _ 2 (by norm_num) cac (by omega)
  · exact nd 9 _ 4 (by norm_num) cabc (by omega)
  · exact nd 10 _ 6 (by norm_num) cabcu (by omega)
  · exact nd 2 _ 2 (by norm_num) cuph (by omega)

/-- One successful command keeps the certificate below `tower j (n+100)`. -/
theorem effect_working {j : V} {n : ℕ} (hn : 2 ≤ n) (k p q t s d h : V)
    (hk : k ≤ tower j n) (hp : p ≤ tower j n) (hq : q ≤ tower j n)
    (hd : d ≤ tower j n) (hh : h ≤ tower j n)
    (hw : WorkingB (tower j n) (stateValue t s d h))
    (hz : effectValue k p q t s d h ≠ 0) :
    WorkingB (tower j (n+100)) (effectValue k p q t s d h - 1) := by
  classical
  have hB : tower j n ≤ tower j (n+100) := tower_mono j (by omega)
  obtain ⟨ht, hhv, hs⟩ := (working_state (tower j n) t s d h).mp hw
  by_cases hk0 : k = 0
  · by_cases hc : h = 1
    · exact absurd ((effectValue_eq_zero_iff k p q t s d h).mpr ⟨hk0, hc⟩) hz
    · rw [effectValue, if_pos hk0, if_neg hc, someState_sub_one]
      exact working_weaken hB ((working_state _ _ _ _ _).mpr ⟨ht, stack_head hs, stack_tail hs⟩)
  · by_cases hk1 : k = 1
    · rw [effectValue, if_neg hk0, if_pos hk1, someState_sub_one]
      exact working_weaken hB ((working_state _ _ _ _ _).mpr ⟨hhv, hhv, stack_cons ht hs⟩)
    · by_cases hk2 : k = 2
      · by_cases hm : wim t (d+p) = h
        · rw [effectValue, if_neg hk0, if_neg hk1, if_pos hk2, if_pos hm, someState_sub_one]
          obtain ⟨pt, hpt, hvt⟩ := ht
          obtain ⟨ph, hph, hvh⟩ := hhv
          refine working_weaken ?_ (mp_working (d+p) pt ph hvt hvh hs hm)
          have hdp : d + p ≤ tower j (n+1) := add_le_tower' hn hd hp
          have c1 := cantor_le_tower hn hpt hph
          have c2 := cantor_le_tower_of (by omega) (by omega) hdp c1
          have c3 := node_le_tower (t := 1) (by omega) (by norm_num) c2
          have c4 := add_le_tower (by omega) (le_tower_of (le_refl (tower j n))
            (show n ≤ n+2+2+1 by omega)) c3
          exact le_tower_of c4 (by omega)
        · rw [effectValue, if_neg hk0, if_neg hk1, if_pos hk2, if_neg hm, someState_sub_one]
          exact working_weaken hB
            ((working_state _ _ _ _ _).mpr ⟨prov_truth hs.1, prov_truth hs.1, hs⟩)
      · rw [effectValue, if_neg hk0, if_neg hk1, if_neg hk2, someState_sub_one]
        obtain ⟨ph, hph, hvh⟩ := hhv
        refine working_weaken ?_ (ax_working (d+q) (h+p) (k-3) d ph hvh ht hs)
        have hdq : d + q ≤ tower j (n+1) := add_le_tower' hn hd hq
        have hhp : h + p ≤ tower j (n+1) := add_le_tower' hn hh hp
        have hc3 : k - 3 ≤ tower j (n+1) := le_tower_of (le_trans tsub_le_self hk) (by omega)
        have hW := witnessBound_le (m := n+1+8) (by omega)
          (le_tower_of (le_refl (tower j n)) (by omega))
          (axWitnesses (d+q) (h+p) (k-3) d ph)
          (axWitnesses_le (m := n+1) (by omega) hdq hhp hc3 (le_tower_of hd (by omega))
            (le_tower_of hph (by omega)))
        refine le_tower_of hW ?_
        simp only [axWitnesses, List.length_cons, List.length_nil]
        omega

theorem state_decode (w : V) :
    stateValue (first w) (first (second w)) (first (second (second w)))
      (second (second (second w))) = w := by
  simp only [stateValue, cantor_projections]

/-- The command step on the actual word fields, with explicit bounds. -/
theorem step_working {j : V} {n : ℕ} (hn : 2 ≤ n) {raw w : V}
    (hraw : raw ≤ tower j n) (hwle : w ≤ tower j n) (hw : WorkingB (tower j n) w)
    (hz : stepValue raw w ≠ 0) : WorkingB (tower j (n+100)) (stepValue raw w - 1) := by
  have hw' : WorkingB (tower j n) (stateValue (first w) (first (second w))
      (first (second (second w))) (second (second (second w)))) := by
    rw [state_decode]; exact hw
  exact effect_working hn _ _ _ _ _ _ _ (le_trans (first_le raw) hraw)
    (le_trans (first_le _) (le_trans (second_le raw) hraw))
    (le_trans (first_le _) (le_trans (second2_le raw) hraw))
    (le_trans (first_le _) (le_trans (second2_le w) hwle))
    (le_trans (second_le _) (le_trans (second2_le w) hwle)) hw' hz

theorem step_sub_one_le {j : V} {n : ℕ} (hn : 2 ≤ n) {raw w : V}
    (hraw : raw ≤ tower j n) (hwle : w ≤ tower j n) :
    stepValue raw w - 1 ≤ tower j (n+90) :=
  effect_sub_one_le hn _ _ _ _ _ _ _ (le_trans (first_le raw) hraw)
    (le_trans (first_le _) (le_trans (second_le raw) hraw))
    (le_trans (first_le _) (le_trans (second2_le raw) hraw))
    (le_trans (first_le w) hwle)
    (le_trans (first_le _) (le_trans (second_le w) hwle))
    (le_trans (first_le _) (le_trans (second2_le w) hwle))
    (le_trans (second_le _) (le_trans (second2_le w) hwle))

/-! ## The enumerator invariant -/

local instance value_delta : 𝚫₁-Function₁[V] value := value_defined_delta.to_definable

/-- Configuration and certificate below one bound; a halted configuration
retains an accepted falsity witness below the same bound. -/
abbrev Good (B c : V) : Prop :=
  c ≤ B ∧ ((c = 0 ∧ ∃ p ≤ B, value p = 2) ∨
    (c ≠ 0 ∧ WorkingB B (ArithmeticEnumSoundnessPerm222.working c)))

instance good_definable : 𝚺₁-Relation (Good (V := V)) := by
  unfold Good
  definability

theorem fetch_bounds {pl np B : V} (hpl : pl ≤ B) (hnp : np ≤ B) :
    first (ArithmeticCommandFetchPerm222.fetchValue pl np) ≤ B ∧
      second (ArithmeticCommandFetchPerm222.fetchValue pl np) ≤ B + 1 := by
  classical
  by_cases h0 : pl = 0
  · subst h0
    simp only [ArithmeticCommandFetchPerm222.raw_new, ArithmeticCommandFetchPerm222.next_new]
    exact ⟨hnp, _root_.add_le_add hnp le_rfl⟩
  · have he := ArithmeticCommandFetchPerm222.pred_add_one pl h0
    rw [← he, ArithmeticCommandFetchPerm222.raw_continuation,
      ArithmeticCommandFetchPerm222.next_continuation]
    refine ⟨le_trans tsub_le_self hpl, le_trans hnp le_self_add⟩

theorem live_decode (c : V) (hc : c ≠ 0) :
    liveValue (first (c-1)) (first (second (c-1))) (second (second (c-1))) = c := by
  simp only [liveValue, cantor_projections]
  exact ArithmeticCommandFetchPerm222.pred_add_one c hc

/-- One enumerator step from a good configuration below `tower j n`. -/
theorem good_step {j : V} {n : ℕ} (hn : 2 ≤ n) {c : V} (hg : Good (tower j n) c) :
    Good (tower j (n+100)) (enumValue c) := by
  classical
  obtain ⟨hc, ⟨h0, p, hp, hv⟩ | ⟨h0, hwB⟩⟩ := hg
  · subst h0
    rw [enum_zero]
    exact ⟨Arithmetic.zero_le _, .inl ⟨rfl, p, le_trans hp (tower_mono j (by omega)), hv⟩⟩
  · have hc1 : c - 1 ≤ tower j n := le_trans tsub_le_self hc
    have hpl : first (c-1) ≤ tower j n := le_trans (first_le _) hc1
    have hnp : first (second (c-1)) ≤ tower j n :=
      le_trans (first_le _) (le_trans (second_le _) hc1)
    have hwle : second (second (c-1)) ≤ tower j n := le_trans (second2_le _) hc1
    have hwork : WorkingB (tower j n) (second (second (c-1))) := hwB
    rw [← live_decode c h0, enum_live]
    obtain ⟨hraw, hnext⟩ := fetch_bounds hpl hnp
    have hnext' := le_trans hnext (succ_le_tower hn le_rfl)
    generalize first (ArithmeticCommandFetchPerm222.fetchValue (first (c-1))
      (first (second (c-1)))) = raw at hraw ⊢
    generalize second (ArithmeticCommandFetchPerm222.fetchValue (first (c-1))
      (first (second (c-1)))) = next at hnext' ⊢
    generalize second (second (c-1)) = w at hwle hwork ⊢
    unfold execValue
    dsimp only
    by_cases hs : stepValue raw w = 0
    · rw [if_pos hs]
      obtain ⟨p, hp, hv⟩ := accepted_falsity_of_cache hwork
        ((stepValue_eq_zero_iff raw w).mp hs).2
      exact ⟨Arithmetic.zero_le _, .inl ⟨rfl, p, le_trans hp (tower_mono j (by omega)), hv⟩⟩
    · rw [if_neg hs]
      refine ⟨?_, .inr ⟨ArithmeticEnumSoundnessPerm222.live_ne_zero _ _ _, ?_⟩⟩
      · have hr := step_sub_one_le hn hraw hwle
        have ht : ArithmeticCommandWordPerm222.tailValue raw ≤ tower j n := le_trans (tail_le raw) hraw
        have q1 := cantor_le_tower_of (m := n+1) (m' := n+90) (by omega) (by omega) hnext' hr
        have q2 := cantor_le_tower_of (by omega) (by omega) ht q1
        have q3 := succ_le_tower (by omega) q2
        exact le_tower_of q3 (by omega)
      · rw [ArithmeticEnumSoundnessPerm222.working_live]
        exact step_working hn hraw hwle hwork hs

/-- The time-indexed bound `2^(2^(100*time+8))`. -/
noncomputable def soundBound (time : V) : V := Exp.exp (Exp.exp (100 * time + 8))

theorem soundBound_eq (time : V) : soundBound time = tower (100 * time) 8 := by
  simp [soundBound, tower]

theorem soundBound_succ (time : V) : soundBound (time+1) = tower (100 * time) 108 := by
  simp only [soundBound, tower]
  congr 2
  push_cast
  ring

instance soundBound_definable : 𝚺₁-Function₁ (soundBound : V → V) := by
  unfold soundBound
  definability

theorem good_run (time initial : V) (hi : Good (soundBound 0) initial) :
    Good (soundBound time) (run time initial) := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa only [run_zero] using hi
  case succ time ih =>
    rw [run_succ, soundBound_succ]
    rw [soundBound_eq] at ih
    exact good_step (by norm_num) ih

theorem good_initial : Good (soundBound 0) (liveValue (0 : V) 4 0) := by
  rw [soundBound_eq]
  have z : (0 : V) ≤ tower (100 * 0) 2 := Arithmetic.zero_le _
  have h4 : (4 : V) ≤ tower (100 * 0) 2 := numeral_le_tower _ le_rfl (by norm_num)
  have c1 := cantor_le_tower le_rfl h4 z
  have c2 := cantor_le_tower_of (by omega) (by omega) z c1
  have c3 := succ_le_tower (by omega) c2
  refine ⟨le_tower_of c3 (by omega), .inr ⟨ArithmeticEnumSoundnessPerm222.live_ne_zero _ _ _, ?_⟩⟩
  rw [ArithmeticEnumSoundnessPerm222.working_live]
  exact working_zero (one_le_tower _ _)

/-- **Halt ⇒ refutation, with an explicit witness bound.** If the actual
enumerator halts at internal time `time` from its literal seed, an accepted
C222 falsity proof code exists below `2^(2^(100*time+8))`. -/
theorem accepted_bound_of_run_zero (time : V) (hh : run time (liveValue 0 4 0) = 0) :
    ∃ proof ≤ soundBound time, value proof = 2 := by
  obtain ⟨_, ⟨_, hp⟩ | ⟨h0, _⟩⟩ := good_run time _ good_initial
  · exact hp
  · exact absurd hh h0

theorem refutation_bound_of_zero_work_halts (time : V)
    (hh : run time (liveValue 0 4 0) = 0) :
    ∃ proof ≤ Exp.exp (Exp.exp (100 * time + 8)),
      ArithmeticHistory222.checkDef.val.Evalb ![proof,1] := by
  obtain ⟨proof, hp, hv⟩ := accepted_bound_of_run_zero time hh
  exact ⟨proof, hp, by simpa [one_add_one_eq_two] using hv⟩

end DiophantineConsistency.ArithmeticEnumBoundSoundness
