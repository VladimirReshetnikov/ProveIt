import DiophantineConsistency.ArithmeticStackCertificate222
import DiophantineConsistency.ArithmeticCommandStepPerm222

/-!
Local soundness of the actual permuted C222 effects in every IΣ1 model.
The only checker is actual History222. NIP/DROP/MP have tags0/1/2; AX reads
physical y/x, uses old counter d for rho8 and GEN, and pushes actual growG
and the gated helper-free seed. No old command-preservation module is imported.
Certification carries one bound on accepted numeric proof witnesses. Successful
commands preserve it with an explicitly enlarged bound where needed. The sole
halting command exposes an accepted cached falsity witness. AX retains its
literal freshness test and all ten pushes, including GEN of the old cache.
No scheduler time induction or binary/consistency transport is asserted here.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandPreservationPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254
open ArithmeticHistory222 (value)
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho8)
open ArithmeticTemplates222 (growG)
open ArithmeticProofConstructors222 ArithmeticStackCertificate222
open ArithmeticCommandStepPerm222
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma working_state (B t s d h : V) :
    WorkingB B (stateValue t s d h) ↔ ProvB B t ∧ ProvB B h ∧ StackB B s :=
  working_fields B t s d h

lemma certified_state {B t s d h : V}
    (ht : ProvB B t) (hh : ProvB B h) (hs : StackB B s) :
    CertifiedWorking (stateValue t s d h) :=
  ⟨B, (working_state B t s d h).mpr ⟨ht, hh, hs⟩⟩

@[simp] lemma someState_sub_one (t s d h : V) :
    someState t s d h - 1 = stateValue t s d h := by simp [someState]

/-- A fixed finite list of newly built internal witnesses enlarges the old
bound constructively. This is not a bound supplied for an arbitrary stack. -/
def witnessBound (B : V) : List V → V
  | [] => B
  | p::ps => extendBound (witnessBound B ps) p

lemma old_le_witnessBound (B : V) (ps : List V) : B ≤ witnessBound B ps := by
  induction ps with
  | nil => exact le_rfl
  | cons p ps ih => exact le_trans ih (old_le_extendBound _ _)

lemma mem_le_witnessBound (B : V) (ps : List V) {p : V} (hp : p ∈ ps) :
    p ≤ witnessBound B ps := by
  induction ps with
  | nil => cases hp
  | cons q ps ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact witness_le_extendBound _ _
    · exact le_trans (ih hp) (old_le_extendBound _ _)

lemma prov_at_witnessBound {B p x : V} {ps : List V}
    (hp : p ∈ ps) (hv : value p = x+1) : ProvB (witnessBound B ps) x :=
  prov_of_value (mem_le_witnessBound B ps hp) hv

lemma gate_witness (a b c : V) : ∃ p, value p = gateValue a b c + 1 := by
  classical
  by_cases hc : c = a ∨ c = b
  · exact ⟨1, by simpa [gateValue, hc] using (value_truth (V := V))⟩
  · exact ⟨node 11 (cantor a (cantor b c)), by
      simpa [gateValue, hc] using value_bundle a b c
        (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))⟩

lemma certified_mp_success {B t s h : V} (b : V)
    (ht : ProvB B t) (hh : ProvB B h) (hs : StackB B s)
    (hm : wim t b = h) : CertifiedWorking (stateValue b (cantor 0 s) b 0) := by
  obtain ⟨pt, _, hpt⟩ := ht
  obtain ⟨ph, _, hph⟩ := hh
  let p := node 1 (cantor b (cantor pt ph))
  have hv : value p = b+1 := value_mp b t h pt ph hpt hph hm.symm
  let C := extendBound B p
  have hC : 1 ≤ C := one_le_extendBound B p
  have hsC : StackB C s := stack_weaken (old_le_extendBound B p) hs
  exact certified_state (prov_extend hv) (prov_truth hC) (stack_cons (prov_truth hC) hsC)

/-- The fixed AX witnesses preserve the stack with their explicit common bound. -/
theorem ax_working_with_witnesses {B t s h : V} (a b c u ph pg : V)
    (hph : value ph = h + 1) (hpg : value pg = gateValue a b c + 1)
    (ht : ProvB B t) (hs : StackB B s) :
    WorkingB (witnessBound B [pg, node 3 (cantor a b), node 4 (cantor a (cantor b c)),
      node 5 (cantor a (cantor b c)), node 6 (cantor a (cantor b c)),
      node 7 (cantor a (cantor b c)), node 8 (cantor a c), node 9 (cantor a (cantor b c)),
      node 10 (cantor a (cantor b (cantor c u))), node 2 (cantor u ph)])
      (stateValue (gateValue a b c) (axStackValue a h b c u t s) 0 0) := by
  let p1 := node 3 (cantor a b)
  let p2 := node 4 (cantor a (cantor b c))
  let p3 := node 5 (cantor a (cantor b c))
  let p4 := node 6 (cantor a (cantor b c))
  let p5 := node 7 (cantor a (cantor b c))
  let p6 := node 8 (cantor a c)
  let p7 := node 9 (cantor a (cantor b c))
  let p8 := node 10 (cantor a (cantor b (cantor c u)))
  let pG := node 2 (cantor u ph)
  let ps := [pg,p1,p2,p3,p4,p5,p6,p7,p8,pG]
  let C := witnessBound B ps
  have hBC : B ≤ C := old_le_witnessBound B ps
  have hC : 1 ≤ C := le_trans hs.1 hBC
  have hgate : ProvB C (gateValue a b c) :=
    prov_at_witnessBound (by simp [ps]) hpg
  have h1 : ProvB C (rho1 a b) :=
    prov_at_witnessBound (p := p1) (by simp [ps]) (value_r1 a b)
  have h2 : ProvB C (rho2 a b c) :=
    prov_at_witnessBound (p := p2) (by simp [ps]) (value_r2 a b c)
  have h3 : ProvB C (rho3 a b c) :=
    prov_at_witnessBound (p := p3) (by simp [ps]) (value_r3 a b c)
  have h4 : ProvB C (rho4 a b c) :=
    prov_at_witnessBound (p := p4) (by simp [ps]) (value_r4 a b c)
  have h5 : ProvB C (rho5 a b c) :=
    prov_at_witnessBound (p := p5) (by simp [ps]) (value_r5 a b c)
  have h6 : ProvB C (rho6 a c) :=
    prov_at_witnessBound (p := p6) (by simp [ps]) (value_r6 a c)
  have h7 : ProvB C (growG a b c) :=
    prov_at_witnessBound (p := p7) (by simp [ps]) (value_growG a b c)
  have h8 : ProvB C (rho8 a b c u) :=
    prov_at_witnessBound (p := p8) (by simp [ps]) (value_r8 a b c u)
  have hG : ProvB C (wal u h) :=
    prov_at_witnessBound (p := pG) (by simp [ps]) (value_gen u h ph hph)
  have hstack : StackB C (axStackValue a h b c u t s) := by
    exact stack_cons h1 (stack_cons h2 (stack_cons h3 (stack_cons h4
      (stack_cons h5 (stack_cons h6 (stack_cons h7 (stack_cons h8
        (stack_cons hG (stack_cons (prov_weaken hBC ht) (stack_weaken hBC hs))))))))))
  exact (working_state C _ _ _ _).mpr ⟨hgate, prov_truth hC, hstack⟩

/-- The fixed nine newly proved AX stack entries plus the top gate witness
share one finite explicit bound. The old top and full old stream are retained. -/
lemma certified_ax {B t s h : V} (a b c u : V)
    (ht : ProvB B t) (hh : ProvB B h) (hs : StackB B s) :
    CertifiedWorking (stateValue (gateValue a b c) (axStackValue a h b c u t s) 0 0) := by
  obtain ⟨ph, _, hph⟩ := hh
  obtain ⟨pg, hpg⟩ := gate_witness a b c
  exact ⟨_, ax_working_with_witnesses a b c u ph pg hph hpg ht hs⟩

/-- Local preservation for every actual selector and all physical fields.
The API p/q corresponds to y/x in the AX branch; u is the old counter d. -/
theorem effect_preserves (k p q t s d h : V)
    (hw : CertifiedWorking (stateValue t s d h))
    (hz : effectValue k p q t s d h ≠ 0) :
    CertifiedWorking (effectValue k p q t s d h - 1) := by
  classical
  obtain ⟨B, hw⟩ := hw
  obtain ⟨ht, hh, hs⟩ := (working_state B t s d h).mp hw
  by_cases hk0 : k = 0
  · by_cases hc : h = 1
    · exact False.elim (hz ((effectValue_eq_zero_iff k p q t s d h).mpr ⟨hk0,hc⟩))
    · rw [effectValue, if_pos hk0, if_neg hc, someState_sub_one]
      exact certified_state ht (stack_head hs) (stack_tail hs)
  · by_cases hk1 : k = 1
    · rw [effectValue, if_neg hk0, if_pos hk1, someState_sub_one]
      exact certified_state hh hh (stack_cons ht hs)
    · by_cases hk2 : k = 2
      · by_cases hm : wim t (d+p) = h
        · rw [effectValue, if_neg hk0, if_neg hk1, if_pos hk2, if_pos hm, someState_sub_one]
          exact certified_mp_success (d+p) ht hh hs hm
        · rw [effectValue, if_neg hk0, if_neg hk1, if_pos hk2, if_neg hm, someState_sub_one]
          exact certified_state (prov_truth hs.1) (prov_truth hs.1) hs
      · rw [effectValue, if_neg hk0, if_neg hk1, if_neg hk2, someState_sub_one]
        exact certified_ax (d+q) (h+p) (k-3) d ht hh hs

/-- No raw shape, standardness, or separately supplied preservation premise. -/
theorem certified_step {raw w : V} (hw : CertifiedWorking w)
    (hz : stepValue raw w ≠ 0) : CertifiedWorking (stepValue raw w - 1) := by
  have he : stateValue (first w) (first (second w))
      (first (second (second w))) (second (second (second w))) = w := by
    simp only [stateValue, cantor_projections]
  exact effect_preserves (first raw) (first (second raw))
    (first (second (second raw))) (first w) (first (second w))
    (first (second (second w))) (second (second (second w)))
    (by simpa only [he] using hw) hz

/-- Actual halt0 is NIP with certified cache1, exposing an accepted false proof. -/
theorem certified_halt {raw w : V} (hw : CertifiedWorking w)
    (hz : stepValue raw w = 0) : ∃ p : V, value p = 2 := by
  obtain ⟨B, hw⟩ := hw
  obtain ⟨p, _, hp⟩ := accepted_falsity_of_cache hw ((stepValue_eq_zero_iff raw w).mp hz).2
  exact ⟨p, hp⟩

end DiophantineConsistency.ArithmeticCommandPreservationPerm222
