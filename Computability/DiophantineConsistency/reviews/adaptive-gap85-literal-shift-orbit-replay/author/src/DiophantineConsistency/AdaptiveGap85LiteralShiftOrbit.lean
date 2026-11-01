import DiophantineConsistency.AdaptiveGap85BalanceModel
import DiophantineConsistency.AdaptiveGap85ShiftModel
set_option autoImplicit false
/-! Abstract residue-preserving coordinate shifts; no zero existence is asserted. -/
/-! Coordinate orbit of two literal shifts; this does not assert zero preservation or existence. -/
namespace DiophantineConsistency.AdaptiveGap85LiteralShiftOrbit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem divisible_blocks (b F C : V) (hF : 0<F) (hC : 0<C) (h : b∣F) : ¬ F+C<1+b := by
  have hbF : b≤F := Arithmetic.le_of_dvd hF h
  have hC1 : 1≤C := pos_iff_one_le.mp hC
  apply not_lt_of_ge
  calc
    1+b = b+1 := by ac_rfl
    _ ≤ F+C := add_le_add hbF hC1

theorem move_residue (b F Fnew t : V) (hb : 0<b)
    (h : Fnew=F+b*t ∨ Fnew+b*t=F) : Fnew%b=F%b := by
  rcases h with hf | hr
  · rw [hf,mod_add_mul' _ _ hb]
  · have hh := congrArg (fun x : V => x%b) hr
    simpa only [mod_add_mul' _ _ hb] using hh

theorem move_preserves (b F Fnew t : V) (hb : 0<b)
    (h : Fnew=F+b*t ∨ Fnew+b*t=F) (hd : b∣F) : b∣Fnew := by
  apply mod_eq_zero_iff_dvd.mp
  rw [move_residue b F Fnew t hb h]
  exact mod_eq_zero_iff_dvd.mpr hd
def Step (b : V) (p r : V × V) : Prop :=
  (∃ t, r.1=p.1+b*t ∨ r.1+b*t=p.1) ∧
  (∃ t, r.2=p.2+b*t ∨ r.2+b*t=p.2)

theorem step_preserves (b : V) (p r : V × V) (hb : 0<b) (h : Step b p r)
    (hd : b∣p.1 ∨ b∣p.2) : b∣r.1 ∨ b∣r.2 := by
  rcases h with ⟨⟨t,ht⟩,⟨s,hs⟩⟩
  rcases hd with hF | hC
  · exact Or.inl (move_preserves b p.1 r.1 t hb ht hF)
  · exact Or.inr (move_preserves b p.2 r.2 s hb hs hC)

theorem orbit_preserves (b : V) (p r : V × V) (hb : 0<b)
    (h : Relation.ReflTransGen (Step b) p r) (hd : b∣p.1 ∨ b∣p.2) :
    b∣r.1 ∨ b∣r.2 := by
  induction h with
  | refl => exact hd
  | tail _ hs ih => exact step_preserves b _ _ hb hs ih

theorem orbit_blocks (b : V) (p r : V × V) (hb : 0<b)
    (h : Relation.ReflTransGen (Step b) p r) (hd : b∣p.1 ∨ b∣p.2)
    (hF : 0<r.1) (hC : 0<r.2) : ¬ r.1+r.2<1+b := by
  rcases orbit_preserves b p r hb h hd with hFdiv | hCdiv
  · exact divisible_blocks b r.1 r.2 hF hC hFdiv
  · simpa only [add_comm r.1 r.2] using
      divisible_blocks b r.2 r.1 hC hF hCdiv
theorem old_shift_step (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let b := v 0*(p 0:V)
    Step b (v 1,v 2) ((AdaptiveGap85ShiftModel.shift p v) 1,(AdaptiveGap85ShiftModel.shift p v) 2) := by
  dsimp [Step,AdaptiveGap85ShiftModel.shift]
  constructor
  · refine ⟨0,Or.inl ?_⟩
    simp
  · refine ⟨(v 9+v 7*(v 9+v 10))*(v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))),Or.inl ?_⟩
    ring

theorem balance_shift_step (p : Fin 4 → ℕ) (v : Fin 13 → V) (t : V)
    (hC : let b := v 0*(p 0:V); let q := 1+b; q*b*t≤v 2) :
    let b := v 0*(p 0:V)
    Step b (v 1,v 2) ((AdaptiveGap85BalanceModel.shift p v t) 1,(AdaptiveGap85BalanceModel.shift p v t) 2) := by
  dsimp [Step,AdaptiveGap85BalanceModel.shift]
  constructor
  · exact ⟨t,Or.inl rfl⟩
  · refine ⟨(1+v 0*(p 0:V))*t,Or.inr ?_⟩
    have heq : v 0*(p 0:V)*((1+v 0*(p 0:V))*t) = (1+v 0*(p 0:V))*(v 0*(p 0:V))*t := by ring
    rw [heq]
    exact tsub_add_cancel_of_le hC
def LiteralStep (p : Fin 4 → ℕ) (v w : Fin 13 → V) : Prop :=
  w=AdaptiveGap85ShiftModel.shift p v ∨
  ∃ t, (let b := v 0*(p 0:V); let q := 1+b; q*b*t≤v 2) ∧
    w=AdaptiveGap85BalanceModel.shift p v t

theorem literal_step_components (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (h : LiteralStep p v w) :
    w 0=v 0 ∧ Step (v 0*(p 0:V)) (v 1,v 2) (w 1,w 2) := by
  rcases h with h | ⟨t,hC,h⟩
  · subst w
    exact ⟨rfl,old_shift_step p v⟩
  · subst w
    exact ⟨rfl,balance_shift_step p v t hC⟩

theorem literal_orbit_preserves (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hb : 0<v 0*(p 0:V))
    (h : Relation.ReflTransGen (LiteralStep p) v w)
    (hd : v 0*(p 0:V)∣v 1 ∨ v 0*(p 0:V)∣v 2) :
    w 0=v 0 ∧ (v 0*(p 0:V)∣w 1 ∨ v 0*(p 0:V)∣w 2) := by
  induction h with
  | refl => exact ⟨rfl,hd⟩
  | @tail x y hprev hstep ih =>
    obtain ⟨hzero,hdiv⟩ := ih
    obtain ⟨hzero',hmove⟩ := literal_step_components p x y hstep
    rw [hzero] at hmove
    exact ⟨hzero'.trans hzero, step_preserves _ _ _ hb hmove hdiv⟩

theorem literal_orbit_blocks (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hb : 0<v 0*(p 0:V))
    (h : Relation.ReflTransGen (LiteralStep p) v w)
    (hd : v 0*(p 0:V)∣v 1 ∨ v 0*(p 0:V)∣v 2)
    (hF : 0<w 1) (hC : 0<w 2) : ¬ w 1+w 2<1+w 0*(p 0:V) := by
  obtain ⟨hzero,hdiv⟩ := literal_orbit_preserves p v w hb h hd
  rw [hzero]
  rcases hdiv with hFdiv | hCdiv
  · exact divisible_blocks _ _ _ hF hC hFdiv
  · simpa only [add_comm (w 1) (w 2)] using
      divisible_blocks (v 0*(p 0:V)) (w 2) (w 1) hC hF hCdiv
end DiophantineConsistency.AdaptiveGap85LiteralShiftOrbit
