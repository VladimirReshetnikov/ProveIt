import DiophantineConsistency.AdaptiveGap85JointResidue
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85WeightedOrbit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85JointResidue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Weighted (N q : V) (p r : V × V) : Prop :=
  ∃ u v, q*r.1+r.2+N*u=q*p.1+p.2+N*v

theorem weighted_refl (N q : V) (p : V×V) : Weighted N q p p := ⟨0,0,by simp⟩
theorem weighted_trans (N q : V) (p r z : V×V)
    (h : Weighted N q p r) (h' : Weighted N q r z) : Weighted N q p z := by
  obtain ⟨u,v,huv⟩ := h
  obtain ⟨u',v',huv'⟩ := h'
  refine ⟨u+u',v+v',?_⟩
  apply add_right_cancel (b:=q*r.1+r.2)
  calc
    (q*z.1+z.2+N*(u+u'))+(q*r.1+r.2) =
        (q*r.1+r.2+N*u)+(q*z.1+z.2+N*u') := by ring
    _ = (q*p.1+p.2+N*v)+(q*r.1+r.2+N*v') := by rw [huv,huv']
    _ = (q*p.1+p.2+N*(v+v'))+(q*r.1+r.2) := by ring

theorem literal_step_weight (p : Fin 4 → ℕ) (v w : Fin 13 → V) (h : LiteralStep p v w) :
    let q := 1+v 0*(p 0:V)
    let N := (v 9+v 7*(v 9+v 10))*(v 7*(q*q))
    w 0=v 0 ∧ w 7=v 7 ∧ w 9=v 9 ∧ w 10=v 10 ∧
    Weighted N q (v 1,v 2) (w 1,w 2) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := v 6+(p 1:V)*q
  let U : V := v 7*(q*q)
  let c : V := v 9+v 7*(v 9+v 10)
  let N : V := c*U
  change w 0=v 0 ∧ w 7=v 7 ∧ w 9=v 9 ∧ w 10=v 10 ∧ Weighted N q (v 1,v 2) (w 1,w 2)
  rcases h with h | ⟨t,hC,h⟩ | ⟨s,hBA,hF,h⟩
  · subst w
    refine ⟨rfl,rfl,rfl,rfl,0,b,?_⟩
    dsimp [AdaptiveGap85ShiftModel.shift,Weighted,N,c,U,q,b]
    ring
  · subst w
    change q*b*t≤v 2 at hC
    have hc : (v 2-q*b*t)+q*b*t=v 2 := tsub_add_cancel_of_le hC
    refine ⟨rfl,rfl,rfl,rfl,0,0,?_⟩
    change q*(v 1+b*t)+(v 2-q*b*t)+N*0=q*v 1+v 2+N*0
    calc
      _ = q*v 1+((v 2-q*b*t)+q*b*t) := by ring
      _ = _ := by rw [hc]; ring
  · subst w
    let d := N*s
    change 1≤b*A at hBA
    change A*d≤v 1 at hF
    have hba : (b*A-1)+1=b*A := tsub_add_cancel_of_le hBA
    have hf : (v 1-A*d)+A*d=v 1 := tsub_add_cancel_of_le hF
    have he : q*(A*d)=(b*A-1)*d+(A+1)*d := by
      calc
        _ = b*A*d+A*d := by dsimp [q]; ring
        _ = ((b*A-1)+1)*d+A*d := by rw [hba]
        _ = _ := by ring
    refine ⟨rfl,rfl,rfl,rfl,(A+1)*s,0,?_⟩
    change q*(v 1-A*d)+(v 2+(b*A-1)*d)+N*((A+1)*s)=q*v 1+v 2+N*0
    calc
      _ = q*(v 1-A*d)+v 2+((b*A-1)*d+(A+1)*d) := by dsimp [d]; ring
      _ = q*((v 1-A*d)+A*d)+v 2 := by rw [←he]; ring
      _ = _ := by rw [hf]; ring

theorem literal_orbit_weight (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (h : Relation.ReflTransGen (LiteralStep p) v w) :
    let q := 1+v 0*(p 0:V)
    let N := (v 9+v 7*(v 9+v 10))*(v 7*(q*q))
    w 0=v 0 ∧ w 7=v 7 ∧ w 9=v 9 ∧ w 10=v 10 ∧
    Weighted N q (v 1,v 2) (w 1,w 2) := by
  induction h with
  | refl => exact ⟨rfl,rfl,rfl,rfl,weighted_refl _ _ _⟩
  | @tail x y hprev hstep ih =>
    obtain ⟨h0,h7,h9,h10,hw⟩ := ih
    obtain ⟨h0',h7',h9',h10',hw'⟩ := literal_step_weight p x y hstep
    rw [h0,h7,h9,h10] at hw'
    exact ⟨h0'.trans h0,h7'.trans h7,h9'.trans h9,h10'.trans h10,weighted_trans _ _ _ _ _ hw hw'⟩

/-- Every gap endpoint has the unique small weighted code determined by
the starting tuple and the cU modulus. -/
theorem orbit_gap_code (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hv : ∀j,0<v j) (h : Relation.ReflTransGen (LiteralStep p) v w)
    (hg : w 1+w 2<1+w 0*(p 0:V)) :
    let q := 1+v 0*(p 0:V)
    let N := (v 9+v 7*(v 9+v 10))*(v 7*(q*q))
    q*w 1+w 2=(q*v 1+v 2)%N := by
  let q : V := 1+v 0*(p 0:V)
  let c : V := v 9+v 7*(v 9+v 10)
  let U : V := v 7*(q*q)
  let N : V := c*U
  have hq : 0<q := by dsimp [q]; simp
  have hq1 : 1≤q := pos_iff_one_le.mp hq
  have hy1 : 1≤v 7 := pos_iff_one_le.mp (hv 7)
  have hcpos : 0<c := by
    dsimp [c]
    exact add_pos (hv 9) (mul_pos (hv 7) (add_pos (hv 9) (hv 10)))
  have hc1 : 1≤c := pos_iff_one_le.mp hcpos
  have hN : 0<N := mul_pos (lt_of_lt_of_le (by simp : (0:V)<1) hc1)
    (mul_pos (hv 7) (mul_pos hq hq))
  have hNlb : q*q≤N := calc
    q*q≤v 7*(q*q) := le_mul_of_one_le_left (by simp) hy1
    _≤c*(v 7*(q*q)) := le_mul_of_one_le_left (by simp) hc1
  obtain ⟨h0,h7,h9,h10,⟨u,t,he⟩⟩ := literal_orbit_weight p v w h
  have hm := congrArg (fun z : V => z%N) he
  rw [mod_add_mul' _ _ hN,mod_add_mul' _ _ hN] at hm
  have hg' : w 1+w 2<q := by simpa only [h0] using hg
  have hsmall : q*w 1+w 2<q*q := calc
    _ ≤ q*w 1+q*w 2 := add_le_add (le_refl _) (le_mul_of_one_le_left (by simp) hq1)
    _ = q*(w 1+w 2) := by ring
    _ < q*q := mul_lt_mul_of_pos_left hg' hq
  rw [mod_eq_self_of_lt (lt_of_lt_of_le hsmall hNlb)] at hm
  exact hm

theorem gap_code_unique (q F C F' C' : V) (hq : 0<q)
    (hg : F+C<q) (hg' : F'+C'<q) (he : q*F+C=q*F'+C') :
    F=F' ∧ C=C' := by
  have hc : C<q := lt_of_le_of_lt (by simp : C≤F+C) hg
  have hc' : C'<q := lt_of_le_of_lt (by simp : C'≤F'+C') hg'
  have hm := congrArg (fun z : V => z%q) he
  have hl : q*F+C=C+q*F := by ring
  have hr : q*F'+C'=C'+q*F' := by ring
  rw [hl,hr,mod_add_mul' _ _ hq,mod_add_mul' _ _ hq,
    mod_eq_self_of_lt hc,mod_eq_self_of_lt hc'] at hm
  have hf : F=F' := by
    rw [hm] at he
    exact mul_left_cancel₀ (ne_of_gt hq) (add_right_cancel he)
  exact ⟨hf,hm⟩

/-- At most one pair of F,C coordinates can be obtained at a gap endpoint
of the specified three-shift orbit. No such endpoint is asserted to exist. -/
theorem orbit_unique_gap_pair (p : Fin 4 → ℕ) (v w z : Fin 13 → V)
    (hv : ∀j,0<v j)
    (hw : Relation.ReflTransGen (LiteralStep p) v w)
    (hz : Relation.ReflTransGen (LiteralStep p) v z)
    (hgw : w 1+w 2<1+w 0*(p 0:V))
    (hgz : z 1+z 2<1+z 0*(p 0:V)) : w 1=z 1 ∧ w 2=z 2 := by
  let q : V := 1+v 0*(p 0:V)
  have hq : 0<q := by dsimp [q]; simp
  have hw0 := (literal_orbit_weight p v w hw).1
  have hz0 := (literal_orbit_weight p v z hz).1
  have hg1 : w 1+w 2<q := by simpa only [hw0] using hgw
  have hg2 : z 1+z 2<q := by simpa only [hz0] using hgz
  have hew := orbit_gap_code p v w hv hw hgw
  have hez := orbit_gap_code p v z hv hz hgz
  exact gap_code_unique q (w 1) (w 2) (z 1) (z 2) hq hg1 hg2 (hew.trans hez.symm)

/-- Conditional obstruction: the weighted code of any gap endpoint is < q². -/
theorem orbit_large_remainder_blocks (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hv : ∀j,0<v j) (h : Relation.ReflTransGen (LiteralStep p) v w)
    (hrem : let q := 1+v 0*(p 0:V)
      let N := (v 9+v 7*(v 9+v 10))*(v 7*(q*q))
      q*q≤(q*v 1+v 2)%N) :
    ¬ w 1+w 2<1+w 0*(p 0:V) := by
  intro hg
  let q : V := 1+v 0*(p 0:V)
  have hq : 0<q := by dsimp [q]; simp
  have hq1 : 1≤q := pos_iff_one_le.mp hq
  have h0 := (literal_orbit_weight p v w h).1
  have hg' : w 1+w 2<q := by simpa only [h0] using hg
  have hsmall : q*w 1+w 2<q*q := calc
    _ ≤ q*w 1+q*w 2 := add_le_add (le_refl _) (le_mul_of_one_le_left (by simp) hq1)
    _ = q*(w 1+w 2) := by ring
    _ < q*q := mul_lt_mul_of_pos_left hg' hq
  have he := orbit_gap_code p v w hv h hg
  dsimp only at hrem he
  rw [←he] at hrem
  exact (not_le_of_gt hsmall) hrem
end DiophantineConsistency.AdaptiveGap85WeightedOrbit
