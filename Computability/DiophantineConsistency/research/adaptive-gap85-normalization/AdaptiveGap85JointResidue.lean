import DiophantineConsistency.AdaptiveGap85ThirdModel
import DiophantineConsistency.AdaptiveGap85BalanceModel
import DiophantineConsistency.AdaptiveGap85ShiftModel
set_option autoImplicit false
set_option maxRecDepth 100000
/-! Joint residue of three coordinate shifts, not an existence or normalization theorem. -/
namespace DiophantineConsistency.AdaptiveGap85JointResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def Joint (b A : V) (p r : V × V) : Prop :=
  ∃ u v, r.1+A*p.2+b*u=p.1+A*r.2+b*v
theorem joint_mod (b A : V) (p r : V × V) (hb : 0<b) (h : Joint b A p r) :
    (r.1+A*p.2)%b=(p.1+A*r.2)%b := by
  obtain ⟨u,v,he⟩ := h
  have hm := congrArg (fun z : V => z%b) he
  simpa only [mod_add_mul' _ _ hb] using hm
theorem joint_refl (b A : V) (p : V×V) : Joint b A p p := by
  exact ⟨0,0,by simp⟩
theorem joint_trans (b A : V) (p r z : V×V) (h : Joint b A p r) (h' : Joint b A r z) : Joint b A p z := by
  obtain ⟨u,v,huv⟩ := h
  obtain ⟨u',v',huv'⟩ := h'
  refine ⟨u+u',v+v',?_⟩
  apply add_right_cancel (b:=r.1+A*r.2)
  calc
    (z.1+A*p.2+b*(u+u'))+(r.1+A*r.2) = (r.1+A*p.2+b*u)+(z.1+A*r.2+b*u') := by ring
    _ = (p.1+A*r.2+b*v)+(r.1+A*z.2+b*v') := by rw [huv,huv']
    _ = (p.1+A*z.2+b*(v+v'))+(r.1+A*r.2) := by ring
theorem joint_orbit (b A : V) (p r : V×V) (h : Relation.ReflTransGen (Joint b A) p r) : Joint b A p r := by
  induction h with
  | refl => exact joint_refl b A p
  | tail _ hs ih => exact joint_trans b A _ _ _ ih hs
theorem old_joint (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let b := v 0*(p 0:V)
    let q := 1+b
    let A := v 6+(p 1:V)*q
    Joint b A (v 1,v 2) ((AdaptiveGap85ShiftModel.shift p v) 1,(AdaptiveGap85ShiftModel.shift p v) 2) := by
  dsimp [Joint,AdaptiveGap85ShiftModel.shift]
  refine ⟨(v 6+(p 1:V)*(1+v 0*(p 0:V)))*(v 9+v 7*(v 9+v 10))*(v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))),0,?_⟩
  ring

theorem balance_joint (p : Fin 4 → ℕ) (v : Fin 13 → V) (t : V)
    (hC : let b := v 0*(p 0:V); let q := 1+b; q*b*t≤v 2) :
    let b := v 0*(p 0:V)
    let q := 1+b
    let A := v 6+(p 1:V)*q
    Joint b A (v 1,v 2) ((AdaptiveGap85BalanceModel.shift p v t) 1,(AdaptiveGap85BalanceModel.shift p v t) 2) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := v 6+(p 1:V)*q
  change q*b*t≤v 2 at hC
  have hc : (v 2-q*b*t)+q*b*t=v 2 := tsub_add_cancel_of_le hC
  change ∃ u z, (v 1+b*t)+A*(v 2)+b*u=v 1+A*(v 2-q*b*t)+b*z
  refine ⟨0,(1+A*q)*t,?_⟩
  calc
    (v 1+b*t)+A*(v 2)+b*0 = (v 1+b*t)+A*((v 2-q*b*t)+q*b*t) := by rw [hc]; simp
    _ = v 1+A*(v 2-q*b*t)+b*((1+A*q)*t) := by ring
theorem third_joint (p : Fin 4 → ℕ) (v : Fin 13 → V) (s : V)
    (hBA : let b := v 0*(p 0:V); let q := 1+b; let A := v 6+(p 1:V)*q; 1≤b*A)
    (hF : let b := v 0*(p 0:V); let q := 1+b; let A := v 6+(p 1:V)*q;
      let U := v 7*(q*q); let c := v 9+v 7*(v 9+v 10); A*(c*U*s)≤v 1) :
    let b := v 0*(p 0:V)
    let q := 1+b
    let A := v 6+(p 1:V)*q
    Joint b A (v 1,v 2) ((AdaptiveGap85ThirdModel.shift p v s) 1,(AdaptiveGap85ThirdModel.shift p v s) 2) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := v 6+(p 1:V)*q
  let U : V := v 7*(q*q)
  let c : V := v 9+v 7*(v 9+v 10)
  let d : V := c*U*s
  change 1≤b*A at hBA
  change A*d≤v 1 at hF
  have hba : (b*A-1)+1=b*A := tsub_add_cancel_of_le hBA
  have hf : (v 1-A*d)+A*d=v 1 := tsub_add_cancel_of_le hF
  have hm : A*d+A*((b*A-1)*d)=b*(A*A*d) := by
    calc
      A*d+A*((b*A-1)*d)=A*(((b*A-1)+1)*d) := by ring
      _ = b*(A*A*d) := by rw [hba]; ring
  change ∃ u z, (v 1-A*d)+A*(v 2)+b*u=v 1+A*(v 2+(b*A-1)*d)+b*z
  refine ⟨A*A*d,0,?_⟩
  calc
    (v 1-A*d)+A*(v 2)+b*(A*A*d) = ((v 1-A*d)+A*d)+A*(v 2)+A*((b*A-1)*d) := by rw [←hm]; ring
    _ = v 1+A*(v 2+(b*A-1)*d)+b*0 := by rw [hf]; ring
def LiteralStep (p : Fin 4 → ℕ) (v w : Fin 13 → V) : Prop :=
  w=AdaptiveGap85ShiftModel.shift p v ∨
  (∃ t, (let b := v 0*(p 0:V); let q := 1+b; q*b*t≤v 2) ∧
    w=AdaptiveGap85BalanceModel.shift p v t) ∨
  ∃ s, (let b := v 0*(p 0:V); let q := 1+b; let A := v 6+(p 1:V)*q; 1≤b*A) ∧
    (let b := v 0*(p 0:V); let q := 1+b; let A := v 6+(p 1:V)*q;
      let U := v 7*(q*q); let c := v 9+v 7*(v 9+v 10); A*(c*U*s)≤v 1) ∧
    w=AdaptiveGap85ThirdModel.shift p v s

theorem literal_step_joint (p : Fin 4 → ℕ) (v w : Fin 13 → V) (h : LiteralStep p v w) :
    w 0=v 0 ∧ w 6=v 6 ∧
    Joint (v 0*(p 0:V)) (v 6+(p 1:V)*(1+v 0*(p 0:V))) (v 1,v 2) (w 1,w 2) := by
  rcases h with h | ⟨t,hC,h⟩ | ⟨s,hBA,hF,h⟩
  · subst w
    exact ⟨rfl,rfl,old_joint p v⟩
  · subst w
    exact ⟨rfl,rfl,balance_joint p v t hC⟩
  · subst w
    exact ⟨rfl,rfl,third_joint p v s hBA hF⟩

theorem literal_orbit_joint (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (h : Relation.ReflTransGen (LiteralStep p) v w) :
    w 0=v 0 ∧ w 6=v 6 ∧
    Joint (v 0*(p 0:V)) (v 6+(p 1:V)*(1+v 0*(p 0:V))) (v 1,v 2) (w 1,w 2) := by
  induction h with
  | refl => exact ⟨rfl,rfl,joint_refl _ _ _⟩
  | @tail x y hprev hstep ih =>
    obtain ⟨hzero,hsix,hjoint⟩ := ih
    obtain ⟨hzero',hsix',hmove⟩ := literal_step_joint p x y hstep
    rw [hzero,hsix] at hmove
    exact ⟨hzero'.trans hzero,hsix'.trans hsix,joint_trans _ _ _ _ _ hjoint hmove⟩

theorem literal_orbit_congruence (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hb : 0<v 0*(p 0:V))
    (h : Relation.ReflTransGen (LiteralStep p) v w) :
    let b := v 0*(p 0:V)
    let A := v 6+(p 1:V)*(1+b)
    (w 1+A*v 2)%b=(v 1+A*w 2)%b := by
  exact joint_mod _ _ _ _ hb (literal_orbit_joint p v w h).2.2
end DiophantineConsistency.AdaptiveGap85JointResidue
