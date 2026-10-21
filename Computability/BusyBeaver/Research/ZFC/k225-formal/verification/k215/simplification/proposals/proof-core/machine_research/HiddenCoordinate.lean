import Std

/- A countermodel for the logical-only recovery of atomic vacuity.
   This is NOT a model of the seed-K bundles and makes no consistency claim
   about the full large-matrix calculus or any Turing machine. -/
namespace HiddenCoordinate

abbrev Val := Nat → Bool

def upd (e : Val) (i : Nat) (x : Bool) : Val := fun j => if j = i then x else e j

@[simp] theorem upd_same (e : Val) (i : Nat) (x : Bool) : upd e i x i = x := by simp [upd]
@[simp] theorem upd_other (e : Val) (i j : Nat) (x : Bool) (h : j ≠ i) :
    upd e i x j = e j := by simp [upd, h]
@[simp] theorem upd_current (e : Val) (i : Nat) : upd e i (e i) = e := by
  funext j; by_cases h : j = i <;> simp [upd, h]
@[simp] theorem upd_overwrite (e : Val) (i : Nat) (x y : Bool) :
    upd (upd e i x) i y = upd e i y := by
  funext j; by_cases h : j = i <;> simp [upd, h]
theorem upd_commute (e : Val) (i j : Nat) (x y : Bool) (h : i ≠ j) :
    upd (upd e i x) j y = upd (upd e j y) i x := by
  funext k
  by_cases hi : k = i
  · subst k; simp [upd, h]
  · by_cases hj : k = j
    · subst k; simp [upd, hi]
    · simp [upd, hi, hj]

inductive F where
  | bot : F
  | rel : Nat → Nat → F
  | eq : Nat → Nat → F
  | imp : F → F → F
  | all : Nat → F → F
open F

def neg (A : F) : F := imp A bot
def ex (i : Nat) (A : F) : F := neg (all i (neg A))

def sem : F → Val → Prop
  | bot, _ => False
  | rel a b, e => e 0 = false ∧ e a ≠ e b
  | eq a b, e => e a = e b
  | imp A B, e => sem A e → sem B e
  | all i A, e => ∀ x, sem A (upd e i x)

def Valid (A : F) : Prop := ∀ e, sem A e

theorem sem_ex (i : Nat) (A : F) (e : Val) :
    sem (ex i A) e ↔ ∃ x, sem A (upd e i x) := by
  classical
  change ((∀ x, sem A (upd e i x) → False) → False) ↔ ∃ x, sem A (upd e i x)
  constructor
  · intro h
    by_cases hf : sem A (upd e i false)
    · exact ⟨false, hf⟩
    · have ht : sem A (upd e i true) := Classical.byContradiction (fun ht =>
        h (fun x hx => by cases x with
          | false => exact hf hx
          | true => exact ht hx))
      exact ⟨true, ht⟩
  · rintro ⟨x, hx⟩ hall
    exact hall x hx

/-- Stronger than the retained logical fragment: all equality-vacuity
    instances and ordinary equality transitivity are allowed as well. -/
inductive Ax : F → Prop
  | r1 (i j) : Ax (ex i (eq i j))
  | r2 (i) (A B) : Ax (imp (all i (imp A B)) (imp (all i A) (all i B)))
  | r3 (a b c) : Ax (imp (eq a b) (imp (rel c a) (rel c b)))
  | r4 (i j) (A) : Ax (imp (all i (all j A)) (all j (all i A)))
  | r5 (a b c) : Ax (imp (eq c a) (imp (rel c b) (rel a b)))
  | r6 (i) (A) : Ax (imp (ex i (all i A)) A)
  | r7 (a b c) : Ax (imp (eq c a) (imp (eq c b) (eq a b)))
  | r8 (A B C U) : Ax (imp (imp (imp C U) A) (imp (imp A C) (imp B C)))
  | eqVac (a b c) : c ≠ a → c ≠ b → Ax (imp (eq a b) (all c (eq a b)))
  | relVac (a b c) : a + b < c → Ax (imp (rel a b) (all c (rel a b)))
  | merged (a b c k) : k ≠ a → k ≠ b →
      Ax (imp (eq c a) (imp (eq c b) (all k (eq a b))))

theorem ax_valid {A : F} (h : Ax A) : Valid A := by
  classical
  cases h with
  | r1 i j =>
    intro e
    apply (sem_ex i (eq i j) e).mpr
    refine ⟨e j, ?_⟩
    simp [sem, upd]
  | r2 i A B => exact fun e h hA x => h x (hA x)
  | r3 a b c =>
    intro e h hr
    exact ⟨hr.1, fun hh => hr.2 (hh.trans h.symm)⟩
  | r4 i j A =>
    intro e h x y
    by_cases hij : i = j
    · subst j
      simpa only [upd_overwrite] using h y y
    · simpa only [upd_commute e i j y x hij] using h y x
  | r5 a b c =>
    intro e h hr
    exact ⟨hr.1, fun hh => hr.2 (h.trans hh)⟩
  | r6 i A =>
    intro e h
    obtain ⟨x, hx⟩ := (sem_ex i (all i A) e).mp h
    have hy := hx (e i)
    simpa only [upd_overwrite, upd_current] using hy
  | r7 a b c => exact fun e h1 h2 => h1.symm.trans h2
  | r8 A B C U =>
    intro e h hAC _
    by_cases hc : sem C e
    · exact hc
    · exact False.elim (hc (hAC (h (fun hh => False.elim (hc hh)))))
  | eqVac a b c ha hb =>
    intro e h x
    simpa only [sem, upd_other e c a x (Ne.symm ha), upd_other e c b x (Ne.symm hb)] using h
  | relVac a b c h =>
    intro e hr x
    have h0 : 0 ≠ c := by omega
    have ha : a ≠ c := by omega
    have hb : b ≠ c := by omega
    simpa only [sem, upd_other e c 0 x h0, upd_other e c a x ha, upd_other e c b x hb] using hr
  | merged a b c k ha hb =>
    intro e h1 h2 x
    have h : e a = e b := h1.symm.trans h2
    simpa only [sem, upd_other e k a x (Ne.symm ha), upd_other e k b x (Ne.symm hb)] using h

inductive Der : F → Prop
  | truth : Der (imp bot bot)
  | ax {A} : Ax A → Der A
  | mp {A B} : Der A → Der (imp A B) → Der B
  | gen (i) {A} : Der A → Der (all i A)

theorem sound {A : F} (h : Der A) : Valid A := by
  induction h with
  | truth => exact fun _ h => h
  | ax h => exact ax_valid h
  | mp _ _ hA hAB => exact fun e => hAB e (hA e)
  | gen i _ h => exact fun e x => h (upd e i x)

def bad : F := imp (rel 1 2) (all 0 (rel 1 2))
def witness : Val := fun i => if i = 2 then true else false

theorem counterexample : ¬ sem bad witness := by
  intro h
  have hp : sem (rel 1 2) witness := by simp [sem, witness]
  have hn := (h hp) true
  have : true = false := hn.1
  cases this

/-- There is no derivation of the missing atomic-vacuity instance in this
    logical fragment, even with all equality-vacuity instances supplied. -/
theorem not_derivable : ¬ Der bad := fun h => counterexample (sound h witness)

#print axioms ax_valid
#print axioms sound
#print axioms not_derivable
end HiddenCoordinate
