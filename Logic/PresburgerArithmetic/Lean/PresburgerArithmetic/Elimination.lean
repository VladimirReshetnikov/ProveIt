import PresburgerArithmetic.NormalForm
import PresburgerArithmetic.Cooper
import Mathlib.Tactic.Tauto

namespace PresburgerArithmetic

namespace Affine

def substHead (t replacement : Affine) : Affine :=
  t.tail.add (replacement.scale t.head)

theorem eval_tail (t : Affine) (xs : List Int) :
    t.tail.eval xs = t.eval (0 :: xs) := by
  cases t with
  | mk c cs => cases cs <;> simp [tail, eval, dot]

@[simp] theorem eval_head (t : Affine) (x : Int) (xs : List Int) :
    t.eval (x :: xs) = t.head * x + t.tail.eval xs := by
  cases t with
  | mk c cs => cases cs <;> simp [head, tail, eval, dot]; ring

@[simp] theorem eval_substHead (t replacement : Affine) (xs : List Int) :
    (t.substHead replacement).eval xs =
      t.eval (replacement.eval xs :: xs) := by
  simp [substHead, eval_head]; ring

end Affine

namespace Atom

def substHead (a : Atom) (replacement : Affine) : Atom :=
  a.mapAffine (·.substHead replacement)

@[simp] theorem eval_substHead (a : Atom) (replacement : Affine) (xs : List Int) :
    (a.substHead replacement).eval xs = a.eval (replacement.eval xs :: xs) := by
  cases a <;> simp [substHead, mapAffine, eval]

def headCoeff (a : Atom) : Int := a.affine.head

def coefficientFactor (a : Atom) : Nat :=
  if a.headCoeff = 0 then 1 else a.headCoeff.natAbs

theorem coefficientFactor_pos (a : Atom) : 0 < a.coefficientFactor := by
  simp only [coefficientFactor]
  split
  · omega
  · exact Int.natAbs_pos.mpr ‹_›

def modulus : Atom → Nat
  | .le _ => 1
  | .dvd d _ _ | .ndvd d _ _ => d


theorem modulus_pos (a : Atom) : 0 < a.modulus := by
  cases a <;> simp [modulus, *]

end Atom

namespace Cooper

def NormalAtom : Atom → Prop
  | .le t => t.head = -1 ∨ t.head = 0 ∨ t.head = 1
  | .dvd _ _ _ | .ndvd _ _ _ => True

def NormalClause (c : Clause) : Prop := ∀ a ∈ c, NormalAtom a

def commonCoefficient (c : Clause) : Nat :=
  (c.map Atom.coefficientFactor).prod

theorem commonCoefficient_pos (c : Clause) : 0 < commonCoefficient c := by
  induction c with
  | nil => simp [commonCoefficient]
  | cons a c ih =>
      simp only [commonCoefficient, List.map_cons, List.prod_cons]
      exact Nat.mul_pos (Atom.coefficientFactor_pos a) (by simpa [commonCoefficient] using ih)

theorem coefficientFactor_dvd_commonCoefficient {c : Clause} {a : Atom}
    (ha : a ∈ c) : a.coefficientFactor ∣ commonCoefficient c := by
  apply List.dvd_prod
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

theorem quotient_pos_of_mem {c : Clause} {a : Atom} (ha : a ∈ c)
    (hne : a.headCoeff ≠ 0) :
    0 < commonCoefficient c / a.headCoeff.natAbs := by
  have hfactor : a.coefficientFactor = a.headCoeff.natAbs := by
    simp [Atom.coefficientFactor, hne]
  have hdvd : a.headCoeff.natAbs ∣ commonCoefficient c := by
    simpa [hfactor] using coefficientFactor_dvd_commonCoefficient ha
  exact Nat.div_pos (Nat.le_of_dvd (commonCoefficient_pos c) hdvd)
    (Int.natAbs_pos.mpr hne)

theorem natAbs_headCoeff_dvd_commonCoefficient {c : Clause} {a : Atom}
    (ha : a ∈ c) (hne : a.headCoeff ≠ 0) :
    a.headCoeff.natAbs ∣ commonCoefficient c := by
  have hfactor : a.coefficientFactor = a.headCoeff.natAbs := by
    simp [Atom.coefficientFactor, hne]
  simpa [hfactor] using coefficientFactor_dvd_commonCoefficient ha

def normalizeAffine (L : Nat) (t : Affine) : Affine :=
  let a := t.head
  if _ : a = 0 then Affine.consCoeff 0 t.tail
  else
    let s : Int := (L / a.natAbs : Nat)
    Affine.consCoeff a.sign (t.tail.scale s)

@[simp] theorem head_normalizeAffine (L : Nat) (t : Affine) :
    (normalizeAffine L t).head = if t.head = 0 then 0 else t.head.sign := by
  unfold normalizeAffine
  split <;> simp_all

theorem eval_normalizeAffine_zero {L : Nat} {t : Affine} (ht : t.head = 0)
    (x : Int) (xs : List Int) :
    (normalizeAffine L t).eval ((L : Int) * x :: xs) = t.eval (x :: xs) := by
  unfold normalizeAffine
  rw [dif_pos ht]
  simp [Affine.eval_head, ht]

theorem eval_normalizeAffine_nonzero {L : Nat} {t : Affine}
    (ht : t.head ≠ 0) (hdiv : t.head.natAbs ∣ L) (x : Int) (xs : List Int) :
    (normalizeAffine L t).eval ((L : Int) * x :: xs) =
      (L / t.head.natAbs : Nat) * t.eval (x :: xs) := by
  let s : Int := (L / t.head.natAbs : Nat)
  have hL : (L : Int) = s * t.head.natAbs := by
    dsimp [s]
    exact_mod_cast (Nat.div_mul_cancel hdiv).symm
  have hcoeff : t.head.sign * (L : Int) = s * t.head := by
    calc
      t.head.sign * (L : Int) = t.head.sign * (s * t.head.natAbs) := by rw [hL]
      _ = s * (t.head.sign * t.head.natAbs) := by ring
      _ = s * t.head := by rw [Int.sign_mul_natAbs]
  unfold normalizeAffine
  rw [dif_neg ht]
  dsimp only
  simp only [Affine.eval_head, Affine.head_consCoeff, Affine.tail_consCoeff,
    Affine.eval_scale]
  change t.head.sign * ((L : Int) * x) + s * t.tail.eval xs =
    s * (t.head * x + t.tail.eval xs)
  rw [← mul_assoc, hcoeff]
  ring

/-- The scaled divisibility constraint produced by atom normalization is
equivalent to the original one.  Shared by the `dvd` and `ndvd` cases. -/
theorem dvd_eval_normalizeAffine_iff {L d : Nat} {t : Affine}
    (ht : t.head ≠ 0) (hdiv : t.head.natAbs ∣ L) (hL : 0 < L)
    (x : Int) (xs : List Int) :
    ((d * max 1 (L / t.head.natAbs) : Nat) : Int) ∣
        (normalizeAffine L t).eval ((L : Int) * x :: xs) ↔
      (d : Int) ∣ t.eval (x :: xs) := by
  have hspos : 0 < L / t.head.natAbs :=
    Nat.div_pos (Nat.le_of_dvd hL hdiv) (Int.natAbs_pos.mpr ht)
  have hmax : max 1 (L / t.head.natAbs) = L / t.head.natAbs := by omega
  rw [eval_normalizeAffine_nonzero ht hdiv x xs]
  simpa [Nat.cast_mul, mul_comm, hmax] using
    (Int.mul_dvd_mul_iff_left
      (by exact_mod_cast (Nat.ne_of_gt hspos) :
        ((L / t.head.natAbs : Nat) : Int) ≠ 0) :
      (((L / t.head.natAbs : Nat) : Int) * d ∣
          ((L / t.head.natAbs : Nat) : Int) * t.eval (x :: xs)) ↔
        (d : Int) ∣ t.eval (x :: xs))

def normalizeAtom (L : Nat) : Atom → Atom
  | .le t => .le (normalizeAffine L t)
  | .dvd d hd t =>
      if ha : t.head = 0 then .dvd d hd (Affine.consCoeff 0 t.tail)
      else
        let s := max 1 (L / t.head.natAbs)
        .dvd (d * s) (Nat.mul_pos hd (by omega)) (normalizeAffine L t)
  | .ndvd d hd t =>
      if ha : t.head = 0 then .ndvd d hd (Affine.consCoeff 0 t.tail)
      else
        let s := max 1 (L / t.head.natAbs)
        .ndvd (d * s) (Nat.mul_pos hd (by omega)) (normalizeAffine L t)

theorem normalAtom_normalizeAtom (L : Nat) (a : Atom) :
    NormalAtom (normalizeAtom L a) := by
  cases a with
  | le t =>
      change (normalizeAffine L t).head = -1 ∨
        (normalizeAffine L t).head = 0 ∨ (normalizeAffine L t).head = 1
      rw [head_normalizeAffine]
      by_cases ht : t.head = 0
      · simp [ht]
      · simp only [ht, if_false]
        cases h : t.head with
        | ofNat n => cases n <;> simp_all [Int.sign]
        | negSucc n => simp [Int.sign]
  | dvd d hd t => simp only [normalizeAtom]; split <;> trivial
  | ndvd d hd t => simp only [normalizeAtom]; split <;> trivial

/- The extra atom records that the normalized variable is a multiple of `L`. -/
def normalizeClause (c : Clause) : Clause :=
  let L := commonCoefficient c
  .dvd L (commonCoefficient_pos c) (Affine.consCoeff 1 (.const 0)) ::
    c.map (normalizeAtom L)

theorem normalClause_normalizeClause (c : Clause) : NormalClause (normalizeClause c) := by
  intro a ha
  simp only [normalizeClause, List.mem_cons, List.mem_map] at ha
  rcases ha with rfl | ⟨b, _, rfl⟩
  · trivial
  · exact normalAtom_normalizeAtom _ b

theorem eval_normalizeAtom_of_mem {c : Clause} {a : Atom} (ha : a ∈ c)
    (x : Int) (xs : List Int) :
    (normalizeAtom (commonCoefficient c) a).eval
        ((commonCoefficient c : Int) * x :: xs) = a.eval (x :: xs) := by
  have hL : 0 < commonCoefficient c := commonCoefficient_pos c
  cases a with
  | le t =>
      by_cases ht : t.head = 0
      · simp only [normalizeAtom, Atom.eval]
        rw [eval_normalizeAffine_zero ht]
      · have hdiv : t.head.natAbs ∣ commonCoefficient c :=
          natAbs_headCoeff_dvd_commonCoefficient ha ht
        have hspos : 0 < commonCoefficient c / t.head.natAbs :=
          quotient_pos_of_mem ha ht
        simp only [normalizeAtom, Atom.eval]
        rw [eval_normalizeAffine_nonzero ht hdiv x xs]
        exact decide_eq_decide.mpr (by
          rw [mul_comm]
          exact Int.mul_nonneg_iff_of_pos_right (by exact_mod_cast hspos))
  | dvd d hd t =>
      by_cases ht : t.head = 0
      · rw [normalizeAtom, dif_pos ht]
        simp [Atom.eval, Affine.eval_head, ht]
      · rw [normalizeAtom, dif_neg ht]
        dsimp only
        simp only [Atom.eval]
        exact decide_eq_decide.mpr (dvd_eval_normalizeAffine_iff ht
          (natAbs_headCoeff_dvd_commonCoefficient ha ht) hL x xs)
  | ndvd d hd t =>
      by_cases ht : t.head = 0
      · rw [normalizeAtom, dif_pos ht]
        simp [Atom.eval, Affine.eval_head, ht]
      · rw [normalizeAtom, dif_neg ht]
        dsimp only
        simp only [Atom.eval]
        exact decide_eq_decide.mpr (not_congr (dvd_eval_normalizeAffine_iff ht
          (natAbs_headCoeff_dvd_commonCoefficient ha ht) hL x xs))

theorem eval_normalizeClause_forward (c : Clause) (x : Int) (xs : List Int)
    (hc : DNF.evalClause c (x :: xs) = true) :
    DNF.evalClause (normalizeClause c)
      ((commonCoefficient c : Int) * x :: xs) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  simp only [normalizeClause, List.mem_cons, List.mem_map] at ha
  rcases ha with hfirst | ⟨b, hb, hab⟩
  · subst a
    simp [Atom.eval, Affine.eval_head]
  · subst a
    rw [eval_normalizeAtom_of_mem hb]
    exact List.all_eq_true.mp hc b hb

theorem eval_normalizeClause_backward (c : Clause) (y : Int) (xs : List Int)
    (hc : DNF.evalClause (normalizeClause c) (y :: xs) = true) :
    ∃ x : Int, DNF.evalClause c (x :: xs) = true := by
  have hc' := List.all_eq_true.mp hc
  have hmultipleBool := hc'
    (.dvd (commonCoefficient c) (commonCoefficient_pos c)
      (Affine.consCoeff 1 (.const 0))) (by
        simp [normalizeClause])
  have hmultiple : (commonCoefficient c : Int) ∣ y := by
    simpa [Atom.eval, Affine.eval_head] using of_decide_eq_true hmultipleBool
  rcases hmultiple with ⟨x, hx⟩
  refine ⟨x, List.all_eq_true.mpr ?_⟩
  intro a ha
  have hnormalized := hc' (normalizeAtom (commonCoefficient c) a) (by
    simp only [normalizeClause, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))
  rw [← eval_normalizeAtom_of_mem ha]
  simpa [hx] using hnormalized

theorem normalizeClause_exists_iff (c : Clause) (xs : List Int) :
    (∃ x : Int, DNF.evalClause c (x :: xs) = true) ↔
      ∃ y : Int, DNF.evalClause (normalizeClause c) (y :: xs) = true := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(commonCoefficient c : Int) * x,
      eval_normalizeClause_forward c x xs hx⟩
  · rintro ⟨y, hy⟩
    exact eval_normalizeClause_backward c y xs hy

def lowerBound? (a : Atom) : Option Affine :=
  match a with
  | .le t => if t.head = 1 then some t.tail.neg else none
  | _ => none

def upperBound? (a : Atom) : Option Affine :=
  match a with
  | .le t => if t.head = -1 then some t.tail else none
  | _ => none

def fixed? (a : Atom) : Option Atom :=
  if a.headCoeff = 0 then some (a.substHead (.const 0)) else none

def periodic? (a : Atom) : Option Atom :=
  match a with
  | .dvd _ _ _ | .ndvd _ _ _ => some a
  | _ => none

def period (c : Clause) : Nat :=
  (c.map Atom.modulus).prod

theorem period_pos (c : Clause) : 0 < period c := by
  induction c with
  | nil => simp [period]
  | cons a c ih =>
      simp only [period, List.map_cons, List.prod_cons]
      exact Nat.mul_pos (Atom.modulus_pos a) (by simpa [period] using ih)

theorem modulus_dvd_period {c : Clause} {a : Atom} (ha : a ∈ c) :
    a.modulus ∣ period c := by
  apply List.dvd_prod
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

theorem mem_of_mem_periodic_filter {c : Clause} {a : Atom}
    (ha : a ∈ c.filterMap periodic?) : a ∈ c := by
  simp only [List.mem_filterMap] at ha
  rcases ha with ⟨b, hb, hba⟩
  cases b <;> simp [periodic?] at hba
  all_goals subst a; exact hb

/-- Shifting the head variable by a multiple of the divisor does not change a
divisibility constraint.  Shared by the `dvd` and `ndvd` cases. -/
theorem dvd_eval_shift_iff {d : Nat} {m : Int} (hdm : (d : Int) ∣ m)
    (t : Affine) (x : Int) (xs : List Int) :
    ((d : Int) ∣ t.eval ((x + m) :: xs)) ↔ (d : Int) ∣ t.eval (x :: xs) := by
  have heval : t.eval ((x + m) :: xs) = t.eval (x :: xs) + t.head * m := by
    simp [Affine.eval_head]
    ring
  rw [heval]
  exact Int.dvd_add_left (dvd_mul_of_dvd_right hdm _)

theorem eval_periodic_atom {c : Clause} {a : Atom}
    (ha : a ∈ c.filterMap periodic?)
    (x : Int) (xs : List Int) :
    a.eval ((x + (period c : Int)) :: xs) = a.eval (x :: xs) := by
  have hac : a ∈ c := mem_of_mem_periodic_filter ha
  cases a with
  | le t =>
      simp only [List.mem_filterMap] at ha
      rcases ha with ⟨b, _, hb⟩
      cases b <;> simp [periodic?] at hb
  | dvd d hd t =>
      have hdm : (d : Int) ∣ (period c : Int) := by
        exact_mod_cast modulus_dvd_period hac
      simp only [Atom.eval]
      exact decide_eq_decide.mpr (dvd_eval_shift_iff hdm t x xs)
  | ndvd d hd t =>
      have hdm : (d : Int) ∣ (period c : Int) := by
        exact_mod_cast modulus_dvd_period hac
      simp only [Atom.eval]
      exact decide_eq_decide.mpr (not_congr (dvd_eval_shift_iff hdm t x xs))

theorem eval_periodic_filter (c : Clause) (x : Int) (xs : List Int) :
    DNF.evalClause (c.filterMap periodic?) ((x + (period c : Int)) :: xs) =
      DNF.evalClause (c.filterMap periodic?) (x :: xs) := by
  have go : ∀ ps : Clause, (∀ a ∈ ps, a ∈ c.filterMap periodic?) →
      DNF.evalClause ps ((x + (period c : Int)) :: xs) = DNF.evalClause ps (x :: xs) := by
    intro ps hps
    induction ps with
    | nil => rfl
    | cons a as ih =>
        change (a.eval ((x + (period c : Int)) :: xs) &&
          DNF.evalClause as ((x + (period c : Int)) :: xs)) =
          (a.eval (x :: xs) && DNF.evalClause as (x :: xs))
        rw [eval_periodic_atom (hps a (by simp)), ih]
        intro b hb; exact hps b (by simp [hb])
  exact go _ (fun _ h => h)

def periodicAt (ps : Clause) (x : Affine) : QF :=
  .conjunction (ps.map (·.substHead x))

@[simp] theorem eval_periodicAt (ps : Clause) (x : Affine) (xs : List Int) :
    (periodicAt ps x).eval xs = DNF.evalClause ps (x.eval xs :: xs) := by
  induction ps with
  | nil => rfl
  | cons a ps ih =>
      change ((a.substHead x).eval xs && (periodicAt ps x).eval xs) =
        (a.eval (x.eval xs :: xs) && DNF.evalClause ps (x.eval xs :: xs))
      rw [Atom.eval_substHead, ih]

theorem eval_normalizedClause_iff (c : Clause) (hc : NormalClause c)
    (x : Int) (xs : List Int) :
    DNF.evalClause c (x :: xs) = true ↔
      DNF.evalClause (c.filterMap fixed?) xs = true ∧
      (∀ lo ∈ c.filterMap lowerBound?, lo.eval xs ≤ x) ∧
      (∀ hi ∈ c.filterMap upperBound?, x ≤ hi.eval xs) ∧
      DNF.evalClause (c.filterMap periodic?) (x :: xs) = true := by
  induction c with
  | nil => simp [DNF.evalClause]
  | cons a c ih =>
      have ha : NormalAtom a := hc a (by simp)
      have htail : NormalClause c := by
        intro b hb; exact hc b (by simp [hb])
      change ((a.eval (x :: xs) && DNF.evalClause c (x :: xs)) = true) ↔ _
      rw [Bool.and_eq_true_iff]
      rw [ih htail]
      cases a with
      | le t =>
          simp only [NormalAtom] at ha
          rcases ha with h | h | h
          · simp [DNF.evalClause, fixed?, lowerBound?, upperBound?, periodic?, h,
              Atom.headCoeff, Atom.affine, Atom.eval, Affine.eval_head, Atom.substHead,
              Atom.mapAffine]; tauto
          · simp [DNF.evalClause, fixed?, lowerBound?, upperBound?, periodic?, h,
              Atom.headCoeff, Atom.affine, Atom.eval, Affine.eval_head, Atom.substHead,
              Atom.mapAffine]; tauto
          · have hineq : (0 ≤ x + t.tail.eval xs) ↔ -t.tail.eval xs ≤ x := by
              omega
            simp [DNF.evalClause, fixed?, lowerBound?, upperBound?, periodic?, h,
              Atom.headCoeff, Atom.affine, Atom.eval, Affine.eval_head, Atom.substHead,
              Atom.mapAffine, hineq]; tauto
      | dvd d hd t =>
          by_cases h : t.head = 0
          · have hfixedEval :
                ((Atom.dvd d hd t).substHead (.const 0)).eval xs =
                  (Atom.dvd d hd t).eval (x :: xs) := by
              rw [Atom.eval_substHead]
              simp [Atom.eval, Affine.eval_head, h]
            simp [DNF.evalClause, fixed?, lowerBound?, upperBound?, periodic?, h,
              Atom.headCoeff, Atom.affine, hfixedEval]; tauto
          · simp [DNF.evalClause, fixed?, lowerBound?, upperBound?, periodic?, h,
              Atom.headCoeff, Atom.affine, Atom.eval]; tauto
      | ndvd d hd t =>
          by_cases h : t.head = 0
          · have hfixedEval :
                ((Atom.ndvd d hd t).substHead (.const 0)).eval xs =
                  (Atom.ndvd d hd t).eval (x :: xs) := by
              rw [Atom.eval_substHead]
              simp [Atom.eval, Affine.eval_head, h]
            simp [DNF.evalClause, fixed?, lowerBound?, upperBound?, periodic?, h,
              Atom.headCoeff, Atom.affine, hfixedEval]; tauto
          · simp [DNF.evalClause, fixed?, lowerBound?, upperBound?, periodic?, h,
              Atom.headCoeff, Atom.affine, Atom.eval]; tauto

theorem eval_disjunction_map_iff {A : Type} (as : List A) (f : A → QF)
    (xs : List Int) :
    (QF.disjunction (as.map f)).eval xs = true ↔
      ∃ a ∈ as, (f a).eval xs = true := by
  rw [QF.eval_disjunction, List.any_eq_true]
  constructor
  · rintro ⟨q, hq, hqtrue⟩
    rcases List.mem_map.mp hq with ⟨a, ha, rfl⟩
    exact ⟨a, ha, hqtrue⟩
  · rintro ⟨a, ha, hatrue⟩
    exact ⟨f a, List.mem_map.mpr ⟨a, ha, rfl⟩, hatrue⟩

theorem eval_conjGrid_iff {A B : Type} (as : List A) (bs : List B)
    (f : A → B → QF) (xs : List Int) :
    (QF.conjList (as.flatMap fun a => bs.map (f a))).eval xs = true ↔
      ∀ a ∈ as, ∀ b ∈ bs, (f a b).eval xs = true := by
  rw [QF.eval_conjList, List.all_eq_true]
  constructor
  · intro hall a ha b hb
    exact hall (f a b) (List.mem_flatMap.mpr ⟨a, ha,
      List.mem_map.mpr ⟨b, hb, rfl⟩⟩)
  · intro hall q hq
    rcases List.mem_flatMap.mp hq with ⟨a, ha, hq⟩
    rcases List.mem_map.mp hq with ⟨b, hb, rfl⟩
    exact hall a ha b hb

def boundedPair (ps : Clause) (m : Nat) (lo hi : Affine) : QF :=
  .disjunction ((List.range m).map fun k : Nat =>
    let x := lo.add (.const (k : Int))
    .and (.atom (.le (hi.add x.neg))) (periodicAt ps x))

theorem eval_boundedPair_iff (ps : Clause) (m : Nat) (lo hi : Affine)
    (xs : List Int) :
    (boundedPair ps m lo hi).eval xs = true ↔
      ∃ k : Nat, k < m ∧ lo.eval xs + k ≤ hi.eval xs ∧
        DNF.evalClause ps ((lo.eval xs + (k : Int)) :: xs) = true := by
  rw [boundedPair, QF.eval_disjunction, List.any_eq_true]
  constructor
  · rintro ⟨q, hq, hqtrue⟩
    rcases List.mem_map.mp hq with ⟨k, hk, rfl⟩
    change ((QF.atom (.le (hi.add (lo.add (.const k)).neg))).eval xs &&
      (periodicAt ps (lo.add (.const k))).eval xs) = true at hqtrue
    rcases Bool.and_eq_true_iff.mp hqtrue with ⟨hatom, hp⟩
    have hnonneg : 0 ≤ (hi.add (lo.add (.const k)).neg).eval xs := by
      change decide (0 ≤ (hi.add (lo.add (.const k)).neg).eval xs) = true at hatom
      exact of_decide_eq_true hatom
    refine ⟨k, by simpa using hk, ?_, ?_⟩
    · simp at hnonneg
      omega
    · rw [eval_periodicAt] at hp
      simpa using hp
  · rintro ⟨k, hk, hle, hp⟩
    refine ⟨QF.and (QF.atom (.le (hi.add (lo.add (.const k)).neg)))
      (periodicAt ps (lo.add (.const k))), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨k, by simpa using hk, rfl⟩
    · change ((QF.atom (.le (hi.add (lo.add (.const k)).neg))).eval xs &&
        (periodicAt ps (lo.add (.const k))).eval xs) = true
      apply Bool.and_eq_true_iff.mpr
      constructor
      · change decide (0 ≤ (hi.add (lo.add (.const k)).neg).eval xs) = true
        apply decide_eq_true
        simp only [Affine.eval_add, Affine.eval_neg, Affine.eval_const]
        omega
      · rw [eval_periodicAt]
        simpa using hp

def elimVariable (c : Clause) : QF :=
  if (c.filterMap lowerBound?).isEmpty ||
      (c.filterMap upperBound?).isEmpty then
    .disjunction ((List.range (period c)).map fun k : Nat =>
      periodicAt (c.filterMap periodic?) (.const (k : Int)))
  else
    .conjList ((c.filterMap lowerBound?).flatMap fun lo =>
      (c.filterMap upperBound?).map fun hi =>
        boundedPair (c.filterMap periodic?) (period c) lo hi)

theorem eval_elimVariable_finite (c : Clause) (xs : List Int) :
    (elimVariable c).eval xs = true ↔
      if (c.filterMap lowerBound?).isEmpty ||
          (c.filterMap upperBound?).isEmpty then
        ∃ k : Nat, k < period c ∧
          DNF.evalClause (c.filterMap periodic?) ((k : Int) :: xs) = true
      else
        ∀ lo ∈ c.filterMap lowerBound?, ∀ hi ∈ c.filterMap upperBound?,
          ∃ k : Nat, k < period c ∧ lo.eval xs + k ≤ hi.eval xs ∧
    DNF.evalClause (c.filterMap periodic?)
              ((lo.eval xs + (k : Int)) :: xs) = true := by
  by_cases hcond : ((c.filterMap lowerBound?).isEmpty ||
    (c.filterMap upperBound?).isEmpty) = true
  · rw [elimVariable, if_pos hcond, if_pos hcond,
      eval_disjunction_map_iff]
    constructor
    · rintro ⟨k, hk, hp⟩
      exact ⟨k, by simpa using hk, by simpa using hp⟩
    · rintro ⟨k, hk, hp⟩
      exact ⟨k, by simpa using hk, by simpa using hp⟩
  · rw [elimVariable, if_neg hcond, if_neg hcond, eval_conjGrid_iff]
    constructor
    · intro hall lo hlo hi hhi
      exact (eval_boundedPair_iff (c.filterMap periodic?) (period c) lo hi xs).mp
        (hall lo hlo hi hhi)
    · intro hall lo hlo hi hhi
      exact (eval_boundedPair_iff (c.filterMap periodic?) (period c) lo hi xs).mpr
        (hall lo hlo hi hhi)

theorem eval_elimVariable_iff (c : Clause) (xs : List Int) :
    (elimVariable c).eval xs = true ↔
      ∃ x : Int,
        (∀ lo ∈ c.filterMap lowerBound?, lo.eval xs ≤ x) ∧
        (∀ hi ∈ c.filterMap upperBound?, x ≤ hi.eval xs) ∧
        DNF.evalClause (c.filterMap periodic?) (x :: xs) = true := by
  let P : Int → Prop := fun x =>
    DNF.evalClause (c.filterMap periodic?) (x :: xs) = true
  let lows := c.filterMap lowerBound?
  let highs := c.filterMap upperBound?
  have hper : ∀ x, P (x + period c) ↔ P x := by
    intro x
    change DNF.evalClause (c.filterMap periodic?)
        ((x + (period c : Int)) :: xs) = true ↔
      DNF.evalClause (c.filterMap periodic?) (x :: xs) = true
    rw [eval_periodic_filter]
  have hcriterion := cooper_finite_criterion (period_pos c) hper
    (lows.map (fun t : Affine => t.eval xs))
    (highs.map (fun t : Affine => t.eval xs))
  have hfinite :
      (if lows.isEmpty || highs.isEmpty then
          ∃ k : Nat, k < period c ∧ P (k : Int)
        else
          ∀ lo ∈ lows, ∀ hi ∈ highs,
            ∃ k : Nat, k < period c ∧ lo.eval xs + (k : Int) ≤ hi.eval xs ∧
              P (lo.eval xs + (k : Int))) ↔
      (if (lows.map (fun t : Affine => t.eval xs)).isEmpty ||
          (highs.map (fun t : Affine => t.eval xs)).isEmpty then
          ∃ k : Nat, k < period c ∧ P (k : Int)
        else
          ∀ lo ∈ lows.map (fun t : Affine => t.eval xs),
            ∀ hi ∈ highs.map (fun t : Affine => t.eval xs),
            ∃ k : Nat, k < period c ∧ lo + (k : Int) ≤ hi ∧
              P (lo + (k : Int))) := by
    simp only [List.isEmpty_map]
    split
    · rfl
    · constructor
      · intro hall lo hlo hi hhi
        rcases List.mem_map.mp hlo with ⟨lo', hlo', rfl⟩
        rcases List.mem_map.mp hhi with ⟨hi', hhi', rfl⟩
        exact hall lo' hlo' hi' hhi'
      · intro hall lo hlo hi hhi
        exact hall (lo.eval xs) (List.mem_map.mpr ⟨lo, hlo, rfl⟩)
          (hi.eval xs) (List.mem_map.mpr ⟨hi, hhi, rfl⟩)
  have hexists :
      (∃ x : Int,
        (∀ lo ∈ lows.map (fun t : Affine => t.eval xs), lo ≤ x) ∧
        (∀ hi ∈ highs.map (fun t : Affine => t.eval xs), x ≤ hi) ∧ P x) ↔
      ∃ x : Int,
        (∀ lo ∈ lows, lo.eval xs ≤ x) ∧
        (∀ hi ∈ highs, x ≤ hi.eval xs) ∧ P x := by
    constructor
    · rintro ⟨x, hlo, hhi, hp⟩
      exact ⟨x,
        (fun lo h => hlo (lo.eval xs) (List.mem_map.mpr ⟨lo, h, rfl⟩)),
        (fun hi h => hhi (hi.eval xs) (List.mem_map.mpr ⟨hi, h, rfl⟩)), hp⟩
    · rintro ⟨x, hlo, hhi, hp⟩
      refine ⟨x, ?_, ?_, hp⟩
      · intro lo h
        rcases List.mem_map.mp h with ⟨lo', hlo', rfl⟩
        exact hlo lo' hlo'
      · intro hi h
        rcases List.mem_map.mp h with ⟨hi', hhi', rfl⟩
        exact hhi hi' hhi'
  exact (eval_elimVariable_finite c xs).trans (by
    simpa [P, lows, highs] using
      (hfinite.trans (hcriterion.symm.trans hexists)))

def elimNormalizedClause (c : Clause) : QF :=
  let fixed := c.filterMap fixed?
  .and (.conjunction fixed) (elimVariable c)

theorem elimNormalizedClause_correct (c : Clause) (hc : NormalClause c)
    (xs : List Int) :
    (elimNormalizedClause c).eval xs = true ↔
      ∃ x : Int, DNF.evalClause c (x :: xs) = true := by
  constructor
  · intro he
    have he' :
        DNF.evalClause (c.filterMap fixed?) xs = true ∧
          (elimVariable c).eval xs = true := by
      have heQ : ((QF.conjunction (c.filterMap fixed?)).eval xs &&
          (elimVariable c).eval xs) = true := by
        simpa only [elimNormalizedClause, QF.eval] using he
      rw [QF.eval_conjunction] at heQ
      exact Bool.and_eq_true_iff.mp heQ
    rcases he' with ⟨hfixed, hvar⟩
    rcases (eval_elimVariable_iff c xs).mp hvar with ⟨x, hlo, hhi, hp⟩
    exact ⟨x, (eval_normalizedClause_iff c hc x xs).mpr
      ⟨hfixed, hlo, hhi, hp⟩⟩
  · rintro ⟨x, hx⟩
    rcases (eval_normalizedClause_iff c hc x xs).mp hx with
      ⟨hfixed, hlo, hhi, hp⟩
    have hvar := (eval_elimVariable_iff c xs).mpr ⟨x, hlo, hhi, hp⟩
    have heQ : ((QF.conjunction (c.filterMap fixed?)).eval xs &&
        (elimVariable c).eval xs) = true := by
      rw [QF.eval_conjunction]
      exact Bool.and_eq_true_iff.mpr ⟨hfixed, hvar⟩
    simpa only [elimNormalizedClause, QF.eval] using heQ

def elimClause (c : Clause) : QF :=
  elimNormalizedClause (normalizeClause c)

theorem elimClause_correct (c : Clause) (xs : List Int) :
    (elimClause c).eval xs = true ↔
      ∃ x : Int, DNF.evalClause c (x :: xs) = true := by
  rw [elimClause, elimNormalizedClause_correct _ (normalClause_normalizeClause c)]
  exact (normalizeClause_exists_iff c xs).symm

def eliminate (p : QF) : QF :=
  .disjunction ((DNF.ofPolarity true p).map elimClause)

theorem eliminate_correct (p : QF) (xs : List Int) :
    (eliminate p).eval xs = true ↔ ∃ x : Int, p.eval (x :: xs) = true := by
  let d := DNF.ofPolarity true p
  constructor
  · intro he
    rw [eliminate, QF.eval_disjunction, List.any_eq_true] at he
    rcases he with ⟨q, hq, hqtrue⟩
    rcases List.mem_map.mp hq with ⟨c, hc, rfl⟩
    rcases (elimClause_correct c xs).mp hqtrue with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hd : DNF.eval (DNF.ofPolarity true p) (x :: xs) = true :=
      List.any_eq_true.mpr ⟨c, hc, hx⟩
    simpa [DNF.eval_ofPolarity] using hd
  · rintro ⟨x, hx⟩
    have hd : DNF.eval (DNF.ofPolarity true p) (x :: xs) = true := by
      simpa [DNF.eval_ofPolarity] using hx
    rcases List.any_eq_true.mp hd with ⟨c, hc, hcx⟩
    rw [eliminate, QF.eval_disjunction, List.any_eq_true]
    exact ⟨elimClause c, List.mem_map.mpr ⟨c, hc, rfl⟩,
      (elimClause_correct c xs).mpr ⟨x, hcx⟩⟩

end Cooper

end PresburgerArithmetic
