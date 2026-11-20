import Dialogue

namespace BudgetAnalysis.BitIntegral

abbrev Oracle := Nat → Bool
abbrev Hist := Nat → Option Bool
abbrev T := Dialogue Nat (fun _ => Bool) Int

def record (h : Hist) (q : Nat) (b : Bool) : Hist :=
  fun i => if i = q then some b else h i

/-- Exact numerator when m is the number of assignments represented by h.
    The certificate below states the divisibility and balance facts needed. -/
def weighted : T → Hist → Nat → Int
  | .ret z, _, m => (m : Int) * z
  | .ask q next, h, m =>
    match h q with
    | some b => weighted (next b) h m
    | none => weighted (next false) (record h q false) (m/2) +
              weighted (next true) (record h q true) (m/2)

def total (v : Oracle → Int) : List Oracle → Int
  | [] => 0
  | x :: xs => v x + total v xs

def side (xs : List Oracle) (q : Nat) (b : Bool) := xs.filter (fun o => o q == b)

theorem total_const (xs : List Oracle) (z : Int) :
    total (fun _ => z) xs = (xs.length : Int) * z := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih => simp [total, ih, Int.add_mul, Int.add_comm]

theorem total_congr (xs : List Oracle) (f g : Oracle → Int)
    (eqn : ∀ o ∈ xs, f o = g o) : total f xs = total g xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have hd := eqn a (by simp)
    have tl := ih (fun o ho => eqn o (by simp [ho]))
    simp [total, hd, tl]

theorem total_partition (xs : List Oracle) (q : Nat) (f : Bool → Oracle → Int) :
    total (fun o => f (o q) o) xs =
    total (f false) (side xs q false) + total (f true) (side xs q true) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : a q <;> simp [total, side, h] at ih ⊢ <;> omega

/-- Semantic invariant. Each fresh split has two equally large populations;
    each cached answer is forced on the current population. -/
def Calibrated : T → Hist → List Oracle → Prop
  | .ret _, _, _ => True
  | .ask q next, h, xs =>
    match h q with
    | some b => (∀ o ∈ xs, o q = b) ∧ Calibrated (next b) h xs
    | none =>
      (side xs q false).length = xs.length / 2 ∧
      (side xs q true).length = xs.length / 2 ∧
      Calibrated (next false) (record h q false) (side xs q false) ∧
      Calibrated (next true) (record h q true) (side xs q true)

theorem weighted_correct (t : T) (h : Hist) (xs : List Oracle)
    (hc : Calibrated t h xs) :
    weighted t h xs.length = total (fun o => Dialogue.eval o t) xs := by
  induction t generalizing h xs with
  | ret r => exact (total_const xs r).symm
  | ask q next ih =>
    cases hq : h q with
    | some b =>
      simp only [Calibrated, hq] at hc
      simp only [weighted, hq]
      rw [ih b h xs hc.2]
      apply total_congr
      intro o ho
      simp only [Dialogue.eval, hc.1 o ho]
    | none =>
      simp only [Calibrated, hq] at hc
      change weighted (.ask q next) h xs.length =
        total (fun o => Dialogue.eval o (next (o q))) xs
      rw [total_partition xs q (fun b o => Dialogue.eval o (next b))]
      simp only [weighted, hq]
      obtain ⟨lf, lt, cf, ct⟩ := hc
      have hf := ih false _ _ cf
      have ht := ih true _ _ ct
      rw [lf] at hf
      rw [lt] at ht
      rw [hf, ht]

end BudgetAnalysis.BitIntegral
