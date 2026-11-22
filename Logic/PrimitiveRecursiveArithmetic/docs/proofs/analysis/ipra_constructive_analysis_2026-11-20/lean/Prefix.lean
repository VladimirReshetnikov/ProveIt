import BitIntegral

namespace BudgetAnalysis.Prefix
open BitIntegral (Hist Oracle)

/-- A partial assignment denotes all total extensions. -/
def Extends (x : Oracle) (h : Hist) : Prop :=
  ∀ i b, h i = some b → x i = b

def AgreeTo (n : Nat) (x y : Oracle) : Prop := ∀ i, i < n → x i = y i

def Compatible (n : Nat) (u v : Hist) : Prop :=
  ∀ i, i < n → ∀ b c, u i = some b → v i = some c → b = c

/-- In the prefix, a missing bit is borrowed from the other assignment.
    The unfixed suffix uses false, and forced own bits always take priority. -/
def complete (n : Nat) (u v : Hist) : Oracle := fun i =>
  (u i).getD (if i < n then (v i).getD false else false)

theorem complete_extends (n : Nat) (u v : Hist) : Extends (complete n u v) u := by
  intro i b hi
  simp [complete, hi]

theorem common_prefix_iff (n : Nat) (u v : Hist) :
    Compatible n u v ↔
      ∃ x y, Extends x u ∧ Extends y v ∧ AgreeTo n x y := by
  constructor
  · intro good
    refine ⟨complete n u v, complete n v u, complete_extends n u v, complete_extends n v u, ?_⟩
    intro i hi
    cases hu : u i with
    | none => cases hv : v i <;> simp [complete, hu, hv, hi]
    | some b =>
      cases hv : v i with
      | none => simp [complete, hu, hv, hi]
      | some c => simpa [complete, hu, hv] using good i hi b c hu hv
  · rintro ⟨x, y, ex, ey, same⟩ i hi b c hu hv
    exact (ex i b hu).symm.trans ((same i hi).trans (ey i c hv))

abbrev Sparse := List (Nat × Bool)

def lookup : Sparse → Hist
  | [], _ => none
  | (q,b)::xs, i => if i = q then some b else lookup xs i

theorem mem_keys (xs : Sparse) (i : Nat) (b : Bool) (has : lookup xs i = some b) :
    i ∈ xs.map Prod.fst := by
  induction xs with
  | nil => contradiction
  | cons p xs ih =>
    obtain ⟨j, c⟩ := p
    by_cases h : i = j
    · simp [h]
    · simp [lookup, h] at has
      exact List.mem_cons_of_mem _ (ih has)

def pairOK : Option Bool → Option Bool → Bool
  | some b, some c => b == c
  | _, _ => true

theorem pairOK_iff (u v : Option Bool) :
    pairOK u v = true ↔ ∀ b c, u = some b → v = some c → b = c := by
  cases u <;> cases v <;> simp [pairOK]

/-- Scans the sparse keys even when the largest bit address is enormous. -/
def prefixOK (n : Nat) (u v : Sparse) : Bool :=
  (u.map Prod.fst).all (fun i =>
    if i < n then pairOK (lookup u i) (lookup v i) else true)

theorem prefixOK_spec (n : Nat) (u v : Sparse) :
    prefixOK n u v = true ↔ Compatible n (lookup u) (lookup v) := by
  simp only [prefixOK, List.all_eq_true]
  constructor
  · intro test i hi b c hb hc
    have passed := test i (mem_keys u i b hb)
    simp only [if_pos hi] at passed
    exact (pairOK_iff _ _).mp passed b c hb hc
  · intro good i _
    by_cases hi : i < n
    · simpa [hi] using (pairOK_iff _ _).mpr (good i hi)
    · simp [hi]

/-- A pair is forbidden when its leaf labels are too far apart. -/
def safePrefix (n : Nat) (forbidden : List (Sparse × Sparse)) : Bool :=
  forbidden.all (fun pair => !(prefixOK n pair.1 pair.2))

theorem safePrefix_spec (n : Nat) (forbidden : List (Sparse × Sparse)) :
    safePrefix n forbidden = true ↔
    ∀ z ∈ forbidden, ¬ ∃ x y, Extends x (lookup z.1) ∧
                              Extends y (lookup z.2) ∧ AgreeTo n x y := by
  simp only [safePrefix, List.all_eq_true]
  constructor
  · intro good z hz witness
    have conflict := good z hz
    have ok := (prefixOK_spec n z.1 z.2).mpr ((common_prefix_iff ..).mpr witness)
    simp [ok] at conflict
  · intro good z hz
    cases h : prefixOK n z.1 z.2 with
    | false => rfl
    | true =>
      exact False.elim ((good z hz) ((common_prefix_iff ..).mp ((prefixOK_spec ..).mp h)))

end BudgetAnalysis.Prefix
