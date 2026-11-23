import GraphCore

/-! Bounded certificates for colourings and cliques, and the odd-walk
    obstruction. The two tables may be obtained by digit extraction. -/
namespace GraphIPRA

def allB (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | k+1 => allB p k && p k

theorem allB_iff (p : Nat → Bool) (n : Nat) :
    allB p n = true ↔ ∀ i, i < n → p i = true := by
  induction n with
  | zero => simp [allB]
  | succ n ih =>
    rw [allB, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨head, last⟩ i hi
      by_cases h : i = n
      · simpa [h] using last
      · exact head i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

def properB (n q : Nat) (edge : Nat → Nat → Bool) (colour : Nat → Nat) : Bool :=
  allB (fun u => decide (colour u < q) &&
    allB (fun v => decide (edge u v = true → colour u ≠ colour v)) n) n

theorem properB_iff (n q : Nat) (edge : Nat → Nat → Bool) (colour : Nat → Nat) :
    properB n q edge colour = true ↔
    ∀ u, u < n → (colour u < q ∧
      ∀ v, v < n → edge u v = true → colour u ≠ colour v) := by
  simp only [properB, allB_iff, Bool.and_eq_true, decide_eq_true_eq]

/-- The list of clique vertices has length r. On a loopless graph the
    pair tests also force its entries to be distinct. -/
def cliqueB (n r : Nat) (edge : Nat → Nat → Bool) (vertex : Nat → Nat) : Bool :=
  allB (fun i => decide (vertex i < n) &&
    allB (fun j => decide (i ≠ j → edge (vertex i) (vertex j) = true)) r) r

theorem cliqueB_iff (n r : Nat) (edge : Nat → Nat → Bool) (vertex : Nat → Nat) :
    cliqueB n r edge vertex = true ↔
    ∀ i, i < r → (vertex i < n ∧
      ∀ j, j < r → i ≠ j → edge (vertex i) (vertex j) = true) := by
  simp only [cliqueB, allB_iff, Bool.and_eq_true, decide_eq_true_eq]

theorem differentCliqueColours {n q r : Nat} {edge : Nat → Nat → Bool}
    {vertex colour : Nat → Nat} (hc : properB n q edge colour = true)
    (hk : cliqueB n r edge vertex = true)
    {i j : Nat} (hi : i < r) (hj : j < r) (hij : i ≠ j) :
    colour (vertex i) ≠ colour (vertex j) := by
  have colours := (properB_iff ..).mp hc
  have vertices := (cliqueB_iff ..).mp hk
  exact (colours _ (vertices i hi).1).2 _
    (vertices j hj).1 ((vertices i hi).2 j hj hij)

def alternatingB (n : Nat) (edge : Nat → Nat → Bool) (colour : Nat → Bool) : Bool :=
  allB (fun u => allB (fun v =>
    decide (edge u v = true → colour v = !colour u)) n) n

theorem alternatingB_iff (n : Nat) (edge : Nat → Nat → Bool) (colour : Nat → Bool) :
    alternatingB n edge colour = true ↔
    ∀ u, u < n → ∀ v, v < n → edge u v = true → colour v = !colour u := by
  simp only [alternatingB, allB_iff, decide_eq_true_eq]

def flipN (b : Bool) : Nat → Bool
  | 0 => b
  | k+1 => !(flipN b k)

theorem Walk.colour {edge n s k v} (p : Walk edge n s k v)
    (c : Nat → Bool) (hc : alternatingB n edge c = true) :
    c v = flipN (c s) k := by
  have h := (alternatingB_iff ..).mp hc
  induction p with
  | nil => rfl
  | snoc path hv he ih =>
    rw [flipN, ← ih]
    exact h _ path.end_lt _ hv he

theorem flipN_even (b : Bool) (t : Nat) : flipN b (2*t) = b := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Nat.mul_succ]
    change (!(!(flipN b (2*t)))) = b
    simp [ih]

theorem noOddClosedWalk {edge n s t} (c : Nat → Bool)
    (hc : alternatingB n edge c = true) (p : Walk edge n s (2*t+1) s) : False := by
  have bad := p.colour c hc
  rw [flipN, flipN_even] at bad
  cases h : c s <;> simp [h] at bad

end GraphIPRA
