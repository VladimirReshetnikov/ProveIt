import StandardReading

/-! Finite tests for the exact dyadic prime-product estimate.
All results in this file concern the standard natural number interpretation.
The probes, bounds, and accumulators use only primitive recursion. -/
namespace RiemannIPRA.Discrete
open LeanProofs.ConciseIPRA PacketLanguage

def args3 (a b c : Nat) : Fin 3 → Nat :=
  Fin.cases a (Fin.cases b (fun _ => c))

private theorem env3 (e : Fin 3 → Nat) : e = args3 (e 0) (e 1) (e 2) := by
  funext i
  refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => ?_) i) i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i; rfl

private theorem env5 (e : Fin 5 → Nat) : e = packetArgs (e 0) (e 1) (e 2) (e 3) (e 4) := by
  funext i
  refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl
    (fun i => Fin.cases rfl (fun i => ?_) i) i) i) i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i; rfl

section Interpreter
variable {ctx : List String}
theorem plus (a b : E ctx) (e) :
    denote (a+b) e = denote a e + denote b e := by
  change value addR _ = _
  rw [value_addR]; rfl
theorem times (a b : E ctx) (e) :
    denote (a*b) e = denote a e * denote b e := by
  change value mulR _ = _
  rw [value_mulR]; rfl
theorem minus (a b : E ctx) (e) :
    denote (a-b) e = denote a e - denote b e := by
  change value subR _ = _
  rw [value_subR]; rfl
theorem power (a b : E ctx) (e) :
    denote (powE a b) e = denote a e ^ denote b e := by
  change value powR _ = _
  rw [value_powR]; rfl
theorem apply3 (f : PR 3) (a b c : E ctx) (e) :
    denote (call f [a,b,c]) e = value f (args3 (denote a e) (denote b e) (denote c e)) :=
  congrArg (value f) (env3 _)
theorem apply5 (f : PR 5) (a b c d t : E ctx) (e) :
    denote (call f [a,b,c,d,t]) e = value f
      (packetArgs (denote a e) (denote b e) (denote c e) (denote d e) (denote t e)) :=
  congrArg (value f) (env5 _)
end Interpreter

/-- Parameters are the degree offset and the three coefficient codes. -/
structure Data where
  degreeOffset : Nat
  height : Nat
  pos : Nat
  neg : Nat

def Data.logP (p : Data) (n : Nat) : Nat :=
  value logProduct (packetArgs (p.degreeOffset+1) p.height p.pos p.neg n)

def Data.cost (p : Data) (n : Nat) : Nat :=
  n * (value allowance (args3 (p.degreeOffset+1) p.height n))^2

def delta (a b : Nat) : Nat := (a-b)+(b-a)

def Data.gap (p : Data) (n : Nat) : Nat := delta (p.logP (2*n)) (2*p.logP n)

def Data.test (p : Data) (t : Nat) : Prop := p.gap (t+100) ^ 2 ≤ p.cost (t+100)

private theorem read_gap (p : Data) (n : Nat) :
    value dyadicGap (packetArgs (p.degreeOffset+1) p.height p.pos p.neg n) = p.gap n := by
  unfold dyadicGap; rw [value_program]
  simp only [plus, minus, times, apply5]
  rfl

theorem read_test (p : Data) (t : Nat) :
    value excess (packetArgs p.degreeOffset p.height p.pos p.neg t) = 0 ↔ p.test t := by
  unfold excess; rw [value_program]
  simp only [minus, power, times, apply5, apply3, plus, Nat.sub_eq_zero_iff_le]
  change value dyadicGap (packetArgs (p.degreeOffset+1) p.height p.pos p.neg (t+100)) ^ 2 ≤ _ ↔ _
  rw [read_gap]
  rfl


/-- Integer Young inequality, with the maximizing slope supplied explicitly. -/
private theorem young (q g : Nat) : 2*q*g ≤ q*q+g*g := by
  rcases Nat.le_total q g with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm k q, Nat.mul_assoc]
    omega
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm k g, Nat.mul_assoc]
    omega

theorem fenchel (g C : Nat) : g^2 ≤ C ↔ ∀ q : Nat, 2*q*g ≤ q*q+C := by
  constructor
  · intro h q
    exact (young q g).trans (Nat.add_le_add_left (by simpa [Nat.pow_succ] using h) _)
  · intro h
    have hh := h g
    rw [Nat.mul_assoc] at hh
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using (show g*g ≤ C by omega)

def TwoSided (a b r : Nat) : Prop := a ≤ b+r ∧ b ≤ a+r

private theorem probe (a b q r : Nat) :
    2*q*delta a b ≤ r ↔ TwoSided (2*q*a) (2*q*b) r := by
  rcases Nat.le_total a b with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [delta, Nat.add_sub_cancel_left, Nat.sub_eq_zero_of_le (Nat.le_add_right _ _),
      Nat.zero_add, TwoSided, Nat.mul_add]
    omega
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [delta, Nat.add_sub_cancel_left, Nat.sub_eq_zero_of_le (Nat.le_add_right _ _),
      Nat.add_zero, TwoSided, Nat.mul_add]
    omega

def Data.dual (p : Data) : Prop := ∀ t q : Nat,
  TwoSided (2*q*p.logP (2*(t+100))) (2*(2*q*p.logP (t+100))) (q*q+p.cost (t+100))

theorem dual_iff (p : Data) : (∀ t, p.test t) ↔ p.dual := by
  have step (t q : Nat) : 2*q*p.gap (t+100) ≤ q*q+p.cost (t+100) ↔
      TwoSided (2*q*p.logP (2*(t+100))) (2*(2*q*p.logP (t+100))) (q*q+p.cost (t+100)) := by
    simpa only [Data.gap, Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using
      probe (p.logP (2*(t+100))) (2*p.logP (t+100)) q (q*q+p.cost (t+100))
  constructor
  · intro h t q
    exact (step t q).mp ((fenchel _ _).mp (h t) q)
  · intro h t
    exact (fenchel _ _).mpr (fun q => (step t q).mpr (h t q))

/-- Double k times. This is definitionally the homogeneous part of the recurrence. -/
def doubleAt (x : Nat) : Nat → Nat
  | 0 => x
  | k+1 => 2 * doubleAt x k

theorem doubleAt_eq (x k : Nat) : doubleAt x k = 2^k*x := by
  induction k with
  | zero => simp [doubleAt]
  | succ k ih => simp [doubleAt, ih, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm]

/-- Aggregate local allowances with their dyadic propagation factors. -/
def Data.chainBudget (p : Data) (n q : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => 2*p.chainBudget n q k + (q*q+p.cost (doubleAt n k))

def Data.chain (p : Data) : Prop := ∀ t k q : Nat,
  TwoSided (2*q*p.logP (doubleAt (t+100) k))
    (doubleAt (2*q*p.logP (t+100)) k) (p.chainBudget (t+100) q k)

theorem chain_iff (p : Data) : p.dual ↔ p.chain := by
  constructor
  · intro h t k q
    induction k with
    | zero => simp [doubleAt, Data.chainBudget, TwoSided]
    | succ k ih =>
      let x := doubleAt (t+100) k
      have hx : 100 ≤ x := by
        change 100 ≤ doubleAt (t+100) k
        clear ih
        induction k with
        | zero => simp [doubleAt]
        | succ k hk => simp only [doubleAt]; omega
      have s := h (x-100) q
      rw [Nat.sub_add_cancel hx] at s
      obtain ⟨s₁,s₂⟩ := s
      obtain ⟨i₁,i₂⟩ := ih
      change 2*q*p.logP (2*x) ≤ 2*doubleAt (2*q*p.logP (t+100)) k +
          (2*p.chainBudget (t+100) q k + (q*q+p.cost x)) ∧ _
      change 2*q*p.logP x ≤ _ at i₁
      change _ ≤ 2*q*p.logP x + _ at i₂
      change _ ∧ 2*doubleAt (2*q*p.logP (t+100)) k ≤
          2*q*p.logP (2*x) + (2*p.chainBudget (t+100) q k + (q*q+p.cost x))
      omega
  · intro h t q
    simpa only [doubleAt, Data.chainBudget, Nat.mul_zero, Nat.zero_add] using h t 1 q

/-- Bounded prefix sum. -/
def total (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t+1 => total a t + a t

def Data.energy (p : Data) (t : Nat) := p.gap (t+100)^2
def Data.budget (p : Data) (t : Nat) := p.cost (t+100)

/-- Arbitrary natural digit weights, all specified by just two natural parameters. -/
def weightDigit (b w i : Nat) := (w/b^i) % b

def Data.weighted (p : Data) : Prop := ∀ s k b w : Nat,
  total (fun i => weightDigit b w i * p.energy (s+i)) k ≤
  total (fun i => weightDigit b w i * p.budget (s+i)) k

theorem weighted_iff (p : Data) : (∀ t, p.test t) ↔ p.weighted := by
  constructor
  · intro h s k b w
    induction k with
    | zero => exact Nat.le_refl 0
    | succ k ih =>
      exact Nat.add_le_add ih (Nat.mul_le_mul_left _ (h (s+k)))
  · intro h t
    simpa [total, weightDigit, Data.test, Data.energy, Data.budget] using h t 1 2 1

/-- Two prefix sums encode the signed slack without subtraction. -/
def Data.increments (p : Data) : Prop := ∀ s k : Nat,
  total p.energy (s+k) + total p.budget s ≤ total p.budget (s+k) + total p.energy s

theorem increments_iff (p : Data) : (∀ t, p.test t) ↔ p.increments := by
  constructor
  · intro h s k
    induction k with
    | zero => simp [Nat.add_comm]
    | succ k ih =>
      have hh : p.energy (s+k) ≤ p.budget (s+k) := h (s+k)
      change (total p.energy (s+k) + p.energy (s+k)) + total p.budget s ≤
        (total p.budget (s+k) + p.budget (s+k)) + total p.energy s
      omega
  · intro h s
    have hh := h s 1
    change (total p.energy s + p.energy s) + total p.budget s ≤
      (total p.budget s + p.budget s) + total p.energy s at hh
    change p.energy s ≤ p.budget s
    omega

/-- Mixed-radix place value at the next index, based solely on its budgets. -/
def radix (C : Nat → Nat) : Nat → Nat
  | 0 => 1
  | t+1 => radix C t * (C t+1)

private theorem radix_budget (C : Nat → Nat) (t : Nat) :
    total (fun i => radix C i * C i) t + 1 = radix C t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [total, radix, Nat.mul_add, Nat.mul_one]
    omega

def packed (E C : Nat → Nat) : Prop := ∀ k,
  total (fun i => radix C i * E i) k ≤ total (fun i => radix C i * C i) k

/-- All prefix budgets suffice after applying these particular place values.
No singleton intervals occur except the very first prefix. -/
theorem packed_iff (E C : Nat → Nat) : (∀ i, E i ≤ C i) ↔ packed E C := by
  constructor
  · intro h k
    induction k with
    | zero => exact Nat.le_refl 0
    | succ k ih => exact Nat.add_le_add ih (Nat.mul_le_mul_left _ (h k))
  · intro h i
    have hi := h (i+1)
    simp only [total] at hi
    have hr := radix_budget C i
    by_cases good : E i ≤ C i
    · exact good
    · have hh : C i+1 ≤ E i := by omega
      have hm := Nat.mul_le_mul_left (radix C i) hh
      simp only [Nat.mul_add, Nat.mul_one] at hm
      omega


section Syntax

/-- Separate the comparison in the supplied matrix into its two sides. -/
def energyCode : PR 5 := program ["d","H","u","v","t"] <|
  powE (call dyadicGap [v "d"+1,v "H",v "u",v "v",v "t"+100]) 2

def budgetCode : PR 5 := program ["d","H","u","v","t"] <|
  (v "t"+100) * powE (call allowance [v "d"+1,v "H",v "t"+100]) 2

def placeCode : PR 5 := program ["d","H","u","v","t"] <|
  prodTo "j" (v "t") (call budgetCode [v "d",v "H",v "u",v "v",v "j"]+1)

def prefixCode (f : PR 5) : PR 5 := program ["d","H","u","v","t"] <|
  sumTo "j" (v "t") (call placeCode [v "d",v "H",v "u",v "v",v "j"] *
    call f [v "d",v "H",v "u",v "v",v "j"])

def packedMatrix : PR 5 := program ["d","H","u","v","t"] <|
  call (prefixCode energyCode) [v "d",v "H",v "u",v "v",v "t"] -
  call (prefixCode budgetCode) [v "d",v "H",v "u",v "v",v "t"]

def Data.args (p : Data) (t : Nat) := packetArgs p.degreeOffset p.height p.pos p.neg t

theorem energy_ok (p : Data) (t : Nat) : value energyCode (p.args t) = p.energy t := by
  unfold energyCode; rw [value_program]
  simp only [power, apply5, plus]
  change _ ^ 2 = _
  apply congrArg (·^2) (read_gap p (t+100))

theorem budget_ok (p : Data) (t : Nat) : value budgetCode (p.args t) = p.budget t := by
  unfold budgetCode; rw [value_program]
  simp only [times, power, apply3, plus]; rfl

theorem place_ok (p : Data) (t : Nat) :
    value placeCode (p.args t) = radix p.budget t := by
  unfold placeCode; rw [value_program]
  change overRange 1 (fun j a => a * @denote ["j","d","H","u","v","t"] _ (Fin.cases j (p.args t))) t = _
  simp only [plus, apply5]
  change overRange 1 (fun j a => a * (value budgetCode (p.args j) + 1)) t = _
  simp only [budget_ok]
  induction t with
  | zero => rfl
  | succ t ih => exact congrArg (· * (p.budget t+1)) ih

private theorem prefix_ok (p : Data) (f : PR 5) (t : Nat) :
    value (prefixCode f) (p.args t) = total (fun j => radix p.budget j * value f (p.args j)) t := by
  unfold prefixCode; rw [value_program]
  change overRange 0 (fun j a => a + @denote ["j","d","H","u","v","t"] _ (Fin.cases j (p.args t))) t = _
  simp only [times, apply5]
  change overRange 0 (fun j a => a + value placeCode (p.args j) * value f (p.args j)) t = _
  simp only [place_ok]
  induction t with
  | zero => rfl
  | succ t ih => exact congrArg (· + radix p.budget t * value f (p.args t)) ih

theorem packedMatrix_ok (p : Data) (k : Nat) : value packedMatrix (p.args k) = 0 ↔
    total (fun i => radix p.budget i * p.energy i) k ≤
      total (fun i => radix p.budget i * p.budget i) k := by
  unfold packedMatrix; rw [value_program]
  simp only [minus, apply5, Nat.sub_eq_zero_iff_le]
  change value (prefixCode energyCode) (p.args k) ≤ value (prefixCode budgetCode) (p.args k) ↔ _
  simp only [prefix_ok, energy_ok, budget_ok]

end Syntax

inductive Family where | riemann | dirichlet | dedekind

def Family.close : Family → PR 5 → Fm PTm 0
  | .riemann => RHHierarchy.RHOf
  | .dirichlet => RHHierarchy.GRHOf
  | .dedekind => RHHierarchy.ERHOf

def Family.allData : Family → (Data → Prop) → Prop
  | .riemann, P => P ⟨0,0,0,1⟩
  | .dirichlet, P => ∀ d, P ⟨d,0,0,1⟩
  | .dedekind, P => ∀ d H u v, P ⟨d,H,u,v⟩

theorem Family.lift_iff (f : Family) {P Q : Data → Prop} (h : ∀ p, P p ↔ Q p) :
    f.allData P ↔ f.allData Q := by
  cases f <;> simp only [Family.allData, h]

private theorem atom_ok {n} (f : PR 5) (d H u v t : PTm n) (e : Fin n → Nat) :
    naturalTerms.Holds (RHHierarchy.atom f d H u v t) e ↔
      value f (packetArgs (termValue d e) (termValue H e) (termValue u e)
        (termValue v e) (termValue t e)) = 0 := by
  change value f _ = 0 ↔ _
  rw [env5 (fun i => termValue (Fin.cases d (Fin.cases H (Fin.cases u
      (Fin.cases v (fun _ => t)))) i) e)]
  rfl

theorem all_ok {n} (A : Fm PTm (n+1)) (e : Fin n → Nat) :
    naturalTerms.Holds (.all A) e ↔ ∀ x, naturalTerms.Holds A (Fin.cases x e) := Iff.rfl

theorem Family.holds_matrix (s : Family) (f : PR 5) : naturalTerms.Holds (s.close f) Fin.elim0 ↔
    s.allData (fun p => ∀ t, value f (p.args t) = 0) := by
  cases s <;> simp only [Family.close, Family.allData, RHHierarchy.RHOf, RHHierarchy.GRHOf,
    RHHierarchy.ERHOf, all_ok, atom_ok] <;> rfl

inductive Form where | localTest | linearProbe | dyadicChain | weightedWindow | prefixIncrement | radixPrefix

def Form.meaning : Form → Data → Prop
  | .localTest, p => ∀ t, p.test t
  | .linearProbe, p => p.dual
  | .dyadicChain, p => p.chain
  | .weightedWindow, p => p.weighted
  | .prefixIncrement, p => p.increments
  | .radixPrefix, p => packed p.energy p.budget

theorem forms_iff (p : Data) (k : Form) : (∀ t, p.test t) ↔ k.meaning p := by
  cases k with
  | localTest => rfl
  | linearProbe => exact dual_iff p
  | dyadicChain => exact (dual_iff p).trans (chain_iff p)
  | weightedWindow => exact weighted_iff p
  | prefixIncrement => exact increments_iff p
  | radixPrefix => exact packed_iff p.energy p.budget

/-- Choose independently among the three hypotheses and six numerical presentations. -/
theorem hypothesis_iff (s : Family) (k : Form) :
    naturalTerms.Holds (s.close excess) Fin.elim0 ↔ s.allData k.meaning :=
  (s.holds_matrix excess).trans (s.lift_iff (fun p =>
    (forall_congr' (fun t => read_test p t)).trans (forms_iff p k)))

/-- A second literal closed formula in each family, comparing mixed-radix prefixes. -/
theorem packed_sentence_iff (s : Family) :
    naturalTerms.Holds (s.close excess) Fin.elim0 ↔
    naturalTerms.Holds (s.close packedMatrix) Fin.elim0 := by
  apply (hypothesis_iff s .radixPrefix).trans
  apply Iff.trans _ (s.holds_matrix packedMatrix).symm
  exact s.lift_iff (fun p => (forall_congr' fun k => (packedMatrix_ok p k).symm))

end RiemannIPRA.Discrete
