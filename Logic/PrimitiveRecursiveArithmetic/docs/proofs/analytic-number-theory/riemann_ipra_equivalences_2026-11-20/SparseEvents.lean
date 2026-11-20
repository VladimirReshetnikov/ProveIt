import DiscreteForms

/-! Only the initial cutoff and endpoints at which a rational prime power can
enter one of the two underlying prime products need be inspected. -/
namespace RiemannIPRA.Sparse
open LeanProofs.ConciseIPRA PacketLanguage Discrete

private theorem leE {ctx} (a b : E ctx) (e) :
    denote (leB a b) e = (if denote a e ≤ denote b e then 1 else 0) := by
  change value isZeroR _ = _
  rw [value_isZeroR]
  change (if denote (a-b) e = 0 then 1 else 0) = _
  simp [minus, Nat.sub_eq_zero_iff_le]

private theorem eqE {ctx} (a b : E ctx) (e) :
    denote (eqB a b) e = (if denote a e = denote b e then 1 else 0) := by
  simp only [eqB, times, leE]
  split <;> split <;> split <;> first | rfl | omega

private theorem iteEval {ctx} (t a b : E ctx) (e) :
    denote (iteE t a b) e = (if denote t e = 0 then denote b e else denote a e) := by
  have hc : ∀ x : E ctx, denote (call clipR [x]) e = bit (denote x e) := fun x => value_clipR _
  have hz : ∀ x : E ctx, denote (call isZeroR [x]) e = (if denote x e = 0 then 1 else 0) :=
    fun x => value_isZeroR _
  simp only [iteE, plus, times, hc, hz, bit]
  split <;> simp

private theorem oneArg {ctx} (f : PR 1) (x : E ctx) (e) :
    denote (call f [x]) e = value f (fun _ => denote x e) := by
  change value f _ = _
  congr 1
  funext i; have h : i = 0 := Subsingleton.elim _ _; subst i; rfl

def pBit (p : Nat) := value primeCode (fun _ => p)

private theorem two_ok : pBit 2 ≠ 0 := by
  have h : value primeCode (fun _ => 2) = 1 := (value_primeCode _).mpr ⟨by decide, by intros; omega⟩
  unfold pBit; omega

private def six (a b c d e f : Nat) : Fin 6 → Nat :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (Fin.cases e (fun _ => f)))))

private theorem sixExt (e : Fin 6 → Nat) : e = six (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) := by
  funext ⟨i,hi⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | n+6 => omega

private theorem sixArg {ctx} (f : PR 6) (a b c d u v : E ctx) (e) :
    denote (call f [a,b,c,d,u,v]) e =
    value f (six (denote a e) (denote b e) (denote c e) (denote d e) (denote u e) (denote v e)) :=
  congrArg (value f) (sixExt _)

private def degVal (D : Data) (p a : Nat) :=
  value PacketPolynomial.rootDegree (six (D.degreeOffset+1) D.height D.pos D.neg p a)

private def prod (f : Nat → Nat) := overRange 1 (fun i a => a*f i)
private def sumF (f : Nat → Nat) := overRange 0 (fun i a => a+f i)

private theorem denProd {ctx} (j : String) (b : E ctx) (f : E (j::ctx)) (e) :
    denote (prodTo j b f) e = prod (fun i => denote f (Fin.cases i e)) (denote b e) := rfl

private theorem denSum {ctx} (j : String) (b : E ctx) (f : E (j::ctx)) (e) :
    denote (sumTo j b f) e = sumF (fun i => denote f (Fin.cases i e)) (denote b e) := rfl

private def factor (D : Data) (x p j : Nat) :=
  if p^(j+1) ≤ x then p^(degVal D p (j+1)) else 1
private def row (D : Data) (x p : Nat) :=
  if pBit p = 0 then 1 else prod (factor D x p) x.log2
private def prodVal (D : Data) (x : Nat) := prod (row D x) (x+1)

private theorem prod_ok (D : Data) (x : Nat) :
    value primeProduct (packetArgs (D.degreeOffset+1) D.height D.pos D.neg x) = prodVal D x := by
  unfold primeProduct
  rw [value_program]
  simp only [denProd, plus, iteEval, oneArg, value_logCode, leE, power, sixArg]
  unfold prodVal
  apply congrArg (fun f => prod f (x+1))
  funext p
  unfold row
  change (if pBit p = 0 then 1 else prod _ x.log2) = _
  by_cases h : pBit p = 0
  · simp [h]
  · simp only [h, if_false]
    congr 1
    funext j
    change (if (if p^(j+1) ≤ x then (1:Nat) else 0) = 0 then 1 else p^degVal D p (j+1)) = _
    unfold factor
    split <;> simp_all

private theorem log_ok (D : Data) (x : Nat) : D.logP x = (prodVal D x).log2 := by
  unfold Data.logP logProduct; rw [value_program]
  simp only [oneArg, apply5, value_logCode]
  exact congrArg Nat.log2 (prod_ok D x)

def HasPower (x : Nat) : Prop := ∃ p, p < x+1 ∧ pBit p ≠ 0 ∧ ∃ j, j < x ∧ p^(j+1) = x

/-- Positive exactly when x is a prime power of positive exponent. -/
def powerCount : PR 1 := program ["x"] <|
  sumTo "p" (v "x"+1) (iteE (call primeCode [v "p"])
    (sumTo "j" (v "x") (eqB (powE (v "p") (v "j"+1)) (v "x"))) 0)

private theorem sum_pos (f : Nat → Nat) (n : Nat) :
    sumF f n ≠ 0 ↔ ∃ i, i < n ∧ f i ≠ 0 := by
  induction n with
  | zero => simp [sumF, overRange]
  | succ n ih =>
    change sumF f n + f n ≠ 0 ↔ _
    constructor
    · intro h
      by_cases z : f n = 0
      · obtain ⟨i,hi,hf⟩ := ih.mp (by omega)
        exact ⟨i, by omega, hf⟩
      · exact ⟨n, by omega, z⟩
    · rintro ⟨i, hi, hf⟩
      by_cases e : i = n
      · subst i; omega
      · have := ih.mpr ⟨i, by omega, hf⟩; omega

def count (x : Nat) := value powerCount (fun _ => x)

theorem count_ok (x : Nat) : count x ≠ 0 ↔ HasPower x := by
  unfold count powerCount
  rw [value_program]
  simp only [denSum, plus, iteEval, oneArg, eqE, power]
  change sumF (fun p => if pBit p = 0 then 0 else sumF (fun j =>
    if p^(j+1) = x then 1 else 0) x) (x+1) ≠ 0 ↔ _
  rw [sum_pos]; unfold HasPower
  apply exists_congr; intro p
  apply and_congr_right; intro _
  by_cases h : pBit p = 0
  · simp [h]
  · simp only [h, if_false, ne_eq, not_false_eq_true, true_and, sum_pos]
    apply exists_congr; intro j
    apply and_congr_right; intro _
    split <;> simp_all

private theorem log_mono {x y : Nat} (h : x ≤ y) : x.log2 ≤ y.log2 := by
  by_cases hx : x = 0
  · simp [hx]
  · have hy : y ≠ 0 := by omega
    exact (Nat.le_log2 hy).mpr ((Nat.log2_self_le hx).trans h)

private theorem log_static (x : Nat) (hx : 0 < x) (hn : ¬ HasPower (x+1)) :
    (x+1).log2 = x.log2 := by
  apply Nat.le_antisymm _ (log_mono (by omega))
  apply (Nat.le_log2 (by omega : x ≠ 0)).mpr
  have hp := Nat.log2_self_le (by omega : x+1 ≠ 0)
  by_cases hh : 2^(x+1).log2 ≤ x
  · exact hh
  · have he : 2^(x+1).log2 = x+1 := by omega
    have hpos : (x+1).log2 ≠ 0 := by intro h; rw [h] at he; simp at he; omega
    have hj := Nat.log2_le_self (x+1)
    exact False.elim (hn ⟨2,by omega,two_ok,(x+1).log2-1,by omega,
      by rwa [Nat.sub_add_cancel (by omega : 1 ≤ (x+1).log2)]⟩)

private theorem prod_congr (n : Nat) (f g : Nat → Nat) (h : ∀ i, i < n → f i = g i) :
    prod f n = prod g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change prod f n * f n = prod g n * g n
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

private theorem product_static (D : Data) (x : Nat) (hx : 0 < x) (hn : ¬ HasPower (x+1)) :
    prodVal D (x+1) = prodVal D x := by
  have hnew : pBit (x+1) = 0 := by
    by_cases hz : pBit (x+1) = 0
    · exact hz
    · exact False.elim (hn ⟨x+1,by omega,hz,0,by omega,by simp⟩)
  change prod (row D (x+1)) (x+1) * row D (x+1) (x+1) = _
  rw [show row D (x+1) (x+1) = 1 by simp [row,hnew], Nat.mul_one]
  apply prod_congr; intro p hp
  unfold row
  by_cases hz : pBit p = 0
  · simp [hz]
  · simp only [hz, if_false, log_static x hx hn]
    apply prod_congr; intro j hj
    have hj' := Nat.log2_le_self x
    have hne : p^(j+1) ≠ x+1 := fun hh => hn ⟨p,by omega,hz,j,by omega,hh⟩
    have hiff : p^(j+1) ≤ x+1 ↔ p^(j+1) ≤ x := by omega
    simp [factor,hiff]

theorem static (D : Data) (x : Nat) (hx : 0 < x) (hn : ¬ HasPower (x+1)) :
    D.logP (x+1) = D.logP x := by rw [log_ok,log_ok,product_static D x hx hn]


private theorem bitsSmall (n : Nat) (f : Nat → Nat) : prod (fun i => bit (f i)) n ≤ 1 := by
  induction n with
  | zero => exact Nat.le_refl 1
  | succ n ih =>
    change prod (fun i => bit (f i)) n * bit (f n) ≤ 1
    by_cases h : f n = 0
    · rw [show bit (f n) = 0 by simp [bit,h], Nat.mul_zero]; decide
    · rw [show bit (f n) = 1 by simp [bit,h], Nat.mul_one]; exact ih

private theorem denAll {ctx} (j : String) (b : E ctx) (f : E (j::ctx)) (e) :
    denote (allTo j b f) e = prod (fun i => bit (denote f (Fin.cases i e))) (denote b e) := rfl

private theorem codePrime_iff (p : Nat) : pBit p ≠ 0 ↔
    2 ≤ p ∧ ∀ d, 2 ≤ d → d < p → p % d ≠ 0 := by
  have bound : pBit p ≤ 1 := by
    unfold pBit primeCode
    rw [value_program]; simp only [times, leE, denAll]
    change (if 2 ≤ p then 1 else 0) * prod (fun i => bit _) _ ≤ 1
    by_cases h : 2 ≤ p <;> simp only [h, if_true, if_false, Nat.one_mul, Nat.zero_mul]
    · exact bitsSmall _ _
    · decide
  have h : pBit p ≠ 0 ↔ pBit p = 1 := by omega
  exact h.trans (value_primeCode (fun _ => p))

/-- The event predicate has the elementary trial-divisor definition of primality. -/
theorem power_reading (x : Nat) : count x ≠ 0 ↔ ∃ p, p < x+1 ∧
    (2 ≤ p ∧ ∀ d, 2 ≤ d → d < p → p % d ≠ 0) ∧ ∃ j, j < x ∧ p^(j+1) = x := by
  simp only [count_ok, HasPower, codePrime_iff]

private theorem cost_mono (D : Data) {x y : Nat} (h : x ≤ y) : D.cost x ≤ D.cost y := by
  unfold Data.cost allowance
  simp only [value_program,times,power,plus,oneArg,value_logCode]
  change x * (_ * (1+(2*x).log2)^2)^2 ≤ y * (_ * (1+(2*y).log2)^2)^2
  apply Nat.mul_le_mul h
  apply Nat.pow_le_pow_left
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_left (log_mono (Nat.mul_le_mul_left 2 h)) 1

def mass (t : Nat) : Nat :=
  let n := t+100
  if t = 0 then 1 else count n + count (2*n-1) + count (2*n)

private theorem gap_static (D : Data) (t : Nat) (hz : mass (t+1) = 0) :
    D.energy (t+1) = D.energy t := by
  let n := t+100
  have h0 : count (n+1) + count (2*(n+1)-1) + count (2*(n+1)) = 0 := by
    simpa only [mass, n, Nat.succ_add, Nat.succ_ne_zero, if_false] using hz
  have h1 : ¬ HasPower (n+1) := fun h => (count_ok _).mpr h (by omega)
  have h2 : ¬ HasPower (2*n+1) := by
    intro h
    have hh := (count_ok _).mpr h
    have he : 2*n+1 = 2*(n+1)-1 := by omega
    rw [he] at hh; omega
  have h3 : ¬ HasPower (2*n+1+1) := by
    intro h
    have hh := (count_ok _).mpr h
    have he : 2*n+1+1 = 2*(n+1) := by omega
    rw [he] at hh; omega
  have hn : 0 < n := by dsimp [n]; omega
  have a := static D n hn h1
  have b₁ := static D (2*n) (by omega) h2
  have b₂ := static D (2*n+1) (by omega) h3
  unfold Data.energy Data.gap
  rw [show t+1+100 = n+1 by rfl, show 2*(n+1) = 2*n+1+1 by omega,a,b₂,b₁]

/-- Constructive localization for arbitrary sample schedules with decidable event count. -/
theorem localize (E C M : Nat → Nat) (base : M 0 ≠ 0)
    (stay : ∀ t, M (t+1) = 0 → E (t+1) = E t)
    (grow : ∀ t, C t ≤ C (t+1)) :
    (∀ i, E i ≤ C i) ↔ ∀ i, M i ≠ 0 → E i ≤ C i := by
  constructor
  · exact fun h i _ => h i
  · intro h i
    induction i with
    | zero => exact h 0 base
    | succ i ih =>
      by_cases z : M (i+1) = 0
      · rw [stay i z]; exact ih.trans (grow i)
      · exact h (i+1) z

theorem events_iff (D : Data) :
    (∀ i, D.test i) ↔ ∀ i, mass i ≠ 0 → D.test i := by
  have grow (t : Nat) : D.budget t ≤ D.budget (t+1) :=
    cost_mono D (show t+100 ≤ t+1+100 by omega)
  have base : mass 0 ≠ 0 := by
    rw [mass, if_pos rfl]
    decide
  exact localize D.energy D.budget mass base (gap_static D) grow

/-- Count scheduled tests. Every branch uses one fixed primitive-recursive program. -/
def eventCode : PR 1 := program ["t"] <|
  let n := v "t"+100
  iteE (eqB (v "t") 0) 1 (call powerCount [n] + call powerCount [2*n-1] + call powerCount [2*n])

def eventMatrix : PR 5 := program ["d","H","u","v","t"] <|
  iteE (call eventCode [v "t"]) (call excess [v "d",v "H",v "u",v "v",v "t"]) 0

private theorem event_ok (t : Nat) : value eventCode (fun _ => t) = mass t := by
  unfold eventCode; rw [value_program]; simp only [iteEval, plus, eqE, oneArg, times, minus]
  change (if (if t = 0 then (1:Nat) else 0) = 0 then _ else 1) = _
  unfold mass
  by_cases h : t = 0
  · simp only [h, if_true, Nat.one_ne_zero, if_false]
  · simp only [h, if_false, if_true]
    rfl

private theorem eventMatrix_ok (p : Data) (t : Nat) :
    value eventMatrix (p.args t) = 0 ↔ (mass t ≠ 0 → p.test t) := by
  unfold eventMatrix; rw [value_program]; simp only [iteEval,oneArg,apply5,event_ok]
  change (if mass t = 0 then 0 else value excess (p.args t)) = 0 ↔ _
  by_cases h : mass t = 0
  · simp [h]
  · simp only [h, if_false, ne_eq, not_false_eq_true, true_implies]
    exact read_test p t

/-- The thinned RH, GRH and ERH sentences have exactly the original standard interpretations. -/
theorem sparse_sentence_iff (s : Family) :
    naturalTerms.Holds (s.close excess) Fin.elim0 ↔ naturalTerms.Holds (s.close eventMatrix) Fin.elim0 := by
  apply (hypothesis_iff s .localTest).trans
  apply Iff.trans _ (s.holds_matrix eventMatrix).symm
  exact s.lift_iff (fun p => (events_iff p).trans (forall_congr' (fun t => (eventMatrix_ok p t).symm)))

end RiemannIPRA.Sparse
