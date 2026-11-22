import Std

/-!
# Finite arithmetic for quadratic reciprocity

All computations use natural numbers and bounded primitive recursion.
The Legendre bit is used on units; on those inputs, 0 = residue, 1 = nonresidue.
-/
namespace QR

def half (p : Nat) : Nat := (p-1)/2

def sum1 (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sum1 f n + f (n+1)

def anyBelow (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n+1 => anyBelow f n || f n

theorem anyBelow_spec (f : Nat → Bool) (n : Nat) :
    anyBelow f n = true ↔ ∃ i, i < n ∧ f i = true := by
  induction n with
  | zero => simp [anyBelow]
  | succ n ih =>
    simp only [anyBelow, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, hf⟩ | hf)
      · exact ⟨i, by omega, hf⟩
      · exact ⟨n, by omega, hf⟩
    · rintro ⟨i, hi, hf⟩
      by_cases h : i = n
      · exact Or.inr (h ▸ hf)
      · exact Or.inl ⟨i, by omega, hf⟩

def primeB (p : Nat) : Bool :=
  decide (1 < p) && !(anyBelow (fun d => decide (2 ≤ d ∧ p % d = 0)) p)

theorem primeB_spec {p : Nat} :
    primeB p = true ↔ 1 < p ∧ ∀ d, d < p → 2 ≤ d → p % d ≠ 0 := by
  simp [primeB, ← Bool.not_eq_true, anyBelow_spec]

theorem prime_divisor {p d : Nat} (hp : primeB p = true) (hd : d ∣ p) :
    d = 1 ∨ d = p := by
  obtain ⟨hp1, hx⟩ := primeB_spec.mp hp
  have hdle := Nat.le_of_dvd (by omega : 0 < p) hd
  have hn : d ≠ 0 := by
    rintro rfl
    have hz : p = 0 := by simpa using hd
    omega
  by_cases h : d = p
  · exact .inr h
  · left
    by_cases h2 : 2 ≤ d
    · exact False.elim (hx d (by omega) h2 (Nat.mod_eq_zero_of_dvd hd))
    · omega

def squareB (p a : Nat) : Bool :=
  anyBelow (fun x => decide ((x*x) % p = a % p)) p

theorem squareB_spec {p a : Nat} :
    squareB p a = true ↔ ∃ x, x < p ∧ (x*x) % p = a % p := by
  simp [squareB, anyBelow_spec]

def nonresBit (p a : Nat) : Nat := if squareB p a then 0 else 1

def highCount (p a : Nat) : Nat :=
  sum1 (fun i => if half p < a*i%p then 1 else 0) (half p)

def foldRep (p r : Nat) : Nat := if half p < r then p-r else r

def floorSum (p a : Nat) : Nat := sum1 (fun i => a*i/p) (half p)

theorem sum1_congr {f g : Nat → Nat} (n : Nat)
    (h : ∀ i, 0 < i → i ≤ n → f i = g i) : sum1 f n = sum1 g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum1]
    rw [ih (by intro i hi hj; exact h i hi (by omega)), h _ (by omega) (by omega)]

theorem sum1_add (f g : Nat → Nat) (n : Nat) :
    sum1 (fun i => f i + g i) n = sum1 f n + sum1 g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum1, ih]; omega

theorem sum1_const (n k : Nat) : sum1 (fun _ => k) n = n*k := by
  induction n with
  | zero => simp [sum1]
  | succ n ih => simp [sum1, ih, Nat.succ_mul]

theorem sum1_transpose (f : Nat → Nat → Nat) (m n : Nat) :
    sum1 (fun i => sum1 (f i) n) m = sum1 (fun j => sum1 (fun i => f i j) m) n := by
  induction m with
  | zero => simp [sum1, sum1_const]
  | succ m ih => simp only [sum1, ih, sum1_add]

theorem sum1_threshold (n t : Nat) :
    sum1 (fun j => if j ≤ t then 1 else 0) n = min n t := by
  induction n with
  | zero => simp [sum1]
  | succ n ih =>
    simp only [sum1, ih]
    split <;> omega

private theorem quotient_bound {p q i : Nat} (hp : 0 < p) (hq : 0 < q)
    (hi : i ≤ half p) : q*i/p ≤ half q := by
  have h2i : 2*i < p := by unfold half at hi; omega
  have hq2 : q ≤ 2*(half q+1) := by unfold half; omega
  have hlt := Nat.mul_lt_mul_of_pos_left h2i hq
  rw [show q*(2*i) = 2*(q*i) by ac_rfl] at hlt
  have hle := Nat.mul_le_mul_right p hq2
  rw [Nat.mul_assoc] at hle
  by_cases h : half q+1 ≤ q*i/p
  · have hb := (Nat.le_div_iff_mul_le hp).mp h
    omega
  · omega

private theorem row_floor {p q i : Nat} (hp : 0 < p) (hq : 0 < q)
    (hi : i ≤ half p) :
    sum1 (fun j => if p*j ≤ q*i then 1 else 0) (half q) = q*i/p := by
  calc
    _ = sum1 (fun j => if j ≤ q*i/p then 1 else 0) (half q) := by
      apply sum1_congr
      intro j _ _
      simp only [Nat.le_div_iff_mul_le hp, Nat.mul_comm j p]
    _ = _ := by rw [sum1_threshold, Nat.min_eq_right (quotient_bound hp hq hi)]

private theorem no_tie {p q i j : Nat} (hp : primeB p = true) (hq : primeB q = true)
    (hpq : p ≠ q) (hi : 0 < i) (hib : i ≤ half p) : p*j ≠ q*i := by
  have hp1 := (primeB_spec.mp hp).1
  have hil : i < p := by unfold half at hib; omega
  have gpq : p.gcd q = 1 := by
    rcases prime_divisor hp (Nat.gcd_dvd_left p q) with h | h
    · exact h
    · have hd := Nat.gcd_dvd_right p q
      rw [h] at hd
      rcases prime_divisor hq hd with hh | hh <;> omega
  have gpi : p.gcd i = 1 := by
    rcases prime_divisor hp (Nat.gcd_dvd_left p i) with h | h
    · exact h
    · have hd := Nat.gcd_dvd_right p i
      rw [h] at hd
      exact False.elim (Nat.not_le_of_gt hil (Nat.le_of_dvd hi hd))
  intro he
  have hd : p ∣ q*i := he ▸ Nat.dvd_mul_right p j
  have hx := Nat.dvd_gcd (Nat.dvd_refl p) hd
  have hy := Nat.gcd_mul_dvd_mul_gcd p q i
  rw [gpq, gpi] at hy
  have hz := Nat.le_of_dvd (by decide : 0 < 1*1) (Nat.dvd_trans hx hy)
  omega

/-- Exact lattice identity for distinct primes. -/
theorem floor_sum_swap {p q : Nat} (hp : primeB p = true) (hq : primeB q = true)
    (hpq : p ≠ q) : floorSum p q + floorSum q p = half p * half q := by
  have hp0 : 0 < p := Nat.lt_trans Nat.zero_lt_one (primeB_spec.mp hp).1
  have hq0 : 0 < q := Nat.lt_trans Nat.zero_lt_one (primeB_spec.mp hq).1
  let low := fun i j => if p*j ≤ q*i then 1 else 0
  let up := fun i j => if q*i ≤ p*j then 1 else 0
  have hl : floorSum p q = sum1 (fun i => sum1 (low i) (half q)) (half p) := by
    apply sum1_congr
    intro i _ hib
    exact (row_floor hp0 hq0 hib).symm
  have hu : floorSum q p = sum1 (fun i => sum1 (up i) (half q)) (half p) := by
    rw [sum1_transpose up]
    apply sum1_congr
    intro j _ hjb
    exact (row_floor hq0 hp0 hjb).symm
  rw [hl, hu, ← sum1_add]
  calc
    _ = sum1 (fun _ => half q) (half p) := by
      apply sum1_congr
      intro i hi hib
      rw [← sum1_add]
      calc
        _ = sum1 (fun _ => 1) (half q) := by
          apply sum1_congr
          intro j _ _
          have hx := no_tie (j := j) hp hq hpq hi hib
          dsimp [low, up]
          split <;> split <;> omega
        _ = _ := by simp [sum1_const]
    _ = _ := sum1_const _ _

/-- Gauss's counting criterion, expressed entirely in natural-number bits. -/
def GaussLaw (p a : Nat) : Prop := nonresBit p a = highCount p a % 2

theorem gcd_one_of_unit {p a : Nat} (hp : primeB p = true) (ha : a%p ≠ 0) :
    p.gcd a = 1 := by
  rcases prime_divisor hp (Nat.gcd_dvd_left p a) with h | h
  · exact h
  · have hd := Nat.gcd_dvd_right p a
    rw [h] at hd
    exact False.elim (ha (Nat.mod_eq_zero_of_dvd hd))

theorem dvd_cancel_unit {p a x : Nat} (hp : primeB p = true) (ha : a%p ≠ 0)
    (hd : p ∣ a*x) : p ∣ x := by
  have h := (Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd)
  simpa [gcd_one_of_unit hp ha] using h

private theorem dvd_diff {p u v : Nat} (h : u%p = v%p) : p ∣ u-v := by
  have hu := Nat.mod_add_div u p
  have hv := Nat.mod_add_div v p
  rw [h] at hu
  rw [show u-v = p*(u/p)-p*(v/p) by omega]
  exact Nat.dvd_sub (Nat.dvd_mul_right _ _) (Nat.dvd_mul_right _ _)

theorem mul_injective_mod {p a i j : Nat} (hp : primeB p = true) (ha : a%p ≠ 0)
    (hi : i < p) (hj : j < p) (he : a*i%p = a*j%p) : i = j := by
  have left_bound : ∀ {x y : Nat}, x < p → a*x%p = a*y%p → x ≤ y := by
    intro x y hx he'
    have hdiff := dvd_diff he'
    rw [← Nat.mul_sub] at hdiff
    have hd := dvd_cancel_unit hp ha hdiff
    by_cases h : 0 < x-y
    · have hb := Nat.le_of_dvd h hd; omega
    · omega
  exact Nat.le_antisymm (left_bound hi he) (left_bound hj he.symm)

theorem mul_res_pos {p a i : Nat} (hp : primeB p = true) (ha : a%p ≠ 0)
    (hi : 0 < i) (hib : i < p) : 0 < a*i%p := by
  by_cases h : a*i%p=0
  · have hd := dvd_cancel_unit hp ha (Nat.dvd_of_mod_eq_zero h)
    have hh := Nat.le_of_dvd hi hd
    omega
  · omega

theorem fold_maps {p a i : Nat} (hp : primeB p = true) (hodd : p%2=1)
    (ha : a%p ≠ 0) (hi : 0<i) (hib : i ≤ half p) :
    0 < foldRep p (a*i%p) ∧ foldRep p (a*i%p) ≤ half p := by
  have hp1 := (primeB_spec.mp hp).1
  have hr := Nat.mod_lt (a*i) (by omega : p>0)
  have hrp := mul_res_pos hp ha hi (by unfold half at hib; omega)
  unfold half at *
  simp only [foldRep, half]
  split <;> constructor <;> omega

theorem fold_injective {p a i j : Nat} (hp : primeB p = true) (ha : a%p ≠ 0)
    (hi : 0<i) (hib : i≤half p) (hj : 0<j) (hjb : j≤half p)
    (hf : foldRep p (a*i%p) = foldRep p (a*j%p)) : i=j := by
  have hp1 := (primeB_spec.mp hp).1
  have hp0 : 0 < p := by omega
  have hil : i < p := by unfold half at hib; omega
  have hjl : j < p := by unfold half at hjb; omega
  have hir := Nat.mod_lt (a*i) hp0
  have hjr := Nat.mod_lt (a*j) hp0
  have hh : a*i%p = a*j%p ∨ a*i%p + a*j%p = p := by
    unfold foldRep at hf
    split at hf <;> split at hf <;> omega
  rcases hh with he | he
  · exact mul_injective_mod hp ha hil hjl he
  · have hz : a*(i+j)%p = 0 := by rw [Nat.mul_add, Nat.add_mod, he]; simp
    have hd := dvd_cancel_unit hp ha (Nat.dvd_of_mod_eq_zero hz)
    have hle := Nat.le_of_dvd (by omega : 0 < i+j) hd
    unfold half at *
    omega

end QR
