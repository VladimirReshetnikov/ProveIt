import Mertens
namespace Mertens

def IsPrime (p : Nat) : Prop := 1 < p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem strip_coprime_prime {p d n : Nat} (hp : IsPrime p) (hpd : ¬ p ∣ d) :
    (d ∣ p*n) ↔ d ∣ n := by
  have hg : Nat.gcd d p = 1 := by
    rcases hp.2 _ (Nat.gcd_dvd_right d p) with h | h
    · exact h
    · have hd := Nat.gcd_dvd_left d p
      rw [h] at hd
      exact False.elim (hpd hd)
  rw [← Nat.dvd_gcd_mul_iff_dvd_mul, hg, Nat.one_mul]

theorem divsum_prime_split (f : Nat → Int) {p n : Nat} (hp : IsPrime p) (hn : 0 < n) :
    divsum f (p*n) (p*n) = divsum (fun d => f (p*d)) n n +
      divsum (fun d => if p ∣ d then 0 else f d) n n := by
  let A := fun i => if p ∣ i then (if i/p ∣ n then f (p*(i/p)) else 0) else 0
  let B := fun i => if i ∣ n then (if p ∣ i then 0 else f i) else 0
  have hpos : 0 < p := by have hh := hp.1; omega
  have splitAt (i : Nat) : (if i ∣ p*n then f i else 0) = A i + B i := by
    dsimp [A, B]
    by_cases hi : p ∣ i
    · have he : p*(i/p) = i := Nat.mul_div_cancel' hi
      have hdiv : i ∣ p*n ↔ i/p ∣ n := by
        constructor
        · intro hd
          apply Nat.dvd_of_mul_dvd_mul_left hpos
          rwa [he]
        · intro hd
          rw [← he]
          exact Nat.mul_dvd_mul_left _ hd
      simp only [hi, if_pos, he, hdiv, ite_self, Int.add_zero]
    · simp only [hi, ↓reduceIte, Int.zero_add, strip_coprime_prime hp hi]
  have hA : sum A (p*n) = divsum (fun d => f (p*d)) n n := by
    have e := multiple_subsum (fun d => if d ∣ n then f (p*d) else 0) p (p*n)
    simp only [Nat.mul_div_cancel_left n hpos] at e
    exact e
  have hB : sum B (p*n) = divsum (fun d => if p ∣ d then 0 else f d) n n := by
    apply divsum_pad _ hn
    have hh := Nat.mul_le_mul_right n (show 1 ≤ p by omega)
    simpa only [Nat.one_mul] using hh
  calc
    _ = sum (fun i => A i + B i) (p*n) := sum_congr (fun i _ _ => splitAt i)
    _ = _ := by rw [sum_add, hA, hB]

theorem zero_from_divsum (f : Nat → Int) (hf : ∀ n, 0 < n → divsum f n n = 0)
    {x : Nat} (hx : 0 < x) : f x = 0 := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    cases x with
    | zero => omega
    | succ n =>
      have h := hf (n+1) hx
      have hprev : divsum f (n+1) n = 0 := by
        rw [← sum_zero n]
        apply sum_congr
        intro d hd hdn
        simp [ih d (by omega) hd]
      change divsum f (n+1) n + (if n+1 ∣ n+1 then f (n+1) else 0) = 0 at h
      simpa only [hprev, Nat.dvd_refl, if_pos, Int.zero_add] using h

theorem mu_prime_step {p n : Nat} (hp : IsPrime p) (hn : 0 < n) :
    mu (p*n) = if p ∣ n then 0 else -mu n := by
  let f := fun d => mu (p*d) + (if p ∣ d then 0 else mu d)
  have hf (m : Nat) (hm : 0 < m) : divsum f m m = 0 := by
    have hh := divsum_prime_split mu hp hm
    have hgt : p*m ≠ 1 := by
      have hh := Nat.mul_le_mul_left p hm
      have hp' := hp.1
      rw [Nat.mul_one] at hh
      omega
    rw [mu_divsum, delta, if_neg hgt] at hh
    conv => rhs; rw [hh]
    unfold divsum
    rw [← sum_add]
    apply sum_congr
    intro d _ _
    by_cases hdm : d ∣ m <;> simp [hdm, f]
  have hzero := zero_from_divsum f hf hn
  change mu (p*n) + (if p ∣ n then 0 else mu n) = 0 at hzero
  by_cases hpn : p ∣ n <;> simp only [hpn, ↓reduceIte] at * <;> omega

/-- Bounded search for the least divisor greater than 1, starting with
n as a known candidate. This is used only when n ≥ 2. -/
def leastUpTo (n : Nat) : Nat → Nat
  | 0 => n
  | k+1 =>
    let d := leastUpTo n k
    if 1 < k+1 ∧ k+1 ∣ n ∧ k+1 < d then k+1 else d

theorem leastUpTo_spec {n : Nat} (hn : 1 < n) (k : Nat) :
    1 < leastUpTo n k ∧ leastUpTo n k ∣ n ∧
    ∀ t, 1 < t → t ≤ k → t ∣ n → leastUpTo n k ≤ t := by
  induction k with
  | zero => exact ⟨hn, Nat.dvd_refl _, fun t h₁ h₂ _ => by omega⟩
  | succ k ih =>
    rw [leastUpTo]
    split
    · rename_i h
      refine ⟨h.1, h.2.1, ?_⟩
      intro t ht htk htn
      by_cases h' : t ≤ k
      · have hmin := ih.2.2 t ht h' htn
        omega
      · omega
    · rename_i h
      refine ⟨ih.1, ih.2.1, ?_⟩
      intro t ht htk htn
      by_cases h' : t ≤ k
      · exact ih.2.2 t ht h' htn
      · have he : t = k+1 := by omega
        subst t
        exact Nat.le_of_not_gt (fun hlt => h ⟨ht, htn, hlt⟩)

theorem least_prime_factor {n : Nat} (hn : 1 < n) :
    IsPrime (leastUpTo n n) ∧ leastUpTo n n ∣ n := by
  let p := leastUpTo n n
  have hs := leastUpTo_spec hn n
  have hp : 1 < p := hs.1
  have hpn : p ∣ n := hs.2.1
  refine ⟨⟨hp, ?_⟩, hpn⟩
  intro d hd
  have hdpos := Nat.pos_of_dvd_of_pos hd (show 0 < p by omega)
  by_cases h1 : d = 1
  · exact Or.inl h1
  · right
    have hdp := Nat.le_of_dvd (show 0 < p by omega) hd
    have hdn := Nat.dvd_trans hd hpn
    exact Nat.le_antisymm hdp
      (hs.2.2 d (by omega) (Nat.le_of_dvd (by omega) hdn) hdn)

theorem mu_range (x : Nat) : -1 ≤ mu x ∧ mu x ≤ 1 := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases hx : 1 < x
    · let p := leastUpTo x x
      have hp := (least_prime_factor hx).1
      obtain ⟨t, he⟩ := (least_prime_factor hx).2
      change x = p*t at he
      have ht : 0 < t := by
        cases t with
        | zero => simp at he; omega
        | succ t => omega
      have hlt : t < x := by
        have hm := Nat.mul_lt_mul_of_pos_right hp.1 ht
        rw [Nat.one_mul] at hm
        exact he.symm ▸ hm
      have hb := ih t hlt
      have hstep := mu_prime_step hp ht
      change mu (p*t) = _ at hstep
      rw [he, hstep]
      split <;> constructor <;> omega
    · have hsmall : x = 0 ∨ x = 1 := by omega
      rcases hsmall with h | h <;> subst x <;> decide

/-- The same bound for increments and decrements over every finite interval. -/
theorem M_interval (n h : Nat) : -(h : Int) ≤ M (n+h) - M n ∧
    M (n+h) - M n ≤ (h : Int) := by
  induction h with
  | zero => simp
  | succ h ih =>
    change -((h : Int)+1) ≤ M ((n+h)+1) - M n ∧ M ((n+h)+1) - M n ≤ (h : Int)+1
    rw [M_step]
    have hb := mu_range (n+h+1)
    constructor <;> omega

theorem M_bound (n : Nat) : -(n : Int) ≤ M n ∧ M n ≤ (n : Int) := by
  simpa [M_zero] using M_interval 0 n

theorem M_bound_after_two (h : Nat) : -(h : Int) ≤ M (2+h) ∧ M (2+h) ≤ (h : Int) := by
  have h2 : M 2 = 0 := rfl
  simpa [h2] using M_interval 2 h

def product : List Nat → Nat
  | [] => 1
  | p :: ps => p * product ps

def primeList : Nat → Nat → List Nat
  | 0, _ => []
  | fuel+1, n =>
    if n ≤ 1 then [] else
      let p := leastUpTo n n
      p :: primeList fuel (n/p)

theorem least_quotient {n : Nat} (hn : 1 < n) :
    let p := leastUpTo n n
    0 < n/p ∧ n/p < n ∧ p*(n/p) = n := by
  let p := leastUpTo n n
  obtain ⟨hp, hd⟩ := least_prime_factor hn
  have he : p*(n/p) = n := Nat.mul_div_cancel' hd
  change 0 < n/p ∧ n/p < n ∧ p*(n/p) = n
  exact ⟨Nat.pos_of_ne_zero (fun h => by rw [h, Nat.mul_zero] at he; omega),
    Nat.div_lt_self (by omega) hp.1, he⟩

theorem factorization {k n : Nat} (hn : 0 < n) (hk : n ≤ k) :
    product (primeList k n) = n ∧ ∀ q, q ∈ primeList k n → IsPrime q := by
  induction k generalizing n with
  | zero => exact False.elim (by omega)
  | succ k ih =>
    rw [primeList]
    split
    · rename_i h
      have he : n = 1 := by omega
      subst n
      exact ⟨rfl, fun _ hq => nomatch hq⟩
    · rename_i h
      have hn' : 1 < n := by omega
      let p := leastUpTo n n
      have hq := least_quotient hn'
      change 0 < n/p ∧ n/p < n ∧ p*(n/p) = n at hq
      have hrec := ih hq.1 (show n/p ≤ k by omega)
      constructor
      · change p * product (primeList k (n/p)) = n
        rw [hrec.1]
        exact hq.2.2
      · intro q hmem
        rcases List.mem_cons.mp hmem with he | htail
        · subst q; exact (least_prime_factor hn').1
        · exact hrec.2 q htail

theorem mem_prime_list {p : Nat} (hp : IsPrime p) (xs : List Nat)
    (hs : ∀ q, q ∈ xs → IsPrime q) : p ∈ xs ↔ p ∣ product xs := by
  induction xs with
  | nil =>
    have hne : p ≠ 1 := by have hh := hp.1; omega
    simp [product, hne, Nat.dvd_one]
  | cons q qs ih =>
    have hq := hs q List.mem_cons_self
    have hqs : ∀ a, a ∈ qs → IsPrime a := fun a h => hs a (List.mem_cons_of_mem q h)
    by_cases h : p = q
    · subst p
      exact ⟨fun _ => Nat.dvd_mul_right _ _, fun _ => List.mem_cons_self⟩
    · have hqp : ¬ q ∣ p := by
        intro hd
        rcases hp.2 q hd with he | he
        · have hh := hq.1; omega
        · exact h he.symm
      simp only [List.mem_cons, h, false_or, product, strip_coprime_prime hq hqp, ih hqs]

def signedFactors (xs : List Nat) : Int :=
  if xs.Nodup then (-1 : Int)^xs.length else 0

theorem signed_cons (p : Nat) (xs : List Nat) :
    signedFactors (p :: xs) = if p ∈ xs then 0 else -signedFactors xs := by
  by_cases h : p ∈ xs <;> by_cases u : xs.Nodup <;>
    simp [signedFactors, List.nodup_cons, h, u, Int.pow_succ]

/-- Conventional Möbius function: repeated prime factors give zero,
otherwise take the parity sign of the number of prime factors. -/
def factorMu (n : Nat) : Int :=
  if n = 0 then 0 else signedFactors (primeList n n)

theorem signed_factorization {k n : Nat} (hn : 0 < n) (hk : n ≤ k) :
    signedFactors (primeList k n) = mu n := by
  induction k generalizing n with
  | zero => exact False.elim (by omega)
  | succ k ih =>
    rw [primeList]
    split
    · rename_i h
      have he : n = 1 := by omega
      subst n; rfl
    · rename_i h
      have hn' : 1 < n := by omega
      let p := leastUpTo n n
      have hp : IsPrime p := (least_prime_factor hn').1
      have hq := least_quotient hn'
      change 0 < n/p ∧ n/p < n ∧ p*(n/p) = n at hq
      have hbound : n/p ≤ k := by omega
      have rest := factorization hq.1 hbound
      have hm := mem_prime_list hp _ rest.2
      rw [rest.1] at hm
      change signedFactors (p :: primeList k (n/p)) = mu n
      rw [signed_cons, ih hq.1 hbound]
      have hstep := mu_prime_step hp hq.1
      rw [hq.2.2] at hstep
      simpa only [hm] using hstep.symm

theorem factorMu_correct (n : Nat) : factorMu n = mu n := by
  cases n with
  | zero => rfl
  | succ n => simpa [factorMu] using signed_factorization (Nat.succ_pos n) (Nat.le_refl _)

end Mertens
