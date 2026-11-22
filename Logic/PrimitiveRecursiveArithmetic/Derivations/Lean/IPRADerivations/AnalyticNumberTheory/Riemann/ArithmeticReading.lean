import IPRADerivations.AnalyticNumberTheory.Riemann.CompilerSemantics

/-! Imported from the packet `analytic-number-theory/riemann_hypotheses_ipra_2026-11-20`,
`ArithmeticReading.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PacketLanguage

variable {ctx : List String}
private theorem ev_add (a b : E ctx) (e) :
    denote (a+b) e = denote a e + denote b e := by
  change value addR _ = _
  rw [value_addR]
  rfl
private theorem ev_mul (a b : E ctx) (e) :
    denote (a*b) e = denote a e * denote b e := by
  change value mulR _ = _
  rw [value_mulR]
  rfl
private theorem ev_sub (a b : E ctx) (e) :
    denote (a-b) e = denote a e - denote b e := by
  change value subR _ = _
  rw [value_subR]
  rfl
private theorem ev_le (a b : E ctx) (e) :
    denote (leB a b) e = (if denote a e ≤ denote b e then 1 else 0) := by
  change value isZeroR _ = _
  rw [value_isZeroR]
  change (if denote (a-b) e = 0 then 1 else 0) = _
  simp [ev_sub, Nat.sub_eq_zero_iff_le]
private theorem ev_clip (a : E ctx) (e) :
    denote (call clipR [a]) e = bit (denote a e) := by
  apply value_clipR
private theorem ev_zero (a : E ctx) (e) :
    denote (call isZeroR [a]) e = (if denote a e = 0 then 1 else 0) := by
  apply value_isZeroR
private theorem ev_ite (t a b : E ctx) (e) :
    denote (iteE t a b) e = (if denote t e = 0 then denote b e else denote a e) := by
  simp only [iteE, ev_add, ev_mul, ev_clip, ev_zero, bit]
  split <;> simp
private theorem ev_maxTo (name : String) (k : E ctx) (s : E (name::ctx)) (e) :
    denote (maxTo name k s) e =
      overRange 0 (fun i a => max a (denote s (Fin.cases i e))) (denote k e) := rfl

/-- Exclusive scan of the integers satisfying a monotone upper threshold. -/
private theorem maximum_prefix (h n : Nat) :
    overRange 0 (fun i a => max a (if i ≤ h then i else 0)) (n+1) = min n h := by
  induction n with
  | zero => simp [overRange]
  | succ n ih =>
    change max (overRange 0 (fun i a => max a (if i ≤ h then i else 0)) (n+1)) (if n+1 ≤ h then n+1 else 0) = _
    rw [ih]
    split <;> omega

private def quotScan (a b n : Nat) : Nat :=
  overRange 0 (fun i acc => max acc (if i*b ≤ a then i else 0)) n

private theorem quotScan_succ (a b n : Nat) (hb : 0 < b) :
    quotScan a b (n+1) = min n (a/b) := by
  simpa only [quotScan, ← Nat.le_div_iff_mul_le hb] using maximum_prefix (a / b) n


private theorem quotScan_eq (a b : Nat) (hb : 0 < b) : quotScan a b (a+1) = a/b := by
  rw [quotScan_succ a b a hb, Nat.min_eq_right (Nat.div_le_self a b)]

theorem value_quotientR (e : Fin 2 → Nat) : value quotientR e = e 0 / e 1 := by
  unfold quotientR
  rw [value_program]
  simp only [ev_ite, ev_maxTo, ev_add, ev_mul, ev_le]
  change (if e 1 = 0 then 0 else overRange 0 (fun i acc =>
    max acc (i * (if i*(e 1) ≤ e 0 then 1 else 0))) (e 0+1)) = _
  have hf : (fun i acc : Nat => max acc (i * (if i*(e 1) ≤ e 0 then 1 else 0))) =
      (fun i acc => max acc (if i*(e 1) ≤ e 0 then i else 0)) := by
    funext i acc; split <;> simp
  rw [hf]
  split
  · rename_i h; simp [h]
  · rename_i h; exact quotScan_eq _ _ (Nat.pos_of_ne_zero h)

theorem denote_divE (a b : E ctx) (e) :
    denote (divE a b) e = denote a e / denote b e := by
  change value quotientR _ = _
  rw [value_quotientR]
  rfl

theorem denote_modE (a b : E ctx) (e) :
    denote (modE a b) e = denote a e % denote b e := by
  simp only [modE, ev_sub, ev_mul, denote_divE]
  rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm (denote b e)]


private theorem ev_pow (a b : E ctx) (e) :
    denote (powE a b) e = denote a e ^ denote b e := by
  change value powR _ = _
  rw [value_powR]
  rfl

/-- The compiled binary-logarithm symbol computes Lean's floor logarithm. -/
theorem value_logCode (e : Fin 1 → Nat) : value logCode e = (e 0).log2 := by
  unfold logCode
  rw [value_program]
  simp only [ev_maxTo, ev_add, ev_mul, ev_le, ev_pow]
  change overRange 0 (fun i a => max a (i * if 2 ^ i ≤ e 0 then 1 else 0)) (e 0+1) = _
  by_cases h : e 0 = 0
  · rw [h]; rfl
  · have he : (fun i a : Nat => max a (i * if 2 ^ i ≤ e 0 then 1 else 0)) =
        (fun i a => max a (if i ≤ (e 0).log2 then i else 0)) := by
      funext i a
      simp only [← Nat.le_log2 h]
      split <;> simp
    rw [he, maximum_prefix, Nat.min_eq_right (Nat.log2_le_self _)]

private theorem ev_eq (a b : E ctx) (e) :
    denote (eqB a b) e = (if denote a e = denote b e then 1 else 0) := by
  simp only [eqB, ev_mul, ev_le]
  split <;> split <;> split <;> first | rfl | omega

private theorem mul_one (a b : Nat) : a*b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    exact ⟨Nat.eq_one_of_mul_eq_one_right h, Nat.eq_one_of_mul_eq_one_left h⟩
  · rintro ⟨rfl, rfl⟩; rfl

private theorem ev_all (name : String) (b : E ctx) (s : E (name::ctx)) (e) :
    denote (allTo name b s) e = 1 ↔
      ∀ j, j < denote b e → denote s (Fin.cases j e) ≠ 0 := by
  change overRange 1 (fun j a => a * bit (denote s (Fin.cases j e))) (denote b e) = 1 ↔ _
  generalize denote b e = n
  induction n with
  | zero => simp [overRange]
  | succ n ih =>
    change (overRange 1 (fun j a => a * bit (denote s (Fin.cases j e))) n) *
      bit (denote s (Fin.cases n e)) = 1 ↔ _
    rw [mul_one, ih]
    have hbit : ∀ a : Nat, bit a = 1 ↔ a ≠ 0 := by
      intro a; cases a <;> simp [bit]
    rw [hbit]
    constructor
    · rintro ⟨h, hn⟩ j hj
      by_cases jj : j = n
      · simpa [jj] using hn
      · exact h j (by omega)
    · intro h
      exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

/-- Trial division in the compiled symbol accepts precisely the primes,
    expressed by the exclusion of all proper integer divisors ≥2. -/
theorem value_primeCode (e : Fin 1 → Nat) : value primeCode e = 1 ↔
    2 ≤ e 0 ∧ ∀ d, 2 ≤ d → d < e 0 → e 0 % d ≠ 0 := by
  unfold primeCode
  rw [value_program]
  simp only [ev_mul, mul_one, ev_le, ev_all, ev_sub, ev_eq, denote_modE, ev_add]
  change ((if 2 ≤ e 0 then 1 else 0) = 1 ∧ ∀ j, j < e 0 - 2 →
    (if (if e 0 % (j + 2) = 0 then 1 else 0) = 0 then 1 else 0) ≠ 0) ↔ _
  have f (a : Nat) :
      (if (if a = 0 then 1 else 0) = 0 then 1 else 0) ≠ 0 ↔ a ≠ 0 := by
    cases a <;> simp
  simp only [f]
  by_cases h : 2 ≤ e 0
  · simp only [h, if_true, true_and]
    constructor
    · intro hs d hd hdp
      have hd' : d - 2 + 2 = d := by omega
      simpa only [hd'] using hs (d-2) (by omega)
    · intro hs j hj
      exact hs (j+2) (by omega) (by omega)
  · simp [h]

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PacketLanguage
