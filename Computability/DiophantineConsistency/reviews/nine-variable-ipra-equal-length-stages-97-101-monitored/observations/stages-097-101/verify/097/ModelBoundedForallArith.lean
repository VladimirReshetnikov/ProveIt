import DiophantineConsistency.ModelBetaFunction
import DiophantineConsistency.ModelRepFactorial
import DiophantineConsistency.NaturalExpressionSemiring

/-! # Internal arithmetic for the bounded-universal CRT certificate

Inside every model `V` of `𝗜𝚺₁`:

* `prodM T n = ∏_{i<n} ((i+1)·T+1)` (a primitive recursion), its divisibility
  and size facts, and `encProd_eq`: the explicit arithmetic encoding of
  `MRDP.encodedModuliProduct` (powers, factorial, binomial, remainder) computes
  `prodM` at positive scale;
* residues modulo the coprime moduli `(i+1)·T+1`: `mod_mul_of_bez`,
  `mod_prodM` (Chinese remainder in the uniqueness direction) and `crt_step`
  (one existence step), all through ring identities in `DiffRing V`;
* irreducible divisors without primes: `exists_irred_dvd` (least divisor
  `> 1`), `bez_of_irred`, `euclid_of_irred` (gcd certificates of
  `ArithmeticGcdNormalization`);
* falling factorials `m!·binom a m = a(a-1)…(a-m+1)` in the recursive form
  `desc_succ`, and the factor lemmas `dvd_factor_of_dvd_desc`, `dvd_desc_of_dvd`;
* natural expressions: monotonicity, congruence and `𝚺₁`-definability of
  `NatExpr.evalSemiring`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelBoundedForallArith
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticPow ArithmeticBinomPascal ArithmeticBinomFactorial
open ArithmeticGcdNormalization ModelBetaFunction

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The product of the moduli -/

namespace ProdM
def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out T. out = 1”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index T. out = previous * ((index + 1) * T + 1)”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 1
  succ parameters index previous := previous * ((index + 1) * parameters 0 + 1)
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]
end ProdM

/-- `prodM T n = ∏_{i<n} ((i+1)·T+1)`. -/
noncomputable def prodM (T n : V) : V := ProdM.construction.result ![T] n

/-- Public graph with argument order output/scale/length. -/
def prodMDef : 𝚺₁.Semisentence 3 := ProdM.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance prodM_defined : 𝚺₁-Function₂[V] prodM via prodMDef := .mk
  fun v ↦ by simp [ProdM.construction.result_defined_iff, prodMDef, prodM]; rfl
instance prodM_definable : 𝚺₁-Function₂[V] prodM := prodM_defined.to_definable

@[simp] theorem prodM_zero (T : V) : prodM T 0 = 1 := by simp [prodM, ProdM.construction]

theorem prodM_succ (T n : V) : prodM T (n + 1) = prodM T n * ((n + 1) * T + 1) := by
  simp [prodM, PR.Construction.result_succ, ProdM.construction]

theorem prodM_pos (T n : V) : 0 < prodM T n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [prodM_succ]
    exact mul_pos ih (beta_succ_pos _)

theorem dvd_prodM (T n : V) : ∀ k < n, (k + 1) * T + 1 ∣ prodM T n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro k hk
    exact absurd hk (not_lt.mpr (Arithmetic.zero_le k))
  case succ n ih =>
    intro k hk
    rw [prodM_succ]
    rcases lt_or_eq_of_le (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp hk) with hlt | heq
    · exact Dvd.dvd.mul_right (ih k hlt) _
    · rw [heq]
      exact dvd_mul_left _ _

theorem prodM_le (T N n : V) : n ≤ N → prodM T n ≤ power ((N + 1) * T + 1) n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _
    simp
  case succ n ih =>
    intro hn
    rw [prodM_succ, power_succ, mul_comm ((N + 1) * T + 1)]
    have hnN : n + 1 ≤ N + 1 := le_trans hn le_self_add
    exact mul_le_mul (ih (le_trans le_self_add hn))
      (_root_.add_le_add (mul_le_mul_of_nonneg_right hnN (Arithmetic.zero_le T)) le_rfl)
      (Arithmetic.zero_le _) (Arithmetic.zero_le _)

/-! ### Residues through the ring of differences -/

/-- Equal residues give a ring multiple of the modulus. -/
theorem ringSub_of_mod_eq {x y d : V} (h : x % d = y % d) :
    ∃ q : DiffRing V, ι x - ι y = ι d * q := by
  refine ⟨ι (x / d) - ι (y / d), ?_⟩
  have hx := congrArg (ι (V := V)) (div_add_mod x d)
  have hy := congrArg (ι (V := V)) (div_add_mod y d)
  simp only [map_add, map_mul] at hx hy
  rw [h] at hx
  linear_combination hy - hx

theorem mod_eq_of_ringDvd {a a' P d : V} {q : DiffRing V} (h : ι a' - ι a = ι P * q)
    (hd : d ∣ P) : a' % d = a % d := by
  obtain ⟨c, hc⟩ := hd
  exact mod_eq_of_sub_eq (q := ι c * q) (by rw [h, hc, map_mul]; ring)

theorem mod_eq_of_dvd_of_mod_eq {x y B p : V} (h : x % B = y % B) (hp : p ∣ B) :
    x % p = y % p := by
  obtain ⟨q, hq⟩ := ringSub_of_mod_eq h
  exact mod_eq_of_ringDvd hq hp

/-- Residues modulo two coprime moduli determine the residue modulo the product. -/
theorem mod_mul_of_bez {x y P M : V} (hP : x % P = y % P) (hM : x % M = y % M)
    (hb : Bez P M 1) : x % (P * M) = y % (P * M) := by
  obtain ⟨q1, h1⟩ := ringSub_of_mod_eq hP
  obtain ⟨q2, h2⟩ := ringSub_of_mod_eq hM
  obtain ⟨α, β, hab⟩ := (bez_one_iff_ring (a := P) (b := M)).mp hb
  refine mod_eq_of_sub_eq (q := α * q2 + β * q1) ?_
  rw [map_mul]
  linear_combination (-(ι x - ι y)) * hab + ι P * α * h2 + ι M * β * h1

/-- Truncated subtraction of equal residues is divisible by the modulus. -/
theorem dvd_tsub_of_mod_eq {a w M : V} (h : a % M = w % M) : M ∣ a - w := by
  rcases le_total w a with hwa | haw
  · obtain ⟨q, hq⟩ := ringSub_of_mod_eq h
    have hsum : ι (a - w) + ι w = ι a := by rw [← map_add, tsub_add_cancel_of_le hwa]
    rcases nonneg_or_nonpos q with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · refine ⟨c, ι_injective ?_⟩
      rw [map_mul]
      linear_combination hsum + hq
    · have h0 : 0 ≤ ι M * ι c := mul_nonneg (ι_nonneg M) (ι_nonneg c)
      have h1 : ι M * -ι c = -(ι M * ι c) := by ring
      have hle : (ι a : DiffRing V) ≤ ι w := by linarith
      have he : a = w := le_antisymm (ι_le_ι.mp hle) hwa
      rw [he, tsub_self]
      exact dvd_zero M
  · rw [tsub_eq_zero_of_le haw]
    exact dvd_zero M

theorem lin_mod_congr {c k M : V} (T : V) (h : c % M = k % M) :
    ((c + 1) * T + 1) % M = ((k + 1) * T + 1) % M := by
  obtain ⟨q, hq⟩ := ringSub_of_mod_eq h
  apply mod_eq_of_sub_eq (q := q * ι T)
  simp only [map_add, map_mul, map_one]
  linear_combination ι T * hq

/-- One Chinese-remainder step: change `a` by a ring multiple of `P` so that its
residue modulo the coprime `M` becomes that of `t`. -/
theorem crt_step {P M : V} (hP : 0 < P) (hM : 0 < M) (hb : Bez P M 1) (a t : V) :
    ∃ a' : V, a' % M = t % M ∧ ∃ q : DiffRing V, ι a' - ι a = ι P * q := by
  obtain ⟨α, β, hab⟩ := (bez_one_iff_ring (a := P) (b := M)).mp hb
  obtain ⟨K, hK⟩ := nonneg_iff.mp (abs_nonneg (ι P * α * (ι t - ι a)))
  have hPM : (1 : DiffRing V) ≤ ι P * ι M := by
    have h1 : (1 : V) ≤ P * M := pos_iff_one_le.mp (mul_pos hP hM)
    calc (1 : DiffRing V) = ι 1 := (map_one (ι (V := V))).symm
      _ ≤ ι (P * M) := ι_le_ι.mpr h1
      _ = ι P * ι M := map_mul (ι (V := V)) _ _
  have hK0 : (0 : DiffRing V) ≤ ι K := ι_nonneg K
  have hKle : ι K ≤ ι P * ι M * ι K := le_mul_of_one_le_left hK0 hPM
  have habs : -(ι P * α * (ι t - ι a)) ≤ ι K := by
    rw [← hK]
    exact neg_le_abs _
  have ha0 : (0 : DiffRing V) ≤ ι a := ι_nonneg a
  obtain ⟨a', ha'⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤
      ι a + ι P * α * (ι t - ι a) + ι P * ι M * ι K by linarith)
  refine ⟨a', mod_eq_of_sub_eq (q := β * (ι a - ι t) + ι P * ι K) ?_,
    α * (ι t - ι a) + ι M * ι K, ?_⟩
  · rw [← ha']
    linear_combination (ι t - ι a) * hab
  · rw [← ha']
    ring

/-- Residues modulo the first `n` pairwise coprime moduli determine the residue
modulo their product; the product stays coprime to the later moduli. -/
theorem mod_prodM (T N x y : V)
    (hcop : ∀ i j, i < j → j < N → Bez ((i + 1) * T + 1) ((j + 1) * T + 1) 1)
    (hres : ∀ k < N, x % ((k + 1) * T + 1) = y % ((k + 1) * T + 1)) (n : V) :
    n ≤ N → x % prodM T n = y % prodM T n ∧
      ∀ j < N, n ≤ j → Bez (prodM T n) ((j + 1) * T + 1) 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · simp only [Bez]
    definability
  case zero =>
    intro _
    refine ⟨by simp, fun j _ _ => ⟨0, 0, 1, 0, by simp⟩⟩
  case succ n ih =>
    intro hn
    have hnN : n < N := LO.FirstOrder.Arithmetic.succ_le_iff_lt.mp hn
    obtain ⟨h1, h2⟩ := ih (le_of_lt hnN)
    rw [prodM_succ]
    refine ⟨mod_mul_of_bez h1 (hres n hnN) (h2 n hnN le_rfl), fun j hj hnj => ?_⟩
    exact bez_mul (h2 j hj (le_trans le_self_add hnj))
      (hcop n j (LO.FirstOrder.Arithmetic.succ_le_iff_lt.mp hnj) hj)

/-! ### The encoded product -/

theorem encProd_core (T Q : V) (hTQ : 1 ≤ T * Q) (n : V) :
    (power T n * ModelRepFactorial.asc Q n) % (T * Q - 1) = prodM T n % (T * Q - 1) := by
  have hD : ι (T * Q - 1) = ι T * ι Q - 1 := by
    have h1 : T * Q - 1 + 1 = T * Q := tsub_add_cancel_of_le hTQ
    have h2 := congrArg (ι (V := V)) h1
    rw [map_add, map_one, map_mul] at h2
    linear_combination h2
  induction n using ISigma1.sigma1_succ_induction
  · unfold ModelRepFactorial.asc
    definability
  case zero =>
    rw [power_zero, ModelRepFactorial.asc_zero, prodM_zero, one_mul]
  case succ n ih =>
    obtain ⟨q, hq⟩ := ringSub_of_mod_eq ih
    apply mod_eq_of_sub_eq
      (q := ι (power T n * ModelRepFactorial.asc Q n) + q * ((ι n + 1) * ι T + 1))
    rw [power_succ, ModelRepFactorial.asc_succ, prodM_succ, hD]
    rw [hD] at hq
    simp only [map_add, map_mul, map_one] at hq ⊢
    linear_combination ((ι n + 1) * ι T + 1) * hq

/-- The explicit encoding of `MRDP.encodedModuliProduct` computes `prodM`. -/
theorem encProd_eq (N T : V) (hT : 0 < T) :
    (power T N * (fact N * binom (power ((N + 1) * T + 1) N + 2 + N) N)) %
      (T * (power ((N + 1) * T + 1) N + 2) - 1) = prodM T N := by
  have hQ1 : (1 : V) ≤ power ((N + 1) * T + 1) N + 2 :=
    le_trans one_le_two le_add_self
  have hTQ : 1 ≤ T * (power ((N + 1) * T + 1) N + 2) :=
    one_le_mul (pos_iff_one_le.mp hT) hQ1
  have h := encProd_core T (power ((N + 1) * T + 1) N + 2) hTQ N
  have hle : prodM T N ≤ power ((N + 1) * T + 1) N := prodM_le T N N le_rfl
  have hQle : power ((N + 1) * T + 1) N + 2 ≤ T * (power ((N + 1) * T + 1) N + 2) :=
    LO.FirstOrder.Arithmetic.le_mul_of_pos_left hT
  have hlt1 : prodM T N + 1 < power ((N + 1) * T + 1) N + 2 :=
    _root_.add_lt_add_of_le_of_lt hle one_lt_two
  have hlt : prodM T N < T * (power ((N + 1) * T + 1) N + 2) - 1 :=
    lt_tsub_iff_right.mpr (lt_of_lt_of_le hlt1 hQle)
  rw [mod_eq_self_of_lt hlt] at h
  exact h

/-! ### Irreducible divisors -/

theorem bez_swap' {a b g : V} (h : Bez a b g) : Bez b a g := by
  obtain ⟨u, v, w, z, he⟩ := h
  refine ⟨v, u, z, w, ?_⟩
  calc g + b * v + a * u = g + a * u + b * v := by ring
    _ = a * w + b * z := he
    _ = b * z + a * w := by ring

/-- The least divisor `> 1` of `M > 1` has only the trivial divisors. -/
theorem exists_irred_dvd (M : V) (hM : 1 < M) :
    ∃ p : V, 1 < p ∧ p ∣ M ∧ ∀ d, d ∣ p → d = 1 ∨ d = p := by
  have hP : 𝚺₁-Predicate (fun d : V => 1 < d ∧ d ∣ M) := by definability
  obtain ⟨p, ⟨hp1, hpM⟩, hmin⟩ :=
    InductionOnHierarchy.least_number 𝚺 1 hP (x := M) ⟨hM, dvd_refl M⟩
  refine ⟨p, hp1, hpM, fun d hd => ?_⟩
  have hp0 : 0 < p := lt_of_le_of_lt (Arithmetic.zero_le 1) hp1
  have hdle : d ≤ p := LO.FirstOrder.Arithmetic.le_of_dvd hp0 hd
  have hd0 : 0 < d := pos_iff_ne_zero.mpr (by
    rintro rfl
    exact hp0.ne' (zero_dvd_iff.mp hd))
  rcases lt_or_eq_of_le hdle with hlt | heq
  · left
    have hn : ¬ (1 < d ∧ d ∣ M) := hmin d hlt
    have hd1 : ¬ 1 < d := fun h1 => hn ⟨h1, dvd_trans hd hpM⟩
    exact le_antisymm (not_lt.mp hd1) (pos_iff_one_le.mp hd0)
  · right
    exact heq

theorem bez_of_irred {p t : V} (hirr : ∀ d, d ∣ p → d = 1 ∨ d = p) (h : ¬ p ∣ t) :
    Bez p t 1 := by
  obtain ⟨g, hgp, hgt, hbez⟩ := gcd_certificate_exists p t
  rcases hirr g hgp with hg | hg
  · rw [hg] at hbez
    exact hbez
  · exact (h (by rw [← hg]; exact hgt)).elim

theorem euclid_of_irred {p : V} (hirr : ∀ d, d ∣ p → d = 1 ∨ d = p) {x y : V}
    (hxy : p ∣ x * y) : p ∣ x ∨ p ∣ y := by
  by_cases hx : p ∣ x
  · exact Or.inl hx
  · exact Or.inr (unit_certificate_cancel (bez_swap' (bez_of_irred hirr hx)) hxy)

/-! ### Falling factorials -/

/-- `(m+1)!·binom a (m+1) = (a-m)·(m!·binom a m)`, also for `a ≤ m`. -/
theorem desc_succ (a m : V) :
    fact (m + 1) * binom a (m + 1) = (a - m) * (fact m * binom a m) := by
  rcases lt_or_ge a (m + 1) with h | h
  · rw [binom_eq_zero_of_lt a (m + 1) h, mul_zero,
      tsub_eq_zero_of_le (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp h), zero_mul]
  · obtain ⟨j, rfl⟩ := exists_add_of_le h
    have h1 := binom_mul_fact (m + 1) j
    have h2 := binom_mul_fact m (j + 1)
    have e1 : m + (j + 1) = m + 1 + j := by ring
    rw [e1] at h2
    have hsub : m + 1 + j - m = j + 1 := by
      rw [← e1]
      exact add_tsub_cancel_left m (j + 1)
    rw [hsub]
    apply mul_right_cancel₀ (fact_pos j).ne'
    calc fact (m + 1) * binom (m + 1 + j) (m + 1) * fact j = fact (m + 1 + j) := by
          rw [← h1]; ring
      _ = binom (m + 1 + j) m * fact m * fact (j + 1) := h2.symm
      _ = (j + 1) * (fact m * binom (m + 1 + j) m) * fact j := by rw [fact_succ]; ring

/-- An irreducible divisor of a falling factorial divides one of its factors. -/
theorem dvd_factor_of_dvd_desc (p a : V) (h1 : ¬ p ∣ 1)
    (heu : ∀ x y : V, p ∣ x * y → p ∣ x ∨ p ∣ y) (m : V) :
    p ∣ fact m * binom a m → ∃ j < m, p ∣ a - j := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro h
    exfalso
    apply h1
    simpa using h
  case succ m ih =>
    intro h
    rw [desc_succ] at h
    rcases heu _ _ h with h' | h'
    · exact ⟨m, lt_add_one m, h'⟩
    · obtain ⟨j, hj, hj'⟩ := ih h'
      exact ⟨j, lt_trans hj (lt_add_one m), hj'⟩

/-- A divisor of one factor divides the falling factorial. -/
theorem dvd_desc_of_dvd (M a w : V) (hw : M ∣ a - w) (m : V) :
    w < m → M ∣ fact m * binom a m := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro h
    exact absurd h (not_lt.mpr (Arithmetic.zero_le w))
  case succ m ih =>
    intro h
    rw [desc_succ]
    rcases lt_or_eq_of_le (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp h) with hlt | heq
    · exact Dvd.dvd.mul_left (ih hlt) _
    · rw [← heq]
      exact Dvd.dvd.mul_right hw _

/-! ### Natural expressions -/

theorem evalSemiring_mono' {τ : Type*} (e : NatExpr τ) {u u' : τ → V}
    (h : ∀ j, u j ≤ u' j) : e.evalSemiring u ≤ e.evalSemiring u' := by
  induction e with
  | constant n => exact le_rfl
  | var j => exact h j
  | add p q hp hq => exact _root_.add_le_add hp hq
  | mul p q hp hq => exact mul_le_mul hp hq (Arithmetic.zero_le _) (Arithmetic.zero_le _)

theorem evalSemiring_mod' {τ : Type*} (e : NatExpr τ) {u u' : τ → V} {M : V} (hM : 0 < M)
    (h : ∀ j, u j % M = u' j % M) : e.evalSemiring u % M = e.evalSemiring u' % M := by
  induction e with
  | constant n => rfl
  | var j => exact h j
  | add p q hp hq =>
    show (p.evalSemiring u + q.evalSemiring u) % M = (p.evalSemiring u' + q.evalSemiring u') % M
    rw [mod_add (a := p.evalSemiring u) (b := q.evalSemiring u) hM, hp, hq,
      ← mod_add (a := p.evalSemiring u') (b := q.evalSemiring u') hM]
  | mul p q hp hq =>
    show (p.evalSemiring u * q.evalSemiring u) % M = (p.evalSemiring u' * q.evalSemiring u') % M
    rw [mod_mul (a := p.evalSemiring u) (b := q.evalSemiring u) hM, hp, hq,
      ← mod_mul (a := p.evalSemiring u') (b := q.evalSemiring u') hM]

/-- Polynomial evaluation with `𝚺₁`-definable coordinates is `𝚺₁`-definable. -/
theorem evalSemiring_definable' {τ : Type*} {k : ℕ} (e : NatExpr τ)
    (ρ : τ → (Fin k → V) → V) (hρ : ∀ j, 𝚺₁.DefinableFunction (ρ j)) :
    𝚺₁.DefinableFunction (fun z : Fin k → V => e.evalSemiring (fun j => ρ j z)) := by
  induction e with
  | constant n => exact HierarchySymbol.DefinableFunction.const (n : V)
  | var j => exact hρ j
  | add p q hp hq => exact HierarchySymbol.DefinableFunction₂.comp (F := (· + ·)) hp hq
  | mul p q hp hq => exact HierarchySymbol.DefinableFunction₂.comp (F := (· * ·)) hp hq

theorem unNpair_le' : ∀ {n : ℕ} (i : Fin n) (W : V), unNpair i W ≤ W
  | 0, i, _ => i.elim0
  | _ + 1, i, W => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [unNpair, Fin.cases_zero]
      exact pi₁_le_self W
    · simp only [unNpair, Fin.cases_succ]
      exact le_trans (unNpair_le' j (pi₂ W)) (pi₂_le_self W)

end DiophantineConsistency.ModelBoundedForallArith
