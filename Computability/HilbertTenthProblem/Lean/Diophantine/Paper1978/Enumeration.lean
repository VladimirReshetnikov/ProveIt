import Diophantine.Paper1978.Pairing
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.NumberTheory.SumFourSquares

/-!
# Jones 1978, §3: the enumeration `W₁, W₂, …` of the Diophantine sets

The polynomials `Pₙ` in the variables `X₀, X₁, …` with nonnegative integer coefficients and
no constant term are defined by
`P₀ = 0`, `P_{3i+2} = Xᵢ`, `P_{3i} = P_{K(i)} + P_{L(i)}` (`i ≥ 1`),
`P_{3i+1} = P_{K(i)} · P_{L(i)}`,
and `x ∈ Wₙ ⟺ (∃ X₀, …, Xₙ ∈ ℤ) P_{K(n)}(X) = P_{L(n)}(X) + x`.

* **Lemma 3.1.** Each Diophantine set of positive integers `W` may be represented, for
  `x > 0`, in the form `x ∈ W ⟺ (∃ X₀, …, Xₙ ∈ ℤ) P(X₀, …, Xₙ) = x` where `P` is a
  polynomial with integer coefficients and no constant term (Putnam's device and
  Lagrange's four-square theorem).  Combined with the enumeration: every Diophantine set
  of positive integers is some `Wₙ` (`lemma_3_1`).

Assignments of the variables are functions `ℕ → ℤ`; `Pₖ` depends only on `Xᵢ` with
`3i + 2 ≤ k`, so nothing changes by allowing infinitely many variables.

That the list contains every recursively enumerable set is the theorem of Davis, Putnam,
Robinson and Matijasevič, which the article cites; it is neither used nor assumed here.
-/

namespace Jones1978

open MvPolynomial

/-! ### The polynomials `Pₙ` -/

/-- The polynomials `Pₙ`, evaluated at an assignment `X : ℕ → ℤ`. -/
def P : ℕ → (ℕ → ℤ) → ℤ
  | n, X =>
    if n = 0 then 0
    else if n % 3 = 2 then X (n / 3)
    else if n % 3 = 0 then P (K (n / 3)) X + P (L (n / 3)) X
    else P (K (n / 3)) X * P (L (n / 3)) X
termination_by n => n
decreasing_by all_goals (have := K_le (n / 3); have := L_le (n / 3); omega)

theorem P_zero (X : ℕ → ℤ) : P 0 X = 0 := by rw [P]; simp

theorem P_var (i : ℕ) (X : ℕ → ℤ) : P (3 * i + 2) X = X i := by
  rw [P]
  have h1 : 3 * i + 2 ≠ 0 := by omega
  have h2 : (3 * i + 2) % 3 = 2 := by omega
  have h3 : (3 * i + 2) / 3 = i := by omega
  simp [h2, h3]

theorem P_add {i : ℕ} (hi : 1 ≤ i) (X : ℕ → ℤ) : P (3 * i) X = P (K i) X + P (L i) X := by
  rw [P]
  have h1 : 3 * i ≠ 0 := by omega
  have h2 : (3 * i) % 3 = 0 := by omega
  have h3 : (3 * i) / 3 = i := by omega
  simp [h1, h2, h3]

theorem P_mul (i : ℕ) (X : ℕ → ℤ) : P (3 * i + 1) X = P (K i) X * P (L i) X := by
  rw [P]
  have h1 : 3 * i + 1 ≠ 0 := by omega
  have h2 : (3 * i + 1) % 3 = 1 := by omega
  have h3 : (3 * i + 1) / 3 = i := by omega
  simp [h2, h3]

theorem P_one (X : ℕ → ℤ) : P 1 X = 0 := by
  have := P_mul 0 X
  simp only [mul_zero, zero_add] at this
  rw [this, K, L, KL, P_zero]; simp

/-- The set `Wₙ`. -/
def W (n : ℕ) : Set ℕ := {x | ∃ X : ℕ → ℤ, P (K n) X = P (L n) X + x}

/-! ### Terms: polynomials with nonnegative coefficients and no constant term -/

/-- Formal terms built from the variables by `+` and `·` (and `0`). -/
inductive Term
  | zero
  | var (i : ℕ)
  | add (s t : Term)
  | mul (s t : Term)

namespace Term

def eval (X : ℕ → ℤ) : Term → ℤ
  | zero => 0
  | var i => X i
  | add s t => s.eval X + t.eval X
  | mul s t => s.eval X * t.eval X

/-- `n` copies of `t` added together. -/
def smul : ℕ → Term → Term
  | 0, _ => zero
  | n + 1, t => add (smul n t) t

theorem eval_smul (X : ℕ → ℤ) (n : ℕ) (t : Term) : (smul n t).eval X = n * t.eval X := by
  induction n with
  | zero => simp [smul, eval]
  | succ n ih => simp [smul, eval, ih]; ring

/-- Substitution of terms for the variables. -/
def subst (f : ℕ → Term) : Term → Term
  | zero => zero
  | var i => f i
  | add s t => add (s.subst f) (t.subst f)
  | mul s t => mul (s.subst f) (t.subst f)

theorem eval_subst (X : ℕ → ℤ) (f : ℕ → Term) (t : Term) :
    (t.subst f).eval X = t.eval (fun i => (f i).eval X) := by
  induction t with
  | zero => rfl
  | var i => rfl
  | add s t ihs iht => simp [subst, eval, ihs, iht]
  | mul s t ihs iht => simp [subst, eval, ihs, iht]

/-- Every term is one of the `Pₖ`. -/
theorem exists_index (t : Term) : ∃ k, ∀ X, P k X = t.eval X := by
  induction t with
  | zero => exact ⟨0, fun X => P_zero X⟩
  | var i => exact ⟨3 * i + 2, fun X => P_var i X⟩
  | add s t ihs iht =>
    obtain ⟨a, ha⟩ := ihs
    obtain ⟨b, hb⟩ := iht
    rcases Nat.eq_zero_or_pos (J a b) with h0 | hpos
    · -- `a = b = 0`
      have ha0 : a = 0 := by have := le_J_left a b; omega
      have hb0 : b = 0 := by have := le_J_right a b; omega
      refine ⟨0, fun X => ?_⟩
      simp only [eval, ← ha, ← hb, ha0, hb0, P_zero, add_zero]
    · refine ⟨3 * J a b, fun X => ?_⟩
      rw [P_add hpos, K_J, L_J, ha, hb]; rfl
  | mul s t ihs iht =>
    obtain ⟨a, ha⟩ := ihs
    obtain ⟨b, hb⟩ := iht
    refine ⟨3 * J a b + 1, fun X => ?_⟩
    rw [P_mul, K_J, L_J, ha, hb]; rfl

end Term

/-- Functions of the form `s.eval − t.eval` for terms `s, t`: the integer polynomials
without constant term. -/
def Rep (f : (ℕ → ℤ) → ℤ) : Prop := ∃ s t : Term, ∀ X, f X = s.eval X - t.eval X

namespace Rep

theorem zero : Rep (fun _ => 0) := ⟨Term.zero, Term.zero, fun _ => by simp [Term.eval]⟩

theorem var (i : ℕ) : Rep (fun X => X i) :=
  ⟨Term.var i, Term.zero, fun _ => by simp [Term.eval]⟩

theorem add {f g} (hf : Rep f) (hg : Rep g) : Rep (fun X => f X + g X) := by
  obtain ⟨s, t, hst⟩ := hf
  obtain ⟨s', t', hst'⟩ := hg
  exact ⟨Term.add s s', Term.add t t', fun X => by simp [Term.eval, hst, hst']; ring⟩

theorem neg {f} (hf : Rep f) : Rep (fun X => -f X) := by
  obtain ⟨s, t, hst⟩ := hf
  exact ⟨t, s, fun X => by simp [hst]⟩

theorem sub {f g} (hf : Rep f) (hg : Rep g) : Rep (fun X => f X - g X) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

theorem mul {f g} (hf : Rep f) (hg : Rep g) : Rep (fun X => f X * g X) := by
  obtain ⟨s, t, hst⟩ := hf
  obtain ⟨s', t', hst'⟩ := hg
  exact ⟨Term.add (Term.mul s s') (Term.mul t t'), Term.add (Term.mul s t') (Term.mul t s'),
    fun X => by simp [Term.eval, hst, hst']; ring⟩

theorem nat_mul {f} (hf : Rep f) (n : ℕ) : Rep (fun X => n * f X) := by
  obtain ⟨s, t, hst⟩ := hf
  exact ⟨Term.smul n s, Term.smul n t, fun X => by simp [Term.eval_smul, hst]; ring⟩

theorem int_mul {f} (hf : Rep f) (c : ℤ) : Rep (fun X => c * f X) := by
  rcases le_or_gt 0 c with hc | hc
  · have := hf.nat_mul c.toNat
    simpa [Int.toNat_of_nonneg hc] using this
  · have := (hf.nat_mul (-c).toNat).neg
    have hc' : ((-c).toNat : ℤ) = -c := Int.toNat_of_nonneg (by linarith)
    simp only [hc'] at this
    simpa using this

theorem congr {f g} (hf : Rep f) (h : ∀ X, g X = f X) : Rep g := by
  obtain ⟨s, t, hst⟩ := hf
  exact ⟨s, t, fun X => by rw [h, hst]⟩

end Rep

/-- Every integer polynomial is a term difference plus a constant. -/
theorem exists_rep_of_mvPolynomial {k : ℕ} (Q : MvPolynomial (Fin k) ℤ) (σ : ℕ → Term) :
    ∃ c : ℤ, Rep (fun X => eval (fun i : Fin k => (σ i).eval X) Q - c) := by
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨a, Rep.zero.congr (fun X => by simp)⟩
  | add p q hp hq =>
    obtain ⟨c, hc⟩ := hp
    obtain ⟨d, hd⟩ := hq
    exact ⟨c + d, (hc.add hd).congr (fun X => by simp [eval_add]; ring)⟩
  | mul_X p i hp =>
    obtain ⟨c, hc⟩ := hp
    -- `(f + c) · σᵢ = f σᵢ + c σᵢ`
    have hσ : Rep (fun X => (σ i).eval X) := ⟨σ i, Term.zero, fun X => by simp [Term.eval]⟩
    refine ⟨0, ((hc.mul hσ).add (hσ.int_mul c)).congr (fun X => ?_)⟩
    simp [eval_mul, eval_X]
    ring

/-! ### Diophantine sets and Lemma 3.1 -/

/-- A Diophantine set: `x ∈ S ⟺ (∃ z ∈ ℕᵐ) Q(x, z) = 0` for an integer polynomial `Q`. -/
def IsDiophantine (S : Set ℕ) : Prop :=
  ∃ (m : ℕ) (Q : MvPolynomial (Fin (m + 1)) ℤ), ∀ x : ℕ,
    x ∈ S ↔ ∃ z : Fin m → ℕ, eval (Fin.cons (x : ℤ) (fun i => (z i : ℤ))) Q = 0

/-- The four-square term `X_{4i}² + X_{4i+1}² + X_{4i+2}² + X_{4i+3}²`. -/
def sqTerm (i : ℕ) : Term :=
  .add (.add (.mul (.var (4 * i)) (.var (4 * i))) (.mul (.var (4 * i + 1)) (.var (4 * i + 1))))
    (.add (.mul (.var (4 * i + 2)) (.var (4 * i + 2))) (.mul (.var (4 * i + 3)) (.var (4 * i + 3))))

theorem sqTerm_eval (X : ℕ → ℤ) (i : ℕ) :
    (sqTerm i).eval X = X (4 * i) ^ 2 + X (4 * i + 1) ^ 2 + X (4 * i + 2) ^ 2 + X (4 * i + 3) ^ 2 := by
  simp [sqTerm, Term.eval]; ring

theorem sqTerm_nonneg (X : ℕ → ℤ) (i : ℕ) : 0 ≤ (sqTerm i).eval X := by
  rw [sqTerm_eval]; positivity

/-- Every value of the four-square terms is attained, at every list of natural numbers
(Lagrange). -/
theorem exists_sqTerm_eq (v : ℕ → ℕ) : ∃ X : ℕ → ℤ, ∀ i, (sqTerm i).eval X = v i := by
  classical
  have h : ∀ i, ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = v i := fun i =>
    Nat.sum_four_squares (v i)
  choose a b c d habcd using h
  refine ⟨fun j => if j % 4 = 0 then a (j / 4) else if j % 4 = 1 then b (j / 4)
    else if j % 4 = 2 then c (j / 4) else d (j / 4), fun i => ?_⟩
  rw [sqTerm_eval]
  have e0 : (4 * i) % 4 = 0 := by omega
  have e1 : (4 * i + 1) % 4 = 1 := by omega
  have e2 : (4 * i + 2) % 4 = 2 := by omega
  have e3 : (4 * i + 3) % 4 = 3 := by omega
  have d0 : (4 * i) / 4 = i := by omega
  have d1 : (4 * i + 1) / 4 = i := by omega
  have d2 : (4 * i + 2) / 4 = i := by omega
  have d3 : (4 * i + 3) / 4 = i := by omega
  simp only [e0, e1, e2, e3, d0, d1, d2, d3]
  simp
  exact_mod_cast habcd i

/-- **Lemma 3.1** together with the enumeration: every Diophantine set of positive
integers is some `Wₙ`. -/
theorem lemma_3_1 {S : Set ℕ} (hS : IsDiophantine S) : ∃ n, ∀ x, 0 < x → (x ∈ S ↔ x ∈ W n) := by
  obtain ⟨m, Q, hQ⟩ := hS
  -- the substitution `σ : Fin (m+1) → Term` and the term difference representing `Q ∘ σ`
  obtain ⟨c, f, hf⟩ : ∃ c : ℤ, Rep (fun X => eval (fun i : Fin (m + 1) => (sqTerm i).eval X) Q - c) :=
    exists_rep_of_mvPolynomial Q sqTerm
  -- Putnam's polynomial `R = σ₀ (1 − (Q ∘ σ)²)`
  set R : (ℕ → ℤ) → ℤ := fun X =>
    (sqTerm 0).eval X * (1 - (eval (fun i : Fin (m + 1) => (sqTerm i).eval X) Q) ^ 2) with hR
  have hRrep : Rep R := by
    -- `σ₀ (1 − (g + c)²) = σ₀ − σ₀ g² − 2c σ₀ g − c² σ₀` with `g = Q∘σ − c`
    have hσ : Rep (fun X => (sqTerm 0).eval X) := ⟨sqTerm 0, Term.zero, fun X => by simp [Term.eval]⟩
    have hg : Rep (fun X => eval (fun i : Fin (m + 1) => (sqTerm i).eval X) Q - c) := ⟨f, hf⟩
    have h1 := hσ.sub ((hσ.mul (hg.mul hg)).add (((hσ.mul hg).int_mul (2 * c)).add (hσ.int_mul (c * c))))
    refine h1.congr (fun X => ?_)
    simp only [hR]
    ring
  obtain ⟨s, t, hst⟩ := hRrep
  obtain ⟨u, hu⟩ := s.exists_index
  obtain ⟨v, hv⟩ := t.exists_index
  refine ⟨J u v, fun x hx => ?_⟩
  -- `x ∈ S ⟺ ∃ X, R X = x`
  have key : x ∈ S ↔ ∃ X : ℕ → ℤ, R X = x := by
    rw [hQ]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨X, hX⟩ := exists_sqTerm_eq (fun i => if i = 0 then x else if h : i - 1 < m then z ⟨i - 1, h⟩ else 0)
      refine ⟨X, ?_⟩
      have hσ : (fun i : Fin (m + 1) => (sqTerm i).eval X) = Fin.cons (x : ℤ) (fun i => (z i : ℤ)) := by
        funext i
        rw [hX]
        refine Fin.cases ?_ (fun i => ?_) i
        · simp
        · simp only [Fin.val_succ, Fin.cons_succ]
          simp [i.isLt]
      simp only [hR, hσ, hz]
      rw [hX 0]
      simp
    · rintro ⟨X, hX⟩
      simp only [hR] at hX
      -- `σ₀ ≥ 0` and `1 − q² ≤ 1`, so a positive value forces `q = 0` and `σ₀ = x`
      set q := eval (fun i : Fin (m + 1) => (sqTerm i).eval X) Q with hq
      have hσ0 := sqTerm_nonneg X 0
      have hq0 : q = 0 := by
        by_contra hne
        have : 1 ≤ q ^ 2 := by
          have : 0 < q ^ 2 := by positivity
          omega
        have : (sqTerm 0).eval X * (1 - q ^ 2) ≤ 0 := by nlinarith
        have : (0 : ℤ) < x := by exact_mod_cast hx
        linarith
      rw [hq0] at hX
      simp at hX
      -- the values `σᵢ X` are natural numbers
      have hnat : ∀ i, ∃ n : ℕ, (sqTerm i).eval X = n := fun i =>
        ⟨((sqTerm i).eval X).toNat, (Int.toNat_of_nonneg (sqTerm_nonneg X i)).symm⟩
      choose n hn using hnat
      refine ⟨fun i => n (i.val + 1), ?_⟩
      have hσ : (fun i : Fin (m + 1) => (sqTerm i).eval X) = Fin.cons (x : ℤ) (fun i : Fin m => (n (i.val + 1) : ℤ)) := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [← hX]
        · simp [hn]
      rw [← hσ]
      exact hq0
  rw [key]
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    rw [K_J, L_J, hu, hv]
    have := hst X
    rw [hX] at this
    linarith
  · rintro ⟨X, hX⟩
    exact ⟨X, by rw [K_J, L_J, hu, hv] at hX; rw [hst]; linarith⟩

end Jones1978
