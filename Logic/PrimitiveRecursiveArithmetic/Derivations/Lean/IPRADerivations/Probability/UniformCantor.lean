import IPRADerivations.Core.OrderCertificates

/-!
# The uniform law and the Cantor law on fair bits

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/foundation.tex`, Section "Independent copies,
a uniform law, and a singular continuous law", the finite estimates, cleared for natural terms:

* `num_le`: `a ≤ b` gives the iPRA inequality of numerals;
* `uniform_cauchy`: "Let `U_n` assign the midpoint `(j + 1/2) 2^{-n}` to the `j`th dyadic cell. For `m ≥ n`,
  `|U_m − U_n| ≤ 2^{-n-1}` on every common row": for a row `ω` of level `m = n + s` in the cell `j`
  (`j P ≤ ω < (j + 1) P`, `P = 2^s`), cleared by `2^{m+1}`: `|(2ω + 1) − (2j + 1) P| ≤ P`, two-sided;
* `tern`, `cantor_tail`: for `C_n = ∑_{j ≤ n} 2 b_j / 3^j`, "The remainder is bounded by `3^{-n}`": the
  ternary block `T = ∑ 2 b_j 3^{s-j}` of `s` further bits satisfies `T + 1 ≤ 3^s`, so
  `C_{n+s} − C_n ≤ 3^{-n} − 3^{-(n+s)}`;
* `cover_rate`: "Choosing `n = 3k` makes this at most `2^{-k}`, since `(2/3)^3 < 1/2`":
  `2^{3k} · 2^k ≤ 3^{3k}`.
-/

namespace LeanProofs.IPRA.Probability.UniformCantor

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- An inequality of numerals. -/
theorem num_le {a b : ℕ} (h : a ≤ b) : Γ ⊢[PRAAx] le (num a) (num b) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  ipra_le (c : Groth (Q Γ)) using push_cast; ring

/-- The midpoints of nested dyadic cells: `|(2ω + 1) − (2j + 1) P| ≤ P`. -/
theorem uniform_cauchy {ω j P : PTm n} (h₁ : Γ ⊢[PRAAx] le (j * P) ω)
    (h₂ : Γ ⊢[PRAAx] le (succ ω) (succ j * P)) :
    (Γ ⊢[PRAAx] le ((num 2 * j + num 1) * P) (num 2 * ω + num 1 + P)) ∧
      (Γ ⊢[PRAAx] le (num 2 * ω + num 1) ((num 2 * j + num 1) * P + P)) := by
  refine ⟨?_, ?_⟩
  · ipra_le 2 * sl h₁ + 1
  · ipra_le 2 * sl h₂ + 1

/-- The ternary block of further Cantor digits: `tern [b_s, …, b_1] = ∑ 2 b_j 3^{s−j}`. -/
def tern : List (PTm n) → PTm n
  | [] => zero
  | b :: L => num 3 * tern L + num 2 * b

/-- The Cantor remainder: `T + 1 ≤ 3^s` for `s` further bits. -/
theorem cantor_tail : (L : List (PTm n)) → (∀ b ∈ L, Γ ⊢[PRAAx] le b (succ zero)) →
    (Γ ⊢[PRAAx] le (succ (tern L)) (num (3 ^ L.length)))
  | [], _ => by
    show Γ ⊢[PRAAx] le (succ zero) (num (3 ^ 0))
    ipra_le 0 using push_cast; ring
  | b :: L, h => by
    have ih := cantor_tail L fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hb : Γ ⊢[PRAAx] le b (succ zero) := h b (List.mem_cons_self ..)
    show Γ ⊢[PRAAx] le (succ (num 3 * tern L + num 2 * b)) (num (3 ^ (L.length + 1)))
    ipra_le 3 * sl ih + 2 * sl hb using push_cast; ring

/-- The covering rate: `(2/3)^{3k} ≤ 2^{-k}`, cleared: `2^{3k} · 2^k ≤ 3^{3k}`. -/
theorem cover_rate (k : ℕ) : Γ ⊢[PRAAx] le (num (2 ^ (3 * k) * 2 ^ k)) (num (3 ^ (3 * k))) := by
  apply num_le
  have h : 2 ^ (3 * k) * 2 ^ k = 16 ^ k := by
    rw [show (16 : ℕ) = 2 ^ 3 * 2 by norm_num, Nat.mul_pow, pow_mul]
  have h' : 3 ^ (3 * k) = 27 ^ k := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num, pow_mul]
  rw [h, h']
  exact Nat.pow_le_pow_left (by norm_num) k

end LeanProofs.IPRA.Probability.UniformCantor
