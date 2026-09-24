import Diophantine.Paper1982.NineMain
import Diophantine.Paper1976.NthPrimePolynomial
import Diophantine.Paper1978.Pairing

/-!
# Theorem 4 with fourteen witnesses

The article remarks that the Matijasevič–Robinson reduction to thirteen unknowns gives
`l = 13` and hence `k = 14` in Theorem 4.  Here the reduction to nine unknowns
(`Jones1982.nine_unknowns_dioph`) is applied to the set of codes `(n + m)² + 3m + n + 1` of the
graph of the `n`th prime.  The graph then has a representation with nine unknowns, Putnam's
construction adds one witness, and four unused witnesses bring the count to fourteen.
-/

namespace JSWW1976

open MvPolynomial

/-- `2J(n, m) + 1`, a polynomial injective code of pairs. -/
def pairCode (n m : ℕ) : ℕ := (n + m) ^ 2 + 3 * m + n + 1

theorem pairCode_injective {n m n' m' : ℕ} (h : pairCode n m = pairCode n' m') :
    n = n' ∧ m = m' := by
  apply Jones1978.J_injective
  have h1 := Jones1978.two_J n m
  have h2 := Jones1978.two_J n' m'
  simp only [pairCode] at h
  omega

/-- The codes of the graph of the `n`th prime form a Diophantine set. -/
theorem nthPrime_codes_dioph :
    Dioph {v : Unit → ℕ | v () ∈ {t | ∃ n m, t = pairCode n m ∧ nthPrime n = m}} := by
  have hgraph := nthPrime_graph_dioph
  have hT : Dioph {u : Unit ⊕ Fin 2 → ℕ |
      u (Sum.inl ()) = pairCode (u (Sum.inr 0)) (u (Sum.inr 1)) ∧
        u ∘ Sum.inr ∈ {v : Fin 2 → ℕ | Nat.nth Nat.Prime (v 0 - 1) = v 1}} := by
    refine Dioph.inter ?_ (Dioph.reindex_dioph _ Sum.inr hgraph)
    have h0 := Dioph.proj_dioph (α := Unit ⊕ Fin 2) (Sum.inl ())
    have ha := Dioph.proj_dioph (α := Unit ⊕ Fin 2) (Sum.inr 0)
    have hb := Dioph.proj_dioph (α := Unit ⊕ Fin 2) (Sum.inr 1)
    have hc : Dioph.DiophFn fun u : Unit ⊕ Fin 2 → ℕ =>
        pairCode (u (Sum.inr 0)) (u (Sum.inr 1)) := by
      unfold pairCode
      have hs := Dioph.add_dioph ha hb
      have hsq := Dioph.mul_dioph hs hs
      have h3 := Dioph.mul_dioph (Dioph.const_dioph 3) hb
      have := Dioph.add_dioph (Dioph.add_dioph (Dioph.add_dioph hsq h3) ha) (Dioph.const_dioph 1)
      simpa only [sq, Function.const_apply] using this
    exact Dioph.eq_dioph h0 hc
  have hex := Dioph.ex_dioph hT
  refine hex.ext fun v => ?_
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨x 0, x 1, hx, hp⟩
  · rintro ⟨n, m, hx, hp⟩
    exact ⟨![n, m], hx, hp⟩

/-- The graph of the `n`th prime with nine unknowns. -/
theorem nthPrime_graph_nine :
    ∃ Q : MvPolynomial (Fin 2 ⊕ Fin 9) ℤ, ∀ v : Fin 2 → ℕ,
      nthPrime (v 0) = v 1 ↔ ∃ t : Fin 9 → ℕ,
        eval (fun idx => ((Sum.elim v t idx : ℕ) : ℤ)) Q = 0 := by
  obtain ⟨M, hM⟩ := Jones1982.nine_unknowns_dioph nthPrime_codes_dioph
  let code : MvPolynomial (Fin 2 ⊕ Fin 9) ℤ :=
    (X (Sum.inl 0) + X (Sum.inl 1)) ^ 2 + 3 * X (Sum.inl 1) + X (Sum.inl 0) + 1
  let sub : Fin 10 → MvPolynomial (Fin 2 ⊕ Fin 9) ℤ :=
    Fin.cases code (fun j => X (Sum.inr j))
  refine ⟨bind₁ sub M, fun v => ?_⟩
  have hcode : pairCode (v 0) (v 1) ∈ {t | ∃ n m, t = pairCode n m ∧ nthPrime n = m} ↔
      nthPrime (v 0) = v 1 := by
    constructor
    · rintro ⟨n, m, h, hp⟩
      obtain ⟨rfl, rfl⟩ := pairCode_injective h
      exact hp
    · intro h; exact ⟨v 0, v 1, rfl, h⟩
  rw [← hcode, hM _ (by simp [pairCode])]
  apply exists_congr
  intro t
  rw [show eval (fun idx => ((Sum.elim v t idx : ℕ) : ℤ)) (bind₁ sub M) =
      eval (fun k => eval (fun idx => ((Sum.elim v t idx : ℕ) : ℤ)) (sub k)) M from
    eval₂Hom_bind₁ (RingHom.id ℤ) _ sub M]
  apply Iff.of_eq
  congr 2
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [sub, code, pairCode]
  · simp [sub]

/-- **Theorem 4 with fourteen witnesses.** -/
theorem theorem_4_fourteen :
    ∃ P : MvPolynomial (Unit ⊕ Fin 14) ℤ,
      ∀ n m : ℕ, 0 < n → 0 < m →
        (nthPrime n = m ↔ ∃ w : Fin 14 → ℕ,
          MvPolynomial.eval
            (fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ)) P = (m : ℤ)) := by
  obtain ⟨Q, hQ⟩ := nthPrime_graph_nine
  obtain ⟨P, hP⟩ := Diophantine.exists_polynomial_of_graph_polynomial (f := nthPrime) Q hQ
  refine ⟨rename (Sum.map id (Fin.castLE (by norm_num : 10 ≤ 14))) P, fun n m _ hm => ?_⟩
  rw [hP n m hm]
  simp only [eval_rename]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun i => if h : i.val < 10 then w ⟨i.val, h⟩ else 0, ?_⟩
    have e : ((fun idx => ((Sum.elim (fun _ : Unit => n)
        (fun i : Fin 14 => if h : i.val < 10 then w ⟨i.val, h⟩ else 0) idx : ℕ) : ℤ)) ∘
          Sum.map id (Fin.castLE (by norm_num : 10 ≤ 14))) =
        fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ) := by
      funext idx
      cases idx with
      | inl _ => rfl
      | inr i => simp [Fin.castLE, i.isLt]
    rw [e]; exact hw
  · rintro ⟨w, hw⟩
    refine ⟨w ∘ Fin.castLE (by norm_num), ?_⟩
    have e : ((fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ)) ∘
          Sum.map id (Fin.castLE (by norm_num : 10 ≤ 14))) =
        fun idx => ((Sum.elim (fun _ : Unit => n) (w ∘ Fin.castLE (by norm_num)) idx : ℕ) : ℤ) := by
      funext idx
      cases idx <;> rfl
    rw [e] at hw; exact hw

end JSWW1976
