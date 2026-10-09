import GowersSzemeredi.Proofs16ClaimNineFourSelection
import GowersSzemeredi.Proofs16CommonValue
import GowersSzemeredi.Proofs16CommonValueFreiman
import GowersSzemeredi.Proofs16SpanBallSplit

/-! Milićević's Claim 9.4 in `ℤ/N` (arXiv:2601.01682, printed p. 66),
from prescribed escaping decompositions to a new Freiman homomorphism.

Prescribe, for `εN³` triples `(x, y, a)`, a decomposition
`ξ₀ − ξ₁ = ξ₂ − ξ₃` with `ξ₀ ∈ ⟨Γ_{x+a}⟩_R`, `ξ₁ ∈ ⟨Γ_x⟩_R`,
`ξ₂ ∈ ⟨Γ_{y+a}⟩_R` and `ξ₃ ∈ ⟨Γ_y⟩_R`, whose frequency `ξ₀ − ξ₁` avoids a
forbidden set `S(x, a)`. In the iteration of Proposition 9.3, `S(x, a)` is
the `{-1,0,1}`-span of the current `θ_i(a)` for `i ∈ I_{x+a,x}`, and
`escape_split` produces the decomposition.
1. `claim_9_4_selection`: four maps `ψ_i` realize the decomposition on a
   `K^(−4)` fraction, with `K = (2R+1)^d`.
2. On those triples `ψ₀(x+a) − ψ₁(x) = ψ₂(y+a) − ψ₃(y)` depends only on
   `(x, a)` and only on `(a, y)`. `exists_common_value` gives `Θ` with
   `Θ(a) = ψ₀(x+a) − ψ₁(x)` on `(ε/K⁴)²N²` pairs `(x, a)`.
3. `freiman_common_value`: `Θ` is a Freiman 8-homomorphism on a set `B`,
   with `claimNineFourDensity ε R d · N²` of those pairs over `B`.

For each such pair, `Θ(a) ∈ ⟨Γ_{x+a} ∪ Γ_x⟩_{2R}` and `Θ(a) ∉ S(x, a)`.
This is the new frequency map that raises `|I_{x+a,x}|`. Milićević's
version takes `Θ(a)` minus a constant; here no constant appears, since
`Θ` is read off the selected values directly. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A difference of two span-ball elements lies in the span ball of the union, at
twice the radius. -/
theorem sub_mem_spanBall_union {G : Type*} [AddCommGroup G] [DecidableEq G]
    {Γ₁ Γ₂ : Finset G} {R : Nat} {α β : G}
    (hα : α ∈ spanBall Γ₁ R) (hβ : β ∈ spanBall Γ₂ R) :
    α - β ∈ spanBall (Γ₁ ∪ Γ₂) (2 * R) := by
  obtain ⟨n₁, hn₁, rfl⟩ := (mem_spanBall_iff _ R _).mp hα
  obtain ⟨n₂, hn₂, rfl⟩ := (mem_spanBall_iff _ R _).mp hβ
  refine (mem_spanBall_iff _ (2 * R) _).mpr
    ⟨fun γ => (if γ ∈ Γ₁ then n₁ γ else 0) - (if γ ∈ Γ₂ then n₂ γ else 0), ?_, ?_⟩
  · intro γ _
    show -((2 * R : Nat) : Int) ≤ (if γ ∈ Γ₁ then n₁ γ else 0) - (if γ ∈ Γ₂ then n₂ γ else 0) ∧
      (if γ ∈ Γ₁ then n₁ γ else 0) - (if γ ∈ Γ₂ then n₂ γ else 0) ≤ ((2 * R : Nat) : Int)
    have h1 : -(R : Int) ≤ (if γ ∈ Γ₁ then n₁ γ else 0) ∧ (if γ ∈ Γ₁ then n₁ γ else 0) ≤ R := by
      split_ifs with h
      · exact hn₁ γ h
      · constructor <;> omega
    have h2 : -(R : Int) ≤ (if γ ∈ Γ₂ then n₂ γ else 0) ∧ (if γ ∈ Γ₂ then n₂ γ else 0) ≤ R := by
      split_ifs with h
      · exact hn₂ γ h
      · constructor <;> omega
    push_cast
    constructor <;> omega
  · have e : ∀ (Γ : Finset G) (n : G → Int), Γ ⊆ Γ₁ ∪ Γ₂ →
        ∑ γ ∈ Γ₁ ∪ Γ₂, (if γ ∈ Γ then n γ else 0) • γ = ∑ γ ∈ Γ, n γ • γ := by
      intro Γ n hsub
      simp_rw [ite_smul, zero_smul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    rw [← e Γ₁ n₁ Finset.subset_union_left, ← e Γ₂ n₂ Finset.subset_union_right,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [sub_smul]

/-- The pair density of Claim 9.4: `κ(c/2)²` with `c = (ε/K⁴)²`,
`K = (2R+1)^d` and `κ = 2^(−1882)·((c/2)^4)^1164`. -/
def claimNineFourDensity (ε : Real) (R d : Nat) : Real :=
  let c := (ε / (((2 * R + 1) ^ d : Nat) : Real) ^ 4) ^ 2
  (2 : Real) ^ (-(1882 : Real)) * ((c / 2) ^ 4) ^ 1164 * (c / 2) ^ 2

/-- **Claim 9.4.** -/
theorem claim_9_4 {N : Nat} [NeZero N] [Fact N.Prime] (Γ : ZMod N → Finset (ZMod N))
    {d R : Nat} (hΓ : ∀ z, (Γ z).card ≤ d) (Tr : Finset (ZMod N × ZMod N × ZMod N))
    (ξ : ZMod N × ZMod N × ZMod N → Fin 4 → ZMod N)
    (hξ : ∀ t ∈ Tr, ξ t 0 ∈ spanBall (Γ (t.1 + t.2.2)) R ∧ ξ t 1 ∈ spanBall (Γ t.1) R ∧
      ξ t 2 ∈ spanBall (Γ (t.2.1 + t.2.2)) R ∧ ξ t 3 ∈ spanBall (Γ t.2.1) R)
    (hdec : ∀ t ∈ Tr, ξ t 0 - ξ t 1 = ξ t 2 - ξ t 3)
    (S : ZMod N → ZMod N → Finset (ZMod N)) (hS : ∀ t ∈ Tr, ξ t 0 - ξ t 1 ∉ S t.1 t.2.2)
    {ε : Real} (hε : 0 < ε) (hTr : ε * (N : Real) ^ 3 ≤ Tr.card) :
    ∃ (Θ : ZMod N → ZMod N) (B : Finset (ZMod N)) (P : Finset (ZMod N × ZMod N)),
      FreimanHom 8 B Θ ∧ claimNineFourDensity ε R d * (N : Real) ^ 2 ≤ P.card ∧
      ∀ p ∈ P, p.2 ∈ B ∧ Θ p.2 ∈ spanBall (Γ (p.1 + p.2) ∪ Γ p.1) (2 * R) ∧
        Θ p.2 ∉ S p.1 p.2 := by
  obtain ⟨ψ, hψ, hcount⟩ := claim_9_4_selection Γ hΓ Tr ξ hξ
  set K := (2 * R + 1) ^ d with hKdef
  have hKpos : 0 < K := Nat.pos_of_ne_zero (by positivity)
  have hN : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  let E := Tr.filter fun t => ψ 0 (t.1 + t.2.2) = ξ t 0 ∧ ψ 1 t.1 = ξ t 1 ∧
    ψ 2 (t.2.1 + t.2.2) = ξ t 2 ∧ ψ 3 t.2.1 = ξ t 3
  have hK4 : (0 : Real) < (K : Real) ^ 4 := by positivity
  have hEcard : ε / (K : Real) ^ 4 * (N : Real) ^ 3 ≤ E.card := by
    have h : (Tr.card : Real) ≤ (K : Real) ^ 4 * E.card := by exact_mod_cast hcount
    rw [div_mul_eq_mul_div, div_le_iff₀ hK4]
    nlinarith
  -- reindex as `(x, a, y)`
  let T := E.image fun t => (t.1, t.2.2, t.2.1)
  have hTcard : T.card = E.card := by
    apply Finset.card_image_of_injOn
    intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)
  have hTmem : ∀ u ∈ T, ∃ t ∈ E, u = (t.1, t.2.2, t.2.1) := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨t, ht, rfl⟩
  let F : ZMod N → ZMod N → ZMod N := fun x a => ψ 0 (x + a) - ψ 1 x
  let H : ZMod N → ZMod N → ZMod N := fun a y => ψ 2 (y + a) - ψ 3 y
  have hFval : ∀ u ∈ T, ∃ t ∈ Tr, u.1 = t.1 ∧ u.2.1 = t.2.2 ∧ F u.1 u.2.1 = ξ t 0 - ξ t 1 ∧
      H u.2.1 u.2.2 = ξ t 2 - ξ t 3 := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := hTmem u hu
    obtain ⟨htT, e0, e1, e2, e3⟩ := Finset.mem_filter.mp ht
    refine ⟨t, htT, rfl, rfl, ?_, ?_⟩
    · show ψ 0 (t.1 + t.2.2) - ψ 1 t.1 = _
      rw [e0, e1]
    · show ψ 2 (t.2.1 + t.2.2) - ψ 3 t.2.1 = _
      rw [e2, e3]
  have hT : ∀ u ∈ T, F u.1 u.2.1 = H u.2.1 u.2.2 := by
    intro u hu
    obtain ⟨t, htT, -, -, hF, hH⟩ := hFval u hu
    rw [hF, hH, hdec t htT]
  obtain ⟨Θ, hΘ⟩ := exists_common_value T F H hT
  simp only [ZMod.card] at hΘ
  let TΘ := T.filter fun u => F u.1 u.2.1 = Θ u.2.1
  let P := TΘ.image fun u => (u.1, u.2.1)
  -- each pair carries at most `N` triples
  have hTΘP : (TΘ.card : Real) ≤ N * P.card := by
    have h := Finset.card_le_mul_card_image (f := fun u : ZMod N × ZMod N × ZMod N => (u.1, u.2.1))
      TΘ N (by
        intro p _
        have : (TΘ.filter fun u => (u.1, u.2.1) = p).card ≤
            (Finset.univ : Finset (ZMod N)).card := by
          refine Finset.card_le_card_of_injOn (fun u => u.2.2) (fun _ _ => by simp) ?_
          intro u hu u' hu' h
          have h1 := (Finset.mem_filter.mp hu).2
          have h2 := (Finset.mem_filter.mp hu').2
          rw [← h2] at h1
          simp only [Prod.mk.injEq] at h1
          exact Prod.ext h1.1 (Prod.ext h1.2 h)
        rwa [Finset.card_univ, ZMod.card] at this)
    exact_mod_cast h
  set c : Real := (ε / (K : Real) ^ 4) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hPc : c * (N : Real) ^ 2 ≤ P.card := by
    have hNN : ((N + N : Nat) : Real) / 2 = N := by push_cast; ring
    rw [hNN] at hΘ
    have h1 : (ε / (K : Real) ^ 4 * (N : Real) ^ 3) ^ 2 ≤ (T.card : Real) ^ 2 := by
      rw [hTcard]
      exact pow_le_pow_left₀ (by positivity) hEcard 2
    have h2 : (T.card : Real) ^ 2 ≤ (N : Real) * (N : Real) ^ 2 * (N * P.card) := by
      calc (T.card : Real) ^ 2 ≤ (N : Real) * (N : Real) ^ 2 * TΘ.card := hΘ
        _ ≤ (N : Real) * (N : Real) ^ 2 * (N * P.card) :=
            mul_le_mul_of_nonneg_left hTΘP (by positivity)
    have h3 : c * (N : Real) ^ 2 * (N : Real) ^ 4 ≤ (P.card : Real) * (N : Real) ^ 4 := by
      calc c * (N : Real) ^ 2 * (N : Real) ^ 4 = (ε / (K : Real) ^ 4 * (N : Real) ^ 3) ^ 2 := by
            rw [hc]; ring
        _ ≤ (N : Real) * (N : Real) ^ 2 * (N * P.card) := h1.trans h2
        _ = (P.card : Real) * (N : Real) ^ 4 := by ring
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hP : ∀ p ∈ P, Θ p.2 = ψ 0 (p.1 + p.2) - ψ 1 p.1 := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hu).2.symm
  obtain ⟨B, hF, hcnt⟩ := freiman_common_value Θ (ψ 0) (ψ 1) P hP hc0 hPc
  refine ⟨Θ, B, P.filter fun p => p.2 ∈ B, hF, ?_, ?_⟩
  · exact hcnt
  · intro p hp
    obtain ⟨hpP, hpB⟩ := Finset.mem_filter.mp hp
    refine ⟨hpB, ?_, ?_⟩
    · rw [hP p hpP]
      exact sub_mem_spanBall_union (hψ 0 _) (hψ 1 _)
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hpP
      have huF := (Finset.mem_filter.mp hu).2
      obtain ⟨t, htT, h1, h2, hFt, -⟩ := hFval u (Finset.mem_filter.mp hu).1
      simp only
      rw [← huF, hFt, h1, h2]
      exact hS t htT

end LeanProofs.GowersSzemeredi
