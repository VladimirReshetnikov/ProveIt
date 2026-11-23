import IPRADerivations.Topology.HairyBallEstimates

/-!
# The mesh of iterated barycentric subdivision

Packet: `topology/hairy_ball_ipra`, `sections/degree.tex`, Lemma `lem:mesh` ("Mesh in the `ℓ¹` metric"): "For
`n ≥ 1` the diameter of every simplex after `r = ns` barycentric subdivisions is at most `2^{1-s}`." As iPRA
derivations (coordinates as integer terms, norms and diameters as natural terms cleared of denominators):

* `mul_cancel_le`, `num_pos`: cancellation of a positive factor;
* `bary_identity`: "For nonempty `B ⊋ D`, `b_B = (|D|/|B|) b_D + ((|B| − |D|)/|B|) b_{B∖D}`", cleared:
  `|B| (b_B − b_D) = (|B| − |D|)(b_{B∖D} − b_D)` (one coordinate);
* `bary_contract`: "The distance of these barycentres `b_B, b_D` is at most `n/(n+1)` times the diameter of the
  parent simplex": from `|B| d ≤ C δ` with `C = |B| − |D| ≤ |B| − 1` and `|B| ≤ n + 1`,
  `(n + 1) d ≤ n δ`;
* `mesh_pow`: `j` subdivisions give `(n + 1)^j δ_j ≤ n^j δ_0`;
* `mesh_halving`: "Bernoulli's inequality gives `(1 + 1/n)^n ≥ 2`. After `r = ns` subdivisions the diameter is
  at most `2^{1-s}`": `2^s δ_{ns} ≤ δ_0`.
-/

namespace LeanProofs.IPRA.Topology.BarycentricMesh

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Topology.HairyBallEstimates (bernoulli)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- A positive factor cancels: `c ≥ 1` and `c x ≤ c y` give `x ≤ y`. -/
theorem mul_cancel_le {c x y : PTm n} (hc : Γ ⊢[PRAAx] le (succ zero) c) (h : Γ ⊢[PRAAx] le (c * x) (c * y)) :
    Γ ⊢[PRAAx] le x y := by
  refine .orE (lt_or_le y x) ?_ Prf.hyp0
  have hlt : (lt y x :: Γ) ⊢[PRAAx] le (succ y) x := Prf.hyp0
  have h' := h.wk (ψ := lt y x)
  have hc' := hc.wk (ψ := lt y x)
  refine not_succ_le_self (c * y) _ ?_
  ipra_le sl h' + 𝔟 c * sl hlt + sl hc'

/-- A positive numeral is at least one. -/
theorem num_pos {m : ℕ} (hm : 1 ≤ m) : Γ ⊢[PRAAx] le (succ zero) (num m : PTm n) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  ipra_le (k : Groth (Q Γ)) using push_cast; ring

/-- The barycentre identity, cleared: `|B| (b_B − b_D) = (|B| − |D|)(b_{B∖D} − b_D)`. -/
theorem bary_identity {B Dn C bB bD bC SD SC : ZT n} (hB : Γ ⊢[PRAAx] ZT.eq (B * bB) (SD + SC))
    (hD : Γ ⊢[PRAAx] ZT.eq (Dn * bD) SD) (hC : Γ ⊢[PRAAx] ZT.eq (C * bC) SC)
    (hsz : Γ ⊢[PRAAx] ZT.eq B (Dn + C)) : Γ ⊢[PRAAx] ZT.eq (B * (bB - bD)) (C * (bC - bD)) := by
  have eB := ZT.toZ_eq hB
  have eD := ZT.toZ_eq hD
  have eC := ZT.toZ_eq hC
  have es := ZT.toZ_eq hsz
  simp only [ZT.toZ_mul, ZT.toZ_add] at eB eD eC es
  apply ZT.derive
  zsimp
  linear_combination eB - ZT.toZ Γ bD * es - eD - eC

/-- The contraction factor `n/(n+1)`: `|B| d ≤ C δ`, `C + 1 ≤ |B|` and `|B| ≤ N + 1` give
`(N + 1) d ≤ N δ`. -/
theorem bary_contract (N : ℕ) {B C d δ : PTm n} (hnorm : Γ ⊢[PRAAx] le (B * d) (C * δ))
    (hC : Γ ⊢[PRAAx] le (succ C) B) (hB : Γ ⊢[PRAAx] le B (num (N + 1))) :
    Γ ⊢[PRAAx] le (num (N + 1) * d) (num N * δ) := by
  have hpos : Γ ⊢[PRAAx] le (succ zero) B := by
    ipra_le sl hC + 𝔟 C
  refine mul_cancel_le hpos ?_
  ipra_le ((N + 1 : ℕ) : Groth (Q Γ)) * sl hnorm + ((N + 1 : ℕ) : Groth (Q Γ)) * sl hC * 𝔟 δ +
    sl hB * 𝔟 δ using push_cast; ring

/-- `j` subdivisions: `(N + 1)^j δ_j ≤ N^j δ_0`. -/
theorem mesh_pow (δ : ℕ → PTm n) (N : ℕ)
    (hstep : ∀ j, Γ ⊢[PRAAx] le (num (N + 1) * δ (j + 1)) (num N * δ j)) (j : ℕ) :
    Γ ⊢[PRAAx] le (num ((N + 1) ^ j) * δ j) (num (N ^ j) * δ 0) := by
  induction j with
  | zero => ipra_le 0 using push_cast; ring
  | succ j ih =>
    have hj := hstep j
    ipra_le ((N + 1 : ℕ) : Groth (Q Γ)) ^ j * sl hj + (N : Groth (Q Γ)) * sl ih using push_cast; ring

/-- `lem:mesh`: after `N s` subdivisions the diameter has been halved `s` times, `2^s δ_{Ns} ≤ δ_0`. -/
theorem mesh_halving (δ : ℕ → PTm n) {N : ℕ} (hN : 1 ≤ N) (s : ℕ)
    (hstep : ∀ j, Γ ⊢[PRAAx] le (num (N + 1) * δ (j + 1)) (num N * δ j)) :
    Γ ⊢[PRAAx] le (num (2 ^ s) * δ (N * s)) (δ 0) := by
  have hp := mesh_pow δ N hstep (N * s)
  have hb : 2 ^ s * N ^ (N * s) ≤ (N + 1) ^ (N * s) := by
    have h := Nat.pow_le_pow_left (bernoulli hN) s
    rw [Nat.mul_pow, ← pow_mul, ← pow_mul] at h
    exact h
  obtain ⟨c, hc⟩ : ∃ c, (N + 1) ^ (N * s) = 2 ^ s * N ^ (N * s) + c := ⟨_, (Nat.add_sub_cancel' hb).symm⟩
  rw [hc] at hp
  refine mul_cancel_le (num_pos (Nat.one_le_pow _ _ hN)) (c := num (N ^ (N * s))) ?_
  ipra_le sl hp + (c : Groth (Q Γ)) * 𝔟 (δ (N * s)) using push_cast; ring

end LeanProofs.IPRA.Topology.BarycentricMesh
