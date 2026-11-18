import IPRADerivations.Core.Search
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.OrderCertificates

/-!
# Disjoint sums of code spaces

Packet: `foundations/STRIVE-iPRA-framework-2026-11-16`, `paper/sections/04_mixed_radix.tex`, Section
"Disjoint sums for one selected child" and the lemma "Disjoint decoding".

For child code spaces of sizes `B_i = B(i, x)` (zero sizes allowed) and prefix sums `S_k = ∑_{i<k} B_i`, a
pair `(i, c)` with `i < N`, `c < B_i` is encoded as `S_i + c < S_N`. The owner of a code `z` is the least
`j < N` with `z < S_{j+1}`, computed by the bounded least search of `Core/Search`:
`owner N z x = μ j < N. (z + 1) ∸ S_{j+1} = 0`.

* `prefix_mono`: `a ≤ b` gives `S_a ≤ S_b`;
* `code_lt`: `i < N` and `c < B_i` give `S_i + c < S_N`;
* `owner_eq`, `local_eq` ("Disjoint decoding"): for `i < N` and `c < B_i`, the owner of `S_i + c` is `i`
  and the local code `(S_i + c) ∸ S_owner` is `c`;
* `owner_found`, `owner_le`, `local_lt`, `reconstruct` (the converse stated before the lemma): for
  `z < S_N`, the owner `o` satisfies `o < N`, `S_o ≤ z < S_{o+1}`, the local code `z ∸ S_o` is below `B_o`,
  and `z = S_o + (z ∸ S_o)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.DisjointSums

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Search (mu search_minimal search_found)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The prefix sum `S_k = ∑_{i<k} B_i`. -/
abbrev Sp (B : PTm 2) (k x : PTm n) : PTm n := ap2 (sumF B) k x

/-- The ownership test over `0 = j`, `1 = ⟨z, x⟩`: zero exactly when `z < S_{j+1}`. -/
abbrev ownB (B : PTm 2) : PTm 2 := monus (succ (fstT (var 1))) (ap2 (sumF B) (succ (var 0)) (sndT (var 1)))

theorem inst2_ownB (B : PTm 2) (j y : PTm n) :
    inst2 (ownB B) j y = monus (succ (fstT y)) (ap2 (sumF B) (succ j) (sndT y)) := by
  simp [inst2]

/-- The owner of the code `z`: the least `j < N` with `z < S_{j+1}`. -/
abbrev owner (B : PTm 2) (N z x : PTm n) : PTm n := mu (ownB B) N (pairT z x)

theorem own_of_lt {B : PTm 2} {j z x : PTm n} (h : Γ ⊢[PRAAx] lt z (Sp B (succ j) x)) :
    Γ ⊢[PRAAx] inst2 (ownB B) j (pairT z x) ≐ zero := by
  rw [inst2_ownB]
  exact lt_congr (fst_pair z x).eqSymm (congrAp2 (sumF B) (.eqRefl _) (snd_pair z x)).eqSymm h

theorem lt_of_own {B : PTm 2} {j z x : PTm n} (h : Γ ⊢[PRAAx] inst2 (ownB B) j (pairT z x) ≐ zero) :
    Γ ⊢[PRAAx] lt z (Sp B (succ j) x) := by
  rw [inst2_ownB] at h
  exact lt_congr (fst_pair z x) (congrAp2 (sumF B) (.eqRefl _) (snd_pair z x)) h

/-! ## Prefix sums and the encoding -/

/-- The prefix sums are monotone. -/
theorem prefix_mono (B : PTm 2) {a b : PTm n} (x : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (Sp B a x) (Sp B b x) := by
  have s := natEq ((congrAp2 (sumF B) (eq_add_of_le h) (.eqRefl x)).eqTrans (sum_split B a (monus b a) x))
  ipra_le 𝔟 (ap2 (sumF (offB B)) (monus b a) (pairT a x)) with s

theorem code_lt_next (B : PTm 2) {i c x : PTm n} (hc : Γ ⊢[PRAAx] lt c (inst2 B i x)) :
    Γ ⊢[PRAAx] lt (Sp B i x + c) (Sp B (succ i) x) := by
  have e := natEq (sum_succ' (Γ := Γ) B i x)
  have hc' : Γ ⊢[PRAAx] le (succ c) (inst2 B i x) := hc
  show Γ ⊢[PRAAx] le (succ (Sp B i x + c)) (Sp B (succ i) x)
  ipra_le sl hc' using rw [e]; ring

/-- The code of `(i, c)` with `i < N`, `c < B_i` is below the bound `S_N` of the disjoint union. -/
theorem code_lt (B : PTm 2) {i c x N : PTm n} (hi : Γ ⊢[PRAAx] lt i N)
    (hc : Γ ⊢[PRAAx] lt c (inst2 B i x)) : Γ ⊢[PRAAx] lt (Sp B i x + c) (Sp B N x) :=
  lt_of_lt_of_le (code_lt_next B hc) (prefix_mono B x hi)

/-! ## Disjoint decoding -/

/-- No earlier interval contains the code `S_i + c`. -/
theorem no_earlier (B : PTm 2) {i c x o : PTm n} (ho : Γ ⊢[PRAAx] lt o i)
    (hz : Γ ⊢[PRAAx] lt (Sp B i x + c) (Sp B (succ o) x)) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ :=
  le_lt_absurd φ (le_trans (prefix_mono B x ho) (le_add_right _ _)) hz

/-- "Disjoint decoding": the least owner of `S_i + c` is `i`. -/
theorem owner_eq (B : PTm 2) {i c x N : PTm n} (hi : Γ ⊢[PRAAx] lt i N)
    (hc : Γ ⊢[PRAAx] lt c (inst2 B i x)) : Γ ⊢[PRAAx] owner B N (Sp B i x + c) x ≐ i := by
  have sf := search_found (own_of_lt (code_lt_next B hc)) hi
  have hz := lt_of_own (Prf.andE₁ (Prf.andE₂ sf))
  refine le_antisymm (Prf.andE₂ (Prf.andE₂ sf)) ?_
  exact .orE (lt_or_le (owner B N (Sp B i x + c) x) i) (no_earlier B Prf.hyp0 hz.wk _) Prf.hyp0

/-- "Disjoint decoding": the local code of `S_i + c` is `c`. -/
theorem local_eq (B : PTm 2) {i c x N : PTm n} (hi : Γ ⊢[PRAAx] lt i N)
    (hc : Γ ⊢[PRAAx] lt c (inst2 B i x)) :
    Γ ⊢[PRAAx] monus (Sp B i x + c) (Sp B (owner B N (Sp B i x + c) x) x) ≐ c :=
  (congrMonus (.eqRefl _) (congrAp2 (sumF B) (owner_eq B hi hc) (.eqRefl x))).eqTrans
    (add_monus' c (Sp B i x))

/-! ## Every code below the bound has an owner -/

section Converse

variable {B : PTm 2} {z x N : PTm n}

local notation "𝔬" => owner B N z x

/-- For `z < S_N`: the owner is below `N` and `z < S_{o+1}`. -/
theorem owner_found (hx : Γ ⊢[PRAAx] lt z (Sp B N x)) :
    Γ ⊢[PRAAx] lt 𝔬 N ⋏ lt z (Sp B (succ 𝔬) x) := by
  refine .orE (zero_or_succ N) ?_ ?_
  · have h0 : ((N ≐ zero) :: Γ) ⊢[PRAAx] N ≐ zero := Prf.hyp0
    exact le_lt_absurd _ (zero_le z)
      (lt_congr (.eqRefl _) ((congrAp2 (sumF B) h0 (.eqRefl x)).eqTrans (sum_zero B x)) hx.wk)
  · have h0 : ((N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp0
    have hi : ((N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] lt (pred N) N :=
      le_congr (.eqRefl _) h0.eqSymm (le_refl _)
    have sf := search_found (own_of_lt (lt_congr (.eqRefl z) (congrAp2 (sumF B) h0 (.eqRefl x)) hx.wk)) hi
    exact .andI (Prf.andE₁ sf) (lt_of_own (Prf.andE₁ (Prf.andE₂ sf)))

/-- Minimality of the owner: `S_o ≤ z`. -/
theorem owner_le : Γ ⊢[PRAAx] le (Sp B 𝔬 x) z := by
  refine .orE (lt_or_le z (Sp B 𝔬 x)) ?_ Prf.hyp0
  refine .orE (zero_or_succ 𝔬) ?_ ?_
  · have h0 : ((𝔬 ≐ zero) :: lt z (Sp B 𝔬 x) :: Γ) ⊢[PRAAx] 𝔬 ≐ zero := Prf.hyp0
    have h1 : ((𝔬 ≐ zero) :: lt z (Sp B 𝔬 x) :: Γ) ⊢[PRAAx] lt z (Sp B 𝔬 x) := Prf.hyp1
    exact le_lt_absurd _ (zero_le z)
      (lt_congr (.eqRefl _) ((congrAp2 (sumF B) h0 (.eqRefl x)).eqTrans (sum_zero B x)) h1)
  · have h0 : ((𝔬 ≐ succ (pred 𝔬)) :: lt z (Sp B 𝔬 x) :: Γ) ⊢[PRAAx] 𝔬 ≐ succ (pred 𝔬) := Prf.hyp0
    have h1 : ((𝔬 ≐ succ (pred 𝔬)) :: lt z (Sp B 𝔬 x) :: Γ) ⊢[PRAAx] lt z (Sp B 𝔬 x) := Prf.hyp1
    have hp : ((𝔬 ≐ succ (pred 𝔬)) :: lt z (Sp B 𝔬 x) :: Γ) ⊢[PRAAx] lt (pred 𝔬) 𝔬 :=
      le_congr (.eqRefl _) h0.eqSymm (le_refl _)
    exact .botE _ (.impE (search_minimal hp)
      (own_of_lt (lt_congr (.eqRefl _) (congrAp2 (sumF B) h0 (.eqRefl x)) h1)))

/-- For `z < S_N`, the local code `z ∸ S_o` is below the size `B_o` of the owner's code space. -/
theorem local_lt (hx : Γ ⊢[PRAAx] lt z (Sp B N x)) :
    Γ ⊢[PRAAx] lt (monus z (Sp B 𝔬 x)) (inst2 B 𝔬 x) := by
  have hu : Γ ⊢[PRAAx] le (succ z) (Sp B (succ 𝔬) x) := Prf.andE₂ (owner_found hx)
  have e := natEq (eq_add_of_le (owner_le (Γ := Γ) (B := B) (z := z) (x := x) (N := N)))
  have es := natEq (sum_succ' (Γ := Γ) B 𝔬 x)
  show Γ ⊢[PRAAx] le (succ (monus z (Sp B 𝔬 x))) (inst2 B 𝔬 x)
  ipra_le sl hu using rw [es]; linear_combination e

/-- A code is the prefix sum of its owner plus its local code. -/
theorem reconstruct : Γ ⊢[PRAAx] z ≐ Sp B 𝔬 x + monus z (Sp B 𝔬 x) :=
  eq_add_of_le owner_le

end Converse

end LeanProofs.IPRA.Foundations.DisjointSums
