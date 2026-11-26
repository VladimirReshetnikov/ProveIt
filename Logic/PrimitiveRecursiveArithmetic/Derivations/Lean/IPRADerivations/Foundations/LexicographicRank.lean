import IPRADerivations.Foundations.MixedRadix
import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.Header

/-!
# Lexicographic rank and the fuel of a fixed-dimensional descent

Packet: `foundations/ipra_staged_contract_kernel_2026-11-15`, `paper/sections/08_resources_lists.tex`:

* Lemma "Lexicographic rank": "If `b` is strictly lexicographically smaller than `a`, with both vectors inside
  the caps, then `rank(b) < rank(a)`", where `rank` is the mixed-radix packing;
* Corollary "Fuel from fixed-dimensional descent": "A run that strictly decreases the capped lexicographic
  tuple has length at most `1 + rank(a⁰) ≤ ∏_{i<r}(M_i + 1)`".

The rank is the code `Cd r d m = ∑_{i<m} d_i ∏_{j<i} r_j` of `Foundations/MixedRadix`, with the least
significant digit at index `0` (the paper's most significant coordinate is the index `m − 1` here, and the
radices are the caps `r_j = M_j + 1`). The coordinate of first difference, read from the top, is `i`: the
digits agree at `i + 1 + s` for `s < t`, and the code has length `i + 1 + t`.

* `tail_congr`: digits that agree above `i` give equal suffix codes `Tl i t`;
* `prefix_lt`: if the digits of `e` below `i` are inside the caps and `e_i < d_i`, then
  `Cd e (i + 1) < Cd d (i + 1)` (the prefix of `e` is below the place value `Pl i`, so
  `Cd e (i + 1) < (e_i + 1) Pl i ≤ d_i Pl i`);
* `lex_rank` ("Lexicographic rank"): under the same hypotheses and agreement above `i`,
  `Cd e (i + 1 + t) < Cd d (i + 1 + t)`; only the lower digits of the smaller vector need the caps;
* `descent_fuel`: for any rank `ρ(k)` along a run with `ρ(k + 1) < ρ(k)` for `k < N`,
  `ρ(N) + N ≤ ρ(0)`;
* `fuel_bound` ("Fuel from fixed-dimensional descent"): the run length `N + 1` is at most `1 + ρ(0)`, and at
  most `R` when `ρ(0) < R`; for the mixed-radix rank `R = Pl m`, the bound `ρ(0) < Pl m` is `code_lt`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.LexicographicRank

open_ipra
open LeanProofs.IPRA.Foundations.MixedRadix

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Digits that agree at `i + s` for `s < t` give equal suffix codes. -/
theorem tail_congr (r d e : PTm 2) (i t x : PTm n)
    (hag : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift t) ⟶
      (inst2 e (Syn.shift i + var 0) (Syn.shift x) ≐ inst2 d (Syn.shift i + var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Tl r e i t x ≐ Tl r d i t x := by
  refine sum_congr_bounded (eB r e) (eB r d) (pairT i x) (pairT i x) t (.allI (.impI ?_))
  rw [shift_pairT, inst2_eB, inst2_eB, inst2_offB, inst2_offB]
  have a := Prf.impE hag.allOpen.wk Prf.hyp0
  have c₁ := congrInst2 e
    (congrAdd (fst_pair (Γ := lt (var 0) (Syn.shift t) :: Γ.map Fm.shift) (Syn.shift i) (Syn.shift x))
      (.eqRefl (var 0))) (snd_pair (Syn.shift i) (Syn.shift x))
  have c₂ := congrInst2 d
    (congrAdd (fst_pair (Γ := lt (var 0) (Syn.shift t) :: Γ.map Fm.shift) (Syn.shift i) (Syn.shift x))
      (.eqRefl (var 0))) (snd_pair (Syn.shift i) (Syn.shift x))
  exact congrMul ((c₁.eqTrans a).eqTrans c₂.eqSymm) (.eqRefl _)

/-- A smaller digit at `i` over a capped prefix gives a smaller code of length `i + 1`. -/
theorem prefix_lt {r d e : PTm 2} {i x : PTm n}
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift i) ⟶
      lt (inst2 e (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x))))
    (hi : Γ ⊢[PRAAx] lt (inst2 e i x) (inst2 d i x)) :
    Γ ⊢[PRAAx] lt (Cd r e (succ i) x) (Cd r d (succ i) x) := by
  have hP : Γ ⊢[PRAAx] le (succ (Cd r e i x)) (Pl r i x) := code_lt r e x i hb
  have hi' : Γ ⊢[PRAAx] le (succ (inst2 e i x)) (inst2 d i x) := hi
  have se' := sum_succ' (Γ := Γ) (dP r e) i x
  rw [inst2_dP] at se'
  have se := natEq se'
  have sd' := sum_succ' (Γ := Γ) (dP r d) i x
  rw [inst2_dP] at sd'
  have sd := natEq sd'
  show Γ ⊢[PRAAx] le (succ (Cd r e (succ i) x)) (Cd r d (succ i) x)
  ipra_le 𝔟 (Cd r d i x) + sl hP + sl hi' * 𝔟 (Pl r i x) using rw [se, sd]; ring

/-- "Lexicographic rank": digits agreeing above `i`, a smaller digit at `i`, and a capped prefix of the
smaller vector give a smaller rank. -/
theorem lex_rank {r d e : PTm 2} {i t x : PTm n}
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift i) ⟶
      lt (inst2 e (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x))))
    (hi : Γ ⊢[PRAAx] lt (inst2 e i x) (inst2 d i x))
    (hag : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift t) ⟶
      (inst2 e (Syn.shift (succ i) + var 0) (Syn.shift x) ≐
        inst2 d (Syn.shift (succ i) + var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] lt (Cd r e (succ i + t) x) (Cd r d (succ i + t) x) := by
  have hp : Γ ⊢[PRAAx] le (succ (Cd r e (succ i) x)) (Cd r d (succ i) x) := prefix_lt hb hi
  have ce := natEq (code_split (Γ := Γ) r e (succ i) t x)
  have cd := natEq (code_split (Γ := Γ) r d (succ i) t x)
  have tl := natEq (tail_congr r d e (succ i) t x hag)
  show Γ ⊢[PRAAx] le (succ (Cd r e (succ i + t) x)) (Cd r d (succ i + t) x)
  ipra_le sl hp using rw [ce, cd, tl]; ring

/-- A rank that drops at every step of a run of length `N` drops by at least `N`. -/
theorem descent_fuel (ρ : PTm 2) (N x : PTm n)
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      lt (inst2 ρ (succ (var 0)) (Syn.shift x)) (inst2 ρ (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (inst2 ρ N x + N) (inst2 ρ zero x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (inst2 ρ (var 0) (Syn.shift x) + var 0) (inst2 ρ zero (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      exact .impI (by ipra_le 0)
    · simp only [Fm.subst_imp, subst_le, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have hk : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶
            le (inst2 ρ (var 0) (Syn.shift x) + var 0) (inst2 ρ zero (Syn.shift x))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift N) := Prf.hyp0
      have h₁ : _ ⊢[PRAAx] le (succ (inst2 ρ (succ (var 0)) (Syn.shift x))) (inst2 ρ (var 0) (Syn.shift x)) :=
        Prf.impE hd.allOpen.wk.wk hk
      have h₂ := Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      ipra_le sl h₁ + sl h₂
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-- "Fuel from fixed-dimensional descent": the run length `N + 1` is at most `1 + ρ(0)`, and at most `R`
when `ρ(0) < R`. -/
theorem fuel_bound (ρ : PTm 2) (N R x : PTm n)
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      lt (inst2 ρ (succ (var 0)) (Syn.shift x)) (inst2 ρ (var 0) (Syn.shift x))))
    (hR : Γ ⊢[PRAAx] lt (inst2 ρ zero x) R) :
    Γ ⊢[PRAAx] le (succ N) (succ (inst2 ρ zero x)) ⋏ le (succ N) R := by
  have h := descent_fuel ρ N x hd
  have hR' : Γ ⊢[PRAAx] le (succ (inst2 ρ zero x)) R := hR
  refine .andI ?_ ?_
  · ipra_le 𝔟 (inst2 ρ N x) + sl h
  · ipra_le 𝔟 (inst2 ρ N x) + sl h + sl hR'

end LeanProofs.IPRA.Foundations.LexicographicRank
