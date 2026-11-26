import IPRADerivations.DiophantineNumberTheory.KhinchinBlockLocal
import IPRADerivations.Core.Header

/-!
# The block's union bit vanishes outside its cell, uniformly (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "All added intervals are inside the gap in
which they were constructed."

`KhinchinBlockLocal.block_out` shows that the union bit of a (K11) block vanishes at one cell `c` outside the gap
`[L, H)`. `Foundations.SumLocal.sum_local` (and `KhinchinCellCount.count_local`) needs this uniformly, as closed
bounded universals over the cells:

* `union_vanish_lo`: the union bit vanishes at every cell `c < L`;
* `union_vanish_hi`: the union bit vanishes at every cell `H + j`.

Both instantiate `block_out` under the cell binder, with its margin hypotheses transported one binder deeper.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinUnionVanish

open_ipra
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales (Xt bB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockLocal (block_out)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The margin hypothesis of `block_out`, one binder deeper. -/
theorem hH_shift (wb : PTm 2) {B K0 M R G α γ b0 H : PTm n}
    (hH : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      le (fact (Syn.shift R) * Syn.shift G * Syn.shift γ +
          inst2 wb (var 0) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ)
            (Syn.shift b0)) * succ (Syn.shift b0))
        (Syn.shift H * succ (Syn.shift b0)))) :
    Γ.map Fm.shift ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift B)) ⟶
      le (fact (Syn.shift (Syn.shift R)) * Syn.shift (Syn.shift G) * Syn.shift (Syn.shift γ) +
          inst2 wb (var 0) (Xt (Syn.shift (Syn.shift K0)) (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift R))
            (Syn.shift (Syn.shift G)) (Syn.shift (Syn.shift α)) (Syn.shift (Syn.shift γ)) (Syn.shift (Syn.shift b0))) *
            succ (Syn.shift (Syn.shift b0)))
        (Syn.shift (Syn.shift H) * succ (Syn.shift (Syn.shift b0)))) := by
  simpa [Fm.shift, Syn.shift, Syn.subst_subst, Xt] using hH.shift

/-- The union bit vanishes at every cell `c < L`. -/
theorem union_vanish_lo (wb : PTm 2) {B K0 M R G α γ b0 L H : PTm n}
    (hL : Γ ⊢[PRAAx] le (L * succ b0) (fact R * G * α))
    (hH : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      le (fact (Syn.shift R) * Syn.shift G * Syn.shift γ +
          inst2 wb (var 0) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ)
            (Syn.shift b0)) * succ (Syn.shift b0))
        (Syn.shift H * succ (Syn.shift b0)))) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L) ⟶
      inst2 (sg (oB (bB wb))) (var 0) (Syn.shift (pairT B (Xt K0 M R G α γ b0))) ≐ zero) := by
  refine .allI (.impI ?_)
  have hL0 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift L * succ (Syn.shift b0))
      (fact (Syn.shift R) * Syn.shift G * Syn.shift α) := by
    simpa [Fm.shift, Syn.shift] using hL.shift
  have z := block_out wb (c := var 0) hL0.wk (hH_shift wb hH).wk (.orI₁ Prf.hyp0)
  rw [show Syn.shift (pairT B (Xt K0 M R G α γ b0)) = pairT (Syn.shift B)
      (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ) (Syn.shift b0)) by
        simp [Syn.shift, Xt],
    show ∀ (c y : PTm (n + 1)), inst2 (sg (oB (bB wb))) c y = sg (inst2 (oB (bB wb)) c y) from fun c y => by
      simp [inst2, Signum.sg]]
  exact z

/-- The union bit vanishes at every cell `H + j`. -/
theorem union_vanish_hi (wb : PTm 2) {B K0 M R G α γ b0 L H N : PTm n}
    (hL : Γ ⊢[PRAAx] le (L * succ b0) (fact R * G * α))
    (hH : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      le (fact (Syn.shift R) * Syn.shift G * Syn.shift γ +
          inst2 wb (var 0) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ)
            (Syn.shift b0)) * succ (Syn.shift b0))
        (Syn.shift H * succ (Syn.shift b0)))) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      inst2 (sg (oB (bB wb))) (Syn.shift H + var 0) (Syn.shift (pairT B (Xt K0 M R G α γ b0))) ≐ zero) := by
  refine .allI (.impI ?_)
  have hL0 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift L * succ (Syn.shift b0))
      (fact (Syn.shift R) * Syn.shift G * Syn.shift α) := by
    simpa [Fm.shift, Syn.shift] using hL.shift
  have hc : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (Syn.shift H + var 0) (Syn.shift L) ⋎ le (Syn.shift H) (Syn.shift H + var 0) :=
    .orI₂ (by ipra_le 𝔞 (var 0))
  have z := block_out wb (c := Syn.shift H + var 0) hL0.wk (hH_shift wb hH).wk hc
  rw [show Syn.shift (pairT B (Xt K0 M R G α γ b0)) = pairT (Syn.shift B)
      (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ) (Syn.shift b0)) by
        simp [Syn.shift, Xt],
    show ∀ (c y : PTm (n + 1)), inst2 (sg (oB (bB wb))) c y = sg (inst2 (oB (bB wb)) c y) from fun c y => by
      simp [inst2, Signum.sg]]
  exact z

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinUnionVanish
