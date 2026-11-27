import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.OrderCertificates

/-!
# The Boolean table of a finite query trace

Packet: `foundations/ipra_unified_finitary_framework_2026-11-15`, `paper/sections/05_trace_compiler.tex`:

* Lemma `lem:finite-query` ("Finite instantiation"): iPRA proves `H_a(p) → GoodTable(p, n, c) = 1` for the
  actual finite query table, provided each table field is a consequence of `H_a(p)`; "induct over the finite
  query trace with a Boolean equation saying that all entries are good";
* Corollary `cor:fix-precision` ("Fix precision, then quantify"): from a derivation of
  `Out(p, n, A(p, n))` for a free precision `n` under the global hypotheses, iPRA proves
  `H(p) → ∀ n Out(p, n, A(p, n))`, and no induction formula contains `∀ n`.

With the table fields as bits `g(i, x) ∈ {0, 1}`, `i < L`, and `GoodTable = ∏_{i<L} g(i)`:

* `table_good`: if every field is good (`g(i) = 1` for `i < L`), then `GoodTable = 1` (the product
  induction of `Core/ProdLemmas`, with the hypothesis available under its binder);
* `table_entry`: conversely, for bits, `GoodTable = 1` gives `g(i) = 1` for each `i < L` (a zero field would
  make the product zero, `prod_zero_of`);
* `fix_precision`: a derivation of `Out(n)` for the bound variable `n` from the shifted context and the
  shifted hypothesis gives `H → ∀ n Out(n)`: universal introduction after the finite argument, with no
  quantified induction formula.
-/

namespace LeanProofs.IPRA.Foundations.FiniteQueryTable

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedReflection (one_ne_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `lem:finite-query`: if every field of the table is good, the table is good. -/
theorem table_good (g : PTm 2) {L x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L) ⟶ (inst2 g (var 0) (Syn.shift x) ≐ one))) :
    Γ ⊢[PRAAx] ap2 (prodF g) L x ≐ one := by
  refine (prod_congr_bounded g (one : PTm 2) x x L (.allI (.impI ?_))).eqTrans (prod_one L x)
  have e : inst2 (one : PTm 2) (var 0) (Syn.shift x) = one := by simp [inst2]
  rw [e]
  exact Prf.impE h.allOpen.wk Prf.hyp0

/-- For bits, a good table has every field good. -/
theorem table_entry (g : PTm 2) {L i x : PTm n} (hbit : Γ ⊢[PRAAx] le (inst2 g i x) one)
    (hi : Γ ⊢[PRAAx] lt i L) (h : Γ ⊢[PRAAx] ap2 (prodF g) L x ≐ one) :
    Γ ⊢[PRAAx] inst2 g i x ≐ one := by
  refine .orE (zero_or_succ (inst2 g i x)) ?_ ?_
  · have z := prod_zero_of g hi.wk (Prf.hyp0 (Γ := Γ) (φ := inst2 g i x ≐ zero))
    exact one_ne_zero _ (h.wk.eqSymm.eqTrans z)
  · have hs : ((inst2 g i x ≐ succ (pred (inst2 g i x))) :: Γ) ⊢[PRAAx]
        inst2 g i x ≐ succ (pred (inst2 g i x)) := Prf.hyp0
    have lo : ((inst2 g i x ≐ succ (pred (inst2 g i x))) :: Γ) ⊢[PRAAx] le one (inst2 g i x) :=
      le_congr (.eqRefl _) hs.eqSymm (by ipra_le 𝔟 (pred (inst2 g i x)))
    exact le_antisymm hbit.wk lo

/-- `cor:fix-precision`: fix the precision, run the finite argument, then quantify. -/
theorem fix_precision {H : Fm PTm n} {Out : Fm PTm (n + 1)}
    (h : (Fm.shift H :: Γ.map Fm.shift) ⊢[PRAAx] Out) : Γ ⊢[PRAAx] H ⟶ Fm.all Out :=
  .impI (.allI h)

end LeanProofs.IPRA.Foundations.FiniteQueryTable
