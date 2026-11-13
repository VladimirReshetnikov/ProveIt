import ConciseIPRA.NativeProgressiveRoundTrip

/-!
# The mixed closure

`MCPrf` is the calculus `C_m` of the package `Research/scope_and_closure`
(`theory/mixed_closure.tex`).  It is the uniform calculus `RPrf` of
`NativeProgressive` with transport in an arbitrary formula template as its
primitive equality rule,

  from `s = t` and `F(s)` infer `F(t)`,

in place of transport in an equation template.  Its closure is *mixed*:
progressive at a literal equation and anchored at a compound matrix, as in
`RPrf`.

`mcprf_iff_rprf` proves that the two calculi derive the same sequents: the
stronger transport is the derived rule `RPrf.tr` of `NativeProgressiveLeibniz`,
and transport in an equation template is an instance of it.  Hence the results
for `RPrf` hold for `MCPrf`: it derives a sequent exactly when the kernel
derives its progressive reading (`mcprf_iff_rd`), and it derives the padded
translation of a sequent exactly when the kernel derives the sequent
(`mcprf_emb_iff`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n : ℕ}

/-- Derivability with the mixed closure and transport in formula templates. -/
inductive MCPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : MCPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      MCPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      MCPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- Transport in a formula template: from `s = t` and `F(s)` infer `F(t)`. -/
  | tr {n : ℕ} {Γ : List (NFm n)} (F : NFm (n + 1)) {s t : Tm n} (h₁ : MCPrf Γ (.eq s t))
      (h₂ : MCPrf Γ (F.subst (inst s))) : MCPrf Γ (F.subst (inst t))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (a c : Tm n) (h₁ : MCPrf Γ (.Q B))
      (h₂ : MCPrf Γ (B.subst (inst (NFm.eta B a)))) :
      MCPrf Γ (B.subst (inst (Tm.add c (NFm.eta B a))))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : MCPrf Γ (.D B))
      (h₂ : MCPrf (.Q B :: Γ.map NFm.shift) A.shift) : MCPrf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : MCPrf ((B.subst (up (inst t))).subst (repl (NFm.eta B (Syn.var 0)))
          :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) : MCPrf Γ (.D B)

variable {Γ : List (NFm n)} {A : NFm n}

theorem MCPrf.toR (h : MCPrf Γ A) : RPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | tr F _ _ ih₁ ih₂ => exact RPrf.tr F ih₁ ih₂
  | qE a c _ _ ih₁ ih₂ => exact .qE a c ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .dI B t ih

theorem RPrf.toMC (h : RPrf Γ A) : MCPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trEq p q _ _ ih₁ ih₂ => exact .tr (.eq p q) ih₁ ih₂
  | qE a c _ _ ih₁ ih₂ => exact .qE a c ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .dI B t ih

/-- **The mixed closure and the uniform calculus.**  They derive the same
sequents: transport in a formula template is a derived rule of the uniform
calculus. -/
theorem mcprf_iff_rprf : MCPrf Γ A ↔ RPrf Γ A := ⟨MCPrf.toR, RPrf.toMC⟩

/-- The mixed closure derives a sequent exactly when the kernel derives its
progressive reading. -/
theorem mcprf_iff_rd : MCPrf Γ A ↔ NPrf (Γ.map NFm.rd) A.rd :=
  mcprf_iff_rprf.trans rprf_iff_rd

/-- The kernel derives a sequent exactly when the mixed closure derives its
padded translation. -/
theorem mcprf_emb_iff : MCPrf (Γ.map NFm.emb) A.emb ↔ NPrf Γ A :=
  mcprf_iff_rprf.trans rprf_emb_iff

/-- The mixed closure is consistent. -/
theorem mcprf_consistent : ¬ MCPrf ([] : List (NFm 0)) NFm.bot := fun h =>
  rprf_consistent h.toR

end LeanProofs.ConciseIPRA
