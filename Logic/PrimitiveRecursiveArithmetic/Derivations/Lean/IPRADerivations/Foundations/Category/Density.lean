import IPRADerivations.Foundations.Yoneda
import IPRADerivations.Core.Header

/-! Imported from the packet `foundations/category_theory_ipra_2026-11-20`, `lean/CategoryIPRA/Density.lean`: the namespace is placed under `LeanProofs.IPRA` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-!
# Object-language algebra needed by the explicit density presentation

Uncompiled integration draft against ProveIt
72d37f6d06fa7b5bd0a46732060446d1cffa3f2d (Lean 4.32.0).

A generator at b is the finite tuple (a,x,f), with f : b → a and x ∈ F(a).
Its value is F(f,x). Equality of generators is defined by equality of their
values. These lemmas are the object-language calculations behind the
canonical representative (b,F(f,x),1_b) and reindexing along k : c → b.
Packaging tuple codes and the full universal cocone statement is roadmap
work; this file does not assert that those additional steps are complete.
-/

namespace LeanProofs.IPRA.Foundations.Category.Density

open_ipra
open LeanProofs.IPRA.Foundations.PresentedCategory
open LeanProofs.IPRA.Foundations.Yoneda

variable {C : Pres} {F : Fam} (FL : FamLaws C F)
variable {n : ℕ} {Γ : List (Fm PTm n)}

include FL

theorem value_carrier {p a b f x : PTm n}
    (hf : Γ ⊢[PRAAx] C.hom b a f)
    (hx : Γ ⊢[PRAAx] F.car p a x) :
    Γ ⊢[PRAAx] F.car p b (F.ac p b a f x) :=
  FL.act_car hf hx

theorem canonical_value {p b z : PTm n}
    (hz : Γ ⊢[PRAAx] F.car p b z) :
    Γ ⊢[PRAAx] F.sim p b (F.ac p b b (C.id1 b) z) z :=
  FL.act_id hz

theorem generator_roundtrip {p a b f x : PTm n}
    (hf : Γ ⊢[PRAAx] C.hom b a f)
    (hx : Γ ⊢[PRAAx] F.car p a x) :
    Γ ⊢[PRAAx] F.sim p b
      (F.ac p b b (C.id1 b) (F.ac p b a f x))
      (F.ac p b a f x) :=
  FL.act_id (FL.act_car hf hx)

theorem reindex_value {p a b c k f x : PTm n}
    (hk : Γ ⊢[PRAAx] C.hom c b k)
    (hf : Γ ⊢[PRAAx] C.hom b a f)
    (hx : Γ ⊢[PRAAx] F.car p a x) :
    Γ ⊢[PRAAx] F.sim p c
      (F.ac p c a (C.comp c b a f k) x)
      (F.ac p c b k (F.ac p b a f x)) :=
  FL.act_comp hk hf hx

end LeanProofs.IPRA.Foundations.Category.Density
