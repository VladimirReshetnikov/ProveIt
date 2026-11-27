import IPRADerivations.Core.MultiSums

/-!
# Substitution into a re-indexed body

A body `f : PTm 2` whose variables have been re-indexed by terms `a, b` and then substituted is the instance of
`f` at the substituted terms. Many proofs carried this fact as a local `have hf : Syn.subst ![d, P]
(Syn.subst ![var 0, sndT (var 1)] w) = inst2 w d (sndT P)`; it is `subst_inst2` with its left side unfolded.

* `subst_reindex2 σ a b f : Syn.subst σ (Syn.subst ![a, b] f) = inst2 f (Syn.subst σ a) (Syn.subst σ b)`;
* `subst_reindex3 σ a b c f`, the same for a body with three variables and `inst3`.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn

variable {n k : ℕ}

theorem subst_reindex2 (σ : Fin k → PTm n) (a b : PTm k) (f : PTm 2) :
    Syn.subst σ (Syn.subst ![a, b] f) = inst2 f (Syn.subst σ a) (Syn.subst σ b) :=
  subst_inst2 σ f a b

theorem subst_reindex3 (σ : Fin k → PTm n) (a b c : PTm k) (f : PTm 3) :
    Syn.subst σ (Syn.subst ![a, b, c] f) = inst3 f (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) :=
  subst_inst3 σ f a b c

end LeanProofs.IPRA
