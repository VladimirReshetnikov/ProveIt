import BusyBeaver.ZFC.KQ1Separation

/-!
Actual formula-indexed Replacement in the bisimulation quotient of a `QHyp`
structure.

The collection matrix is a literal equality-free formula, guarded by raw
membership in the domain. The requested formula uses the repository's
output-at-0/input-at-1 convention. Its quotient translation supplies both
argument invariance, and functionality in the quotient supplies uniqueness
modulo bisimilarity. There is no collection assumption for arbitrary semantic
relations. Arbitrary quotient parameter valuations are lifted using the
existing representative-selection API.

The argument follows the attributed `S_ax.v:rep_core` construction at upstream
commit 297ab8df7e5de329605c3875b4934643b371a5e3. It proves this axiom schema
and its actual `Repl_form` interface, not all quotient ZF axioms or a numerical
enumerator, register-machine or binary consistency endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.KQ1Replacement

open KQHyp

open Form Profile ProfileCollection ProfileComposition ProfileAxioms
open ProfileSyntax ProfileModel CompositionModel DeepPositiveClosure

universe u
variable {V : Type u}

/-- Swap the matrix's two arguments, and skip the inserted domain slot. -/
def replacementRename : Nat → Nat
  | 0 => 1
  | 1 => 0
  | k + 2 => k + 3

def replacementChoiceForm (phi : Form) : Form :=
  fAnd (fMem 0 2) (rename replacementRename (KQ1Model.translate phi))

theorem equalityFree_replacementChoiceForm (phi : Form) :
    EqualityFree (replacementChoiceForm phi) :=
  ⟨True.intro, equalityFree_rename (KQ1Model.translate phi) replacementRename
    (KQ1Model.equalityFree_translate phi)⟩

theorem sat_replacementChoiceForm (mem : V → V → Prop) (phi : Form)
    (a : V) (env : Nat → V) (x y : V) :
    MatrixRelation mem (replacementChoiceForm phi) (scons a env) x y ↔
      ReplacementChoice mem a
        (fun u v => KQ1Model.RelSat mem (scons v (scons u env)) phi) x y := by
  have hr := Sat_rename_ext (mem := mem) (KQ1Model.translate phi) replacementRename
    (scons x (scons y (scons a env))) (scons y (scons x env))
    (fun n => match n with | 0 => rfl | 1 => rfl | _ + 2 => rfl)
  exact and_congr Iff.rfl
    (hr.trans (KQ1Model.sat_translate mem phi (scons y (scons x env))))

theorem replacement_instance (mem : V → V → Prop) (h : ModelsGIC mem)
    (a : V) (phi : Form) (env : Nat → V) :
    CollectionInstance mem (ReplacementChoice mem a
      (fun x y => KQ1Model.RelSat mem (scons y (scons x env)) phi)) :=
  instance_of_matrix mem h (replacementChoiceForm phi)
    (equalityFree_replacementChoiceForm phi) (scons a env) _
    (sat_replacementChoiceForm mem phi a env)

/-- Partial functionality on the interpreted domain suffices for this image. -/
theorem interpreted_replacement (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) (a : V) (phi : Form) (env : Nat → V)
    (hFunctional : ∀ x y z, Member mem x a →
      KQ1Model.RelSat mem (scons y (scons x env)) phi →
      KQ1Model.RelSat mem (scons z (scons x env)) phi → Eqv mem y z) :
    ∃ b, ∀ z, Member mem z b ↔ ∃ x, Member mem x a ∧
      KQ1Model.RelSat mem (scons z (scons x env)) phi := by
  apply replacement_of_instance mem a
    (fun x y => KQ1Model.RelSat mem (scons y (scons x env)) phi)
    (h.refl)
    (fun _ _ hxy => h.symm hxy) _ hFunctional
    (replacement_instance mem h.gic a phi env)
  intro x x' y y' hxx' hyy'
  apply KQ1Model.relSat_congr mem witness h phi
    (scons y (scons x env)) (scons y' (scons x' env))
  intro n
  match n with
  | 0 => exact hyy'
  | 1 => exact hxx'
  | k + 2 => exact h.refl (env k)

/-- Formula relations under any quotient valuation agree with their lifted
interpretations; source slot0 is output and slot1 is input. -/
theorem quotient_relOf (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (phi : Form) (env : Nat → KQ1Model.Domain mem witness h) (x y : V) :
    relOf (KQ1Model.quotientMember mem witness h) phi env
      (KQ1Model.mk mem witness h y) (KQ1Model.mk mem witness h x) ↔
    KQ1Model.RelSat mem
      (scons y (scons x (KQ1Separation.liftEnv mem witness h env))) phi := by
  have he : (fun i => KQ1Model.mk mem witness h
      (KQ1Separation.liftEnv mem witness h env i)) = env := by
    funext i
    exact KQ1Separation.mk_liftEnv mem witness h env i
  have hs := KQ1Model.sat_quotient mem witness h phi
    (scons y (scons x (KQ1Separation.liftEnv mem witness h env)))
  rwa [KQ1Model.mk_scons, KQ1Model.mk_scons, he] at hs

/-- The full quotient satisfies the actual semantic `ZFAxioms.repl` interface. -/
theorem quotient_replacement (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (phi : Form) (env : Nat → KQ1Model.Domain mem witness h)
    (hFunctional : Functional (relOf (KQ1Model.quotientMember mem witness h) phi env))
    (a : KQ1Model.Domain mem witness h) :
    ∃ b, ∀ y, KQ1Model.quotientMember mem witness h y b ↔
      ∃ x, KQ1Model.quotientMember mem witness h x a ∧
        relOf (KQ1Model.quotientMember mem witness h) phi env y x := by
  induction a using Quotient.ind with
  | _ a =>
    let rawEnv := KQ1Separation.liftEnv mem witness h env
    have hRawFunctional : ∀ x y z, Member mem x a →
        KQ1Model.RelSat mem (scons y (scons x rawEnv)) phi →
        KQ1Model.RelSat mem (scons z (scons x rawEnv)) phi → Eqv mem y z := by
      intro x y z _ hxy hxz
      apply (KQ1Model.mk_eq_iff mem witness h y z).mp
      exact hFunctional (KQ1Model.mk mem witness h x)
        (KQ1Model.mk mem witness h y) (KQ1Model.mk mem witness h z)
        ((quotient_relOf mem witness h phi env x y).mpr hxy)
        ((quotient_relOf mem witness h phi env x z).mpr hxz)
    obtain ⟨b, hb⟩ := interpreted_replacement mem witness h a phi rawEnv hRawFunctional
    refine ⟨KQ1Model.mk mem witness h b, ?_⟩
    intro y
    induction y using Quotient.ind with
    | _ y =>
      apply (hb y).trans
      constructor
      · rintro ⟨x, hxa, hxy⟩
        exact ⟨KQ1Model.mk mem witness h x, hxa,
          (quotient_relOf mem witness h phi env x y).mpr hxy⟩
      · rintro ⟨x, hxa, hxy⟩
        obtain ⟨x, rfl⟩ := Quotient.exists_rep x
        exact ⟨x, hxa, (quotient_relOf mem witness h phi env x y).mp hxy⟩

/-- Every repository Replacement formula holds under every quotient valuation. -/
theorem quotient_repl_form (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    ∀ phi env, SetTheory.Sat (KQ1Model.quotientMember mem witness h) env (Repl_form phi) := by
  intro phi env
  exact (bridge_Repl phi env).mpr (quotient_replacement mem witness h phi env)

end SetTheory.BusyBeaver.ZFC.KQ1Replacement
