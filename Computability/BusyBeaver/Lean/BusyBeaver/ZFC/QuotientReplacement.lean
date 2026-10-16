import BusyBeaver.ZFC.QuotientSeparation

/-!
Actual formula-indexed Replacement in the CP/GIC bisimulation quotient.

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

namespace SetTheory.BusyBeaver.ZFC.QuotientReplacement

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
  fAnd (fMem 0 2) (rename replacementRename (QuotientModel.translate phi))

theorem equalityFree_replacementChoiceForm (phi : Form) :
    EqualityFree (replacementChoiceForm phi) :=
  ⟨True.intro, equalityFree_rename (QuotientModel.translate phi) replacementRename
    (QuotientModel.equalityFree_translate phi)⟩

theorem sat_replacementChoiceForm (mem : V → V → Prop) (phi : Form)
    (a : V) (env : Nat → V) (x y : V) :
    MatrixRelation mem (replacementChoiceForm phi) (scons a env) x y ↔
      ReplacementChoice mem a
        (fun u v => QuotientModel.RelSat mem (scons v (scons u env)) phi) x y := by
  have hr := Sat_rename_ext (mem := mem) (QuotientModel.translate phi) replacementRename
    (scons x (scons y (scons a env))) (scons y (scons x env))
    (fun n => match n with | 0 => rfl | 1 => rfl | _ + 2 => rfl)
  exact and_congr Iff.rfl
    (hr.trans (QuotientModel.sat_translate mem phi (scons y (scons x env))))

theorem replacement_instance (mem : V → V → Prop) (h : ModelsGIC mem)
    (a : V) (phi : Form) (env : Nat → V) :
    CollectionInstance mem (ReplacementChoice mem a
      (fun x y => QuotientModel.RelSat mem (scons y (scons x env)) phi)) :=
  instance_of_matrix mem h (replacementChoiceForm phi)
    (equalityFree_replacementChoiceForm phi) (scons a env) _
    (sat_replacementChoiceForm mem phi a env)

/-- Partial functionality on the interpreted domain suffices for this image. -/
theorem interpreted_replacement (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) (a : V) (phi : Form) (env : Nat → V)
    (hFunctional : ∀ x y z, Member mem x a →
      QuotientModel.RelSat mem (scons y (scons x env)) phi →
      QuotientModel.RelSat mem (scons z (scons x env)) phi → Eqv mem y z) :
    ∃ b, ∀ z, Member mem z b ↔ ∃ x, Member mem x a ∧
      QuotientModel.RelSat mem (scons z (scons x env)) phi := by
  apply replacement_of_instance mem a
    (fun x y => QuotientModel.RelSat mem (scons y (scons x env)) phi)
    (eqv_refl_of_model mem witness h)
    (fun _ _ hxy => eqv_symm_of_model mem witness h hxy) _ hFunctional
    (replacement_instance mem h.2 a phi env)
  intro x x' y y' hxx' hyy'
  apply QuotientModel.relSat_congr mem witness h phi
    (scons y (scons x env)) (scons y' (scons x' env))
  intro n
  match n with
  | 0 => exact hyy'
  | 1 => exact hxx'
  | k + 2 => exact eqv_refl_of_model mem witness h (env k)

/-- Formula relations under any quotient valuation agree with their lifted
interpretations; source slot0 is output and slot1 is input. -/
theorem quotient_relOf (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (phi : Form) (env : Nat → QuotientModel.Domain mem witness h) (x y : V) :
    relOf (QuotientModel.quotientMember mem witness h) phi env
      (QuotientModel.mk mem witness h y) (QuotientModel.mk mem witness h x) ↔
    QuotientModel.RelSat mem
      (scons y (scons x (QuotientSeparation.liftEnv mem witness h env))) phi := by
  have he : (fun i => QuotientModel.mk mem witness h
      (QuotientSeparation.liftEnv mem witness h env i)) = env := by
    funext i
    exact QuotientSeparation.mk_liftEnv mem witness h env i
  have hs := QuotientModel.sat_quotient mem witness h phi
    (scons y (scons x (QuotientSeparation.liftEnv mem witness h env)))
  rw [QuotientModel.mk_scons, QuotientModel.mk_scons, he] at hs
  exact hs

/-- The full quotient satisfies the actual semantic `ZFAxioms.repl` interface. -/
theorem quotient_replacement (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (phi : Form) (env : Nat → QuotientModel.Domain mem witness h)
    (hFunctional : Functional (relOf (QuotientModel.quotientMember mem witness h) phi env))
    (a : QuotientModel.Domain mem witness h) :
    ∃ b, ∀ y, QuotientModel.quotientMember mem witness h y b ↔
      ∃ x, QuotientModel.quotientMember mem witness h x a ∧
        relOf (QuotientModel.quotientMember mem witness h) phi env y x := by
  induction a using Quotient.ind with
  | _ a =>
    let rawEnv := QuotientSeparation.liftEnv mem witness h env
    have hRawFunctional : ∀ x y z, Member mem x a →
        QuotientModel.RelSat mem (scons y (scons x rawEnv)) phi →
        QuotientModel.RelSat mem (scons z (scons x rawEnv)) phi → Eqv mem y z := by
      intro x y z _ hxy hxz
      apply (QuotientModel.mk_eq_iff mem witness h y z).mp
      exact hFunctional (QuotientModel.mk mem witness h x)
        (QuotientModel.mk mem witness h y) (QuotientModel.mk mem witness h z)
        ((quotient_relOf mem witness h phi env x y).mpr hxy)
        ((quotient_relOf mem witness h phi env x z).mpr hxz)
    obtain ⟨b, hb⟩ := interpreted_replacement mem witness h a phi rawEnv hRawFunctional
    refine ⟨QuotientModel.mk mem witness h b, ?_⟩
    intro y
    induction y using Quotient.ind with
    | _ y =>
      apply (hb y).trans
      constructor
      · rintro ⟨x, hxa, hxy⟩
        exact ⟨QuotientModel.mk mem witness h x, hxa,
          (quotient_relOf mem witness h phi env x y).mpr hxy⟩
      · rintro ⟨x, hxa, hxy⟩
        obtain ⟨x, rfl⟩ := Quotient.exists_rep x
        exact ⟨x, hxa, (quotient_relOf mem witness h phi env x y).mp hxy⟩

/-- Every repository Replacement formula holds under every quotient valuation. -/
theorem quotient_repl_form (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    ∀ phi env, SetTheory.Sat (QuotientModel.quotientMember mem witness h) env (Repl_form phi) := by
  intro phi env
  exact (bridge_Repl phi env).mpr (quotient_replacement mem witness h phi env)

end SetTheory.BusyBeaver.ZFC.QuotientReplacement
