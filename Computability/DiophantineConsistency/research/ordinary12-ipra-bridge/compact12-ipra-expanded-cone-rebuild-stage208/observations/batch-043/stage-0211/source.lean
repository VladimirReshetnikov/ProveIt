import BusyBeaver.ZFC.QuotientPower
import BusyBeaver.ZFC.KQ1Collect

/-!
CP and all native-Form GIC instances in the actual bisimulation quotient.

The new trace is a literal equality-free matrix with both input and output
raw-membership guards. Its output is a literal raw subset, not merely SubD.
This lets the original raw CP container bound every quotient subset without
assuming collection for arbitrary semantic predicates or iterating containers.
Full native GIC uses only the existing equality-free translation of each Form.

The input is an actual equality-free CP/GIC model and an explicit inhabitant.
No irreflexivity premise or quotient-irreflexivity conclusion occurs here.
In particular raw IR must not be silently transported across bisimilarity.
This supplies neither a numerical decoded-bundle model nor a machine endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.QuotientCPGIC

open Form Profile ProfileCollection ProfileComposition ProfileAxioms
open ProfileSyntax ProfileModel CompositionModel DeepPositiveClosure

universe u
variable {V : Type u}

/-- Parameter 0 is the raw domain; the formula's old parameters start at 3. -/
def strongTraceForm (phi : Form) : Form :=
  fAnd (fMem 0 2) (fAnd (fMem 1 2) (fAnd (sameForm 1 0)
    (rename QuotientSeparation.separationRename (QuotientModel.translate phi))))

theorem equalityFree_strongTraceForm (phi : Form) :
    EqualityFree (strongTraceForm phi) :=
  ⟨True.intro, ⟨True.intro, ⟨equalityFree_sameForm 1 0,
    equalityFree_rename (QuotientModel.translate phi)
      QuotientSeparation.separationRename (QuotientModel.equalityFree_translate phi)⟩⟩⟩

theorem sat_strongTraceForm (mem : V → V → Prop) (phi : Form)
    (a : V) (env : Nat → V) (x y : V) :
    MatrixRelation mem (strongTraceForm phi) (scons a env) x y ↔
      mem x a ∧ mem y a ∧ Same mem y x ∧
        QuotientModel.RelSat mem (scons x env) phi := by
  have hr := Sat_rename_ext (mem := mem) (QuotientModel.translate phi)
    QuotientSeparation.separationRename (scons x (scons y (scons a env)))
    (scons x env) (fun n => match n with | 0 => rfl | _ + 1 => rfl)
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr (sat_sameForm mem _ 1 0)
      (hr.trans (QuotientModel.sat_translate mem phi (scons x env)))))

/-- Only this actual matrix instance is requested from the raw GIC schema. -/
theorem strongTrace_instance (mem : V → V → Prop) (h : ModelsGIC mem)
    (a : V) (phi : Form) (env : Nat → V) :
    CollectionInstance mem (fun x y => mem x a ∧ mem y a ∧ Same mem y x ∧
      QuotientModel.RelSat mem (scons x env) phi) :=
  instance_of_matrix mem h (strongTraceForm phi) (equalityFree_strongTraceForm phi)
    (scons a env) _ (sat_strongTraceForm mem phi a env)

/-- The output guard gives a literal subset while preserving interpreted trace. -/
theorem strong_trace (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) (a : V) (phi : Form) (env : Nat → V) :
    ∃ r, PositiveClosure.Sub mem r a ∧ ∀ z, Member mem z r ↔
      Member mem z a ∧ QuotientModel.RelSat mem (scons z env) phi := by
  have hInv (x y : V) (hxy : Eqv mem x y) :
      QuotientModel.RelSat mem (scons x env) phi ↔
        QuotientModel.RelSat mem (scons y env) phi :=
    QuotientModel.relSat_congr mem witness h phi _ _ fun n => by
      cases n with | zero => exact hxy | succ n => exact eqv_refl_of_model mem witness h (env n)
  obtain ⟨r, hSupport, hCover⟩ := strongTrace_instance mem h.2 a phi env a
  refine ⟨r, fun y hyr => (hSupport y hyr).elim fun _ hx => hx.2.1, fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hyr, hzy⟩
    obtain ⟨x, _, hya, hyx, hpx⟩ := hSupport y hyr
    have hzx := eqv_trans_of_model mem witness h hzy
      (same_eqv mem (eqv_refl_of_model mem witness h) hyx)
    exact ⟨⟨y, hya, hzy⟩, (hInv z x hzx).mpr hpx⟩
  · rintro ⟨⟨x, hxa, hzx⟩, hpz⟩
    obtain ⟨y, hyr, _, _, hyx, _⟩ := hCover x hxa
      ⟨x, hxa, hxa, same_refl mem x, (hInv z x hzx).mp hpz⟩
    exact ⟨y, hyr, eqv_trans_of_model mem witness h hzx
      (same_eqv mem (eqv_refl_of_model mem witness h) (same_symm mem hyx))⟩

/-- Every interpreted subset has an equivalent representative literally inside a. -/
theorem literal_subset_representative (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) (a z : V) (hz : InterpretedSub mem z a) :
    ∃ r, PositiveClosure.Sub mem r a ∧ Eqv mem z r := by
  obtain ⟨r, hrSub, hr⟩ := strong_trace mem witness h a (fMem 0 1) (fun _ => z)
  exact ⟨r, hrSub, eqv_extensionality_of_model mem witness h z r fun t =>
    ⟨fun htz => (hr t).mpr ⟨hz t htz, htz⟩, fun htr => ((hr t).mp htr).2⟩⟩

/-- Raw transitivity becomes transitivity for interpreted membership. -/
theorem interpreted_transitive (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) (v : V) (hv : PositiveClosure.Transitive mem v) :
    PositiveClosure.Transitive (Member mem) v := by
  rintro x ⟨x', hx'v, hxx'⟩ z hzx
  obtain ⟨z', hz'x', hzz'⟩ :=
    (QuotientModel.member_right_congr mem witness h hxx').mp hzx
  exact ⟨z', hv x' hx'v z' hz'x', hzz'⟩

/-- The very same raw container witnesses CP in the full quotient. -/
theorem quotient_containers (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) :
    Containers (QuotientModel.quotientMember mem witness h) := by
  intro a
  induction a using Quotient.ind with
  | _ a =>
    obtain ⟨v, hav, hTrans, hPower⟩ :=
      ((sat_containerForm mem (fun _ => witness)).mp (h.1 _)) a
    refine ⟨QuotientModel.mk mem witness h v,
      raw_member mem (eqv_refl_of_model mem witness h) hav, ?_, ?_⟩
    · intro x hx z hz
      induction x, z using Quotient.ind₂ with
      | _ x z => exact interpreted_transitive mem witness h v hTrans x hx z hz
    · intro x hx
      induction x using Quotient.ind with
      | _ x =>
        obtain ⟨x', hx'v, hxx'⟩ := hx
        obtain ⟨p, hpv, hp⟩ := hPower x' hx'v
        refine ⟨QuotientModel.mk mem witness h p,
          raw_member mem (eqv_refl_of_model mem witness h) hpv, ?_⟩
        intro z hz
        induction z using Quotient.ind with
        | _ z =>
          have hzx' : InterpretedSub mem z x' := fun t ht =>
            (QuotientModel.member_right_congr mem witness h hxx').mp
              ((QuotientPower.quotient_sub mem witness h z x).mp hz t ht)
          obtain ⟨r, hrSub, hzr⟩ := literal_subset_representative mem witness h x' z hzx'
          exact ⟨r, hp r hrSub, hzr⟩

/-- Matrix satisfaction respects both bisimulation-equivalent inputs. -/
theorem rel_matrix_congr (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) (phi : Form) (env : Nat → V)
    {x x' y y' : V} (hxx' : Eqv mem x x') (hyy' : Eqv mem y y') :
    QuotientModel.RelSat mem (scons x (scons y env)) phi ↔
      QuotientModel.RelSat mem (scons x' (scons y' env)) phi :=
  KQ1Collect.rel_matrix_congr mem witness (QuotientModel.ofCPGIC mem witness h) phi env hxx' hyy'

/-- The raw instance is always the equality-free translation of an actual Form. -/
theorem translated_instance (mem : V → V → Prop) (h : ModelsGIC mem)
    (phi : Form) (env : Nat → V) :
    CollectionInstance mem
      (fun x y => QuotientModel.RelSat mem (scons x (scons y env)) phi) :=
  KQ1Collect.translated_instance mem h phi env

/-- Full native-equality matrices are covered, with an arbitrary quotient valuation. -/
theorem quotient_collection (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) (phi : Form)
    (env : Nat → QuotientModel.Domain mem witness h) :
    CollectionInstance (QuotientModel.quotientMember mem witness h)
      (MatrixRelation (QuotientModel.quotientMember mem witness h) phi env) :=
  KQ1Collect.quotient_collection mem witness (QuotientModel.ofCPGIC mem witness h) phi env

/-- This schema includes native Eq, with no EqualityFree premise on phi. -/
theorem quotient_fullGIC (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) :
    ∀ phi env, Sat (QuotientModel.quotientMember mem witness h) env (gicForm phi) :=
  KQ1Collect.quotient_fullGIC mem witness (QuotientModel.ofCPGIC mem witness h)

/-- Actual CP plus every native-Form GIC instance, rather than only EF instances. -/
theorem quotient_fullCPGIC (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) :
    (∀ env, Sat (QuotientModel.quotientMember mem witness h) env containerForm) ∧
      ∀ phi env, Sat (QuotientModel.quotientMember mem witness h) env (gicForm phi) :=
  ⟨fun env => (sat_containerForm _ env).mpr (quotient_containers mem witness h),
    quotient_fullGIC mem witness h⟩

/-- In particular the quotient again satisfies the original EF CP/GIC interface. -/
theorem quotient_modelsCPGIC (mem : V → V → Prop) (witness : V)
    (h : ModelsCPGIC mem) : ModelsCPGIC (QuotientModel.quotientMember mem witness h) :=
  ⟨(quotient_fullCPGIC mem witness h).1,
    fun phi _ env => quotient_fullGIC mem witness h phi env⟩

end SetTheory.BusyBeaver.ZFC.QuotientCPGIC
