import BusyBeaver.ZFC.WFRelativization
import BusyBeaver.ZFC.PowerSets

/-! The general well-founded-part model construction.
Declarations are copied verbatim from WFModel; the CPGIC specialization
and historical enumerator consequences remain in its compatibility wrapper. -/

namespace SetTheory.BusyBeaver.ZFC.WFModel
open Form WellFoundedPart WFRelativization
universe u
variable {V : Type u} {mem : V → V → Prop}

abbrev ClosedWF (mem : V → V → Prop) : Prop :=
  ∀ a, (∀ x, mem x a → WF mem x) → WF mem a

theorem finiteBase (H : ZFAxioms mem) : FiniteSets.Base mem where
  ext := H.ext
  pair := H.pair
  sep := H.sep
  union := H.union

theorem domain_ext (H : ZFAxioms mem) (a b : Domain mem)
    (h : ∀ x, domainMem mem x a ↔ domainMem mem x b) : a = b := by
  apply Subtype.ext
  apply H.ext
  intro x
  constructor
  · intro hx
    exact (h ⟨x, wf_mem a.property hx⟩).mp hx
  · intro hx
    exact (h ⟨x, wf_mem b.property hx⟩).mpr hx

theorem domain_pair (H : ZFAxioms mem) (hc : ClosedWF mem) (a b : Domain mem) :
    ∃ p : Domain mem, ∀ x, domainMem mem x p ↔ x = a ∨ x = b := by
  obtain ⟨p, hp⟩ := H.pair a.val b.val
  have hwp : WF mem p := hc p fun x hx => by
    rcases (hp x).mp hx with h | h
    · exact h.symm ▸ a.property
    · exact h.symm ▸ b.property
  refine ⟨⟨p, hwp⟩, fun x => ?_⟩
  constructor
  · intro hx
    rcases (hp x.val).mp hx with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (h | h)
    · exact (hp x.val).mpr (Or.inl (congrArg Subtype.val h))
    · exact (hp x.val).mpr (Or.inr (congrArg Subtype.val h))

theorem domain_union (H : ZFAxioms mem) (hc : ClosedWF mem) (a : Domain mem) :
    ∃ w : Domain mem, ∀ x, domainMem mem x w ↔
      ∃ y : Domain mem, domainMem mem x y ∧ domainMem mem y a := by
  obtain ⟨w, hw⟩ := H.union a.val
  have hww : WF mem w := hc w fun x hx => by
    obtain ⟨y, hxy, hya⟩ := (hw x).mp hx
    exact wf_mem (wf_mem a.property hya) hxy
  refine ⟨⟨w, hww⟩, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨y, hxy, hya⟩ := (hw x.val).mp hx
    exact ⟨⟨y, wf_mem a.property hya⟩, hxy, hya⟩
  · rintro ⟨y, hxy, hya⟩
    exact (hw x.val).mpr ⟨y.val, hxy, hya⟩

theorem domain_separation (H : ZFAxioms mem) (hc : ClosedWF mem)
    (phi : Form) (env : Nat → Domain mem) (a : Domain mem) :
    ∃ s : Domain mem, ∀ x, domainMem mem x s ↔
      domainMem mem x a ∧ Sat (domainMem mem) (scons x env) phi := by
  obtain ⟨s, hs⟩ := H.sep (translate phi) (liftEnv mem env) a.val
  have hws : WF mem s := hc s fun x hx => wf_mem a.property ((hs x).mp hx).1
  refine ⟨⟨s, hws⟩, fun x => ?_⟩
  change mem x.val s ↔ mem x.val a.val ∧ _
  rw [hs x.val]
  apply and_congr_right
  intro _
  have he : scons x.val (liftEnv mem env) = liftEnv mem (scons x env) :=
    funext fun i => by cases i <;> rfl
  rw [he]
  exact sat_translate mem phi (scons x env)

theorem domain_power (hc : ClosedWF mem) (hp : PSCCalibration.PowerSets mem)
    (a : Domain mem) :
    ∃ p : Domain mem, ∀ x, domainMem mem x p ↔ Sub (domainMem mem) x a := by
  obtain ⟨p, hp⟩ := hp a.val
  have hwp : WF mem p := hc p fun x hx =>
    hc x fun z hz => wf_mem a.property ((hp x).mp hx z hz)
  refine ⟨⟨p, hwp⟩, fun x => ?_⟩
  constructor
  · exact fun hx z hz => (hp x.val).mp hx z.val hz
  · exact fun hx => (hp x.val).mpr fun z hz => hx ⟨z, wf_mem x.property hz⟩ hz

/-- Separating WF from an inductive set gives an inductive WF set. -/
theorem domain_infinity (H : ZFAxioms mem) (hc : ClosedWF mem) :
    ∃ I : Domain mem,
      (∃ e : Domain mem, domainMem mem e I ∧ ∀ z, ¬ domainMem mem z e) ∧
      (∀ x, domainMem mem x I → ∃ sx : Domain mem, domainMem mem sx I ∧
        ∀ t, domainMem mem t sx ↔ domainMem mem t x ∨ t = x) := by
  obtain ⟨I, ⟨e, heI, he⟩, hsucc⟩ := H.inf
  obtain ⟨J, hJ⟩ := H.sep (wfForm 0) (fun _ => e) I
  have hJ' (x : V) : mem x J ↔ mem x I ∧ WF mem x :=
    (hJ x).trans (and_congr_right fun _ => sat_wfForm mem (scons x (fun _ => e)) 0)
  have hwJ : WF mem J := hc J fun x hx => ((hJ' x).mp hx).2
  have hwe : WF mem e := wf_empty (finiteBase H) e he
  refine ⟨⟨J, hwJ⟩, ⟨⟨e, hwe⟩, (hJ' e).mpr ⟨heI, hwe⟩, ?_⟩, ?_⟩
  · exact fun z => he z.val
  · intro x hx
    obtain ⟨sx, hsI, hs⟩ := hsucc x.val ((hJ' x.val).mp hx).1
    have hws : WF mem sx := hc sx fun z hz => by
      rcases (hs z).mp hz with hz | hz
      · exact wf_mem x.property hz
      · exact hz.symm ▸ x.property
    refine ⟨⟨sx, hws⟩, (hJ' sx).mpr ⟨hsI, hws⟩, fun t => ?_⟩
    constructor
    · intro ht
      rcases (hs t.val).mp ht with ht | ht
      · exact Or.inl ht
      · exact Or.inr (Subtype.ext ht)
    · rintro (ht | ht)
      · exact (hs t.val).mpr (Or.inl ht)
      · exact (hs t.val).mpr (Or.inr (congrArg Subtype.val ht))

/-- Both arguments are guarded, so raw functionality holds globally. -/
def replacementForm (phi : Form) : Form :=
  fAnd (wfForm 0) (fAnd (wfForm 1) (translate phi))

theorem replacementForm_spec (phi : Form) (env : Nat → Domain mem)
    (y x : V) : relOf mem (replacementForm phi) (liftEnv mem env) y x ↔
      WF mem y ∧ WF mem x ∧ Sat mem (scons y (scons x (liftEnv mem env))) (translate phi) := by
  change (Sat mem _ (wfForm 0) ∧ Sat mem _ (wfForm 1) ∧ _) ↔ _
  exact and_congr (sat_wfForm mem _ 0) (and_congr (sat_wfForm mem _ 1) Iff.rfl)

private theorem raw_rel_iff (phi : Form) (env : Nat → Domain mem)
    (y x : Domain mem) :
    Sat mem (scons y.val (scons x.val (liftEnv mem env))) (translate phi) ↔
      relOf (domainMem mem) phi env y x := by
  have he : scons y.val (scons x.val (liftEnv mem env)) = liftEnv mem (scons y (scons x env)) :=
    funext fun i => by rcases i with _ | _ | _ <;> rfl
  rw [he]
  exact sat_translate mem phi (scons y (scons x env))

theorem domain_replacement (H : ZFAxioms mem) (hc : ClosedWF mem)
    (phi : Form) (env : Nat → Domain mem)
    (hf : Functional (relOf (domainMem mem) phi env)) (a : Domain mem) :
    ∃ r : Domain mem, ∀ y, domainMem mem y r ↔
      ∃ x : Domain mem, domainMem mem x a ∧ relOf (domainMem mem) phi env y x := by
  have hfun : Functional (relOf mem (replacementForm phi) (liftEnv mem env)) := by
    intro x y1 y2 h1 h2
    obtain ⟨hy1, hx, h1⟩ := (replacementForm_spec phi env y1 x).mp h1
    obtain ⟨hy2, _, h2⟩ := (replacementForm_spec phi env y2 x).mp h2
    exact congrArg Subtype.val (hf ⟨x, hx⟩ ⟨y1, hy1⟩ ⟨y2, hy2⟩
      ((raw_rel_iff phi env ⟨y1, hy1⟩ ⟨x, hx⟩).mp h1)
      ((raw_rel_iff phi env ⟨y2, hy2⟩ ⟨x, hx⟩).mp h2))
  obtain ⟨r, hr⟩ := H.repl (replacementForm phi) (liftEnv mem env) hfun a.val
  have hwr : WF mem r := hc r fun y hy => by
    obtain ⟨x, _, hrel⟩ := (hr y).mp hy
    exact ((replacementForm_spec phi env y x).mp hrel).1
  refine ⟨⟨r, hwr⟩, fun y => ?_⟩
  constructor
  · intro hy
    obtain ⟨x, hxa, hrel⟩ := (hr y.val).mp hy
    obtain ⟨_, hx, hrel⟩ := (replacementForm_spec phi env y.val x).mp hrel
    exact ⟨⟨x, hx⟩, hxa, (raw_rel_iff phi env y ⟨x, hx⟩).mp hrel⟩
  · rintro ⟨x, hxa, hrel⟩
    exact (hr y.val).mpr ⟨x.val, hxa,
      (replacementForm_spec phi env y.val x.val).mpr
        ⟨y.property, x.property, (raw_rel_iff phi env y x).mpr hrel⟩⟩

/-- All six ambient ZF fields hold in the interpreted WF domain. -/
theorem domain_zfAxioms (H : ZFAxioms mem) (hc : ClosedWF mem) :
    ZFAxioms (domainMem mem) where
  ext := domain_ext H
  pair := domain_pair H hc
  union := domain_union H hc
  sep := domain_separation H hc
  inf := domain_infinity H hc
  repl := domain_replacement H hc

/-- Every actual closed ZF sentence holds, including Regularity. -/
theorem domain_models_ZF (H : ZFAxioms mem) (hc : ClosedWF mem)
    (hp : PSCCalibration.PowerSets mem) (env : Nat → Domain mem) :
    ∀ phi, ZFax_s phi → Sat (domainMem mem) env phi := by
  intro phi hphi
  have A := domain_zfAxioms H hc
  rcases hphi with rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ | ⟨phi, rfl⟩
  · exact (closeN_valid (bound Ext_form) Ext_form).mpr (bridge_Ext.mpr A.ext) env
  · exact (closeN_valid (bound Reg_form) Reg_form).mpr (domain_regular mem) env
  · exact (closeN_valid (bound Pow_form) Pow_form).mpr (bridge_Pow.mpr (domain_power hc hp)) env
  · exact (closeN_valid (bound Pair_form) Pair_form).mpr (bridge_Pair.mpr A.pair) env
  · exact (closeN_valid (bound Union_form) Union_form).mpr (bridge_Union.mpr A.union) env
  · exact (closeN_valid (bound Inf_form) Inf_form).mpr (fun e => (bridge_Inf e).mpr A.inf) env
  · exact (closeN_valid (bound (Sep_form phi)) (Sep_form phi)).mpr
      (fun e => bridge_Sep.mpr A.sep phi e) env
  · exact (closeN_valid (bound (Repl_form phi)) (Repl_form phi)).mpr
      (fun e => (bridge_Repl phi e).mpr (A.repl phi e)) env

end SetTheory.BusyBeaver.ZFC.WFModel
