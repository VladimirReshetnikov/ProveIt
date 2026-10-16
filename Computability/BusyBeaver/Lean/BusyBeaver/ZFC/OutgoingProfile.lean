import BusyBeaver.ZFC.RawPSCModel
import BusyBeaver.ZFC.TarskiCalculus

/-!
Outgoing inclusion expresses full observational equivalence when twin
singletons exist. The short predicate and reserved-zero translation follow
batch151 source24, `zfc_minimal_theory`, inspected at ProveIt commit
2178c3885423f923021d4aaf1dbf52b4e2060837. The exact observational singleton
resource was already proved by `RawPSCProfile`/`RawPSCModel` from the earlier
PSC research. This module supplies new Lean proofs of these local interfaces.

Every theory-model consequence below uses the existing equality-free,
formula-indexed `ModelsRawPSC`; no closure principle for all external
semantic relations is assumed. There is no EPSC-to-PSC adapter here.

The named translation shifts every source variable and binder by one,
reserves zero for a false point, expands equality by outgoing inclusion,
and maps Bottom to membership(0,0). Its source satisfaction interprets equality
as full observational equivalence, not literal identity of raw objects.
The theorem is semantic: no proof-calculus, numerical-code, compiler,
enumerator, ZFC consistency, or Turing-machine calibration follows here.
-/

namespace SetTheory.BusyBeaver.ZFC.OutgoingProfile

open RawPSCProfile

universe u
variable {V : Type u}

/-- Inclusion of outgoing membership profiles. Its direction is essential. -/
def Outgoing (mem : V → V → Prop) (a b : V) : Prop :=
  ∀ z, mem a z → mem b z

/-- The singleton resource upgrades one-way outgoing inclusion to the full
incoming/outgoing profile. It does not identify raw objects. -/
theorem outgoing_iff_full (mem : V → V → Prop) (hTwins : TwinSingletons mem)
    (a b : V) : Outgoing mem a b ↔ RawPSCProfile.Full mem a b := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := hTwins a
    have has : mem a s := (hs a).mpr (full_refl mem a)
    exact full_symm mem ((hs b).mp (h s has))
  · intro h z hz
    exact (h.2 z).mp hz

theorem outgoing_refl (mem : V → V → Prop) (a : V) : Outgoing mem a a :=
  fun _ h => h

theorem outgoing_symm (mem : V → V → Prop) (hTwins : TwinSingletons mem)
    {a b : V} (h : Outgoing mem a b) : Outgoing mem b a :=
  (outgoing_iff_full mem hTwins b a).mpr
    (full_symm mem ((outgoing_iff_full mem hTwins a b).mp h))

theorem outgoing_trans (mem : V → V → Prop) {a b c : V}
    (hab : Outgoing mem a b) (hbc : Outgoing mem b c) : Outgoing mem a c :=
  fun z hz => hbc z (hab z hz)

theorem outgoing_mem_congr (mem : V → V → Prop) (hTwins : TwinSingletons mem)
    {a a' b b' : V} (ha : Outgoing mem a a') (hb : Outgoing mem b b') :
    mem a b ↔ mem a' b' :=
  full_mem_congr mem ((outgoing_iff_full mem hTwins a a').mp ha)
    ((outgoing_iff_full mem hTwins b b').mp hb)

/-- Four syntax nodes, with the two free indices shifted under a genuine
De Bruijn binder. The quantified variable is the receiving object. -/
def outgoingForm (i j : Nat) : Form :=
  .fAll (.fImp (.fMem (i + 1) 0) (.fMem (j + 1) 0))

theorem sat_outgoingForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (outgoingForm i j) ↔ Outgoing mem (env i) (env j) :=
  Iff.rfl

theorem equalityFree_outgoingForm (i j : Nat) :
    DeepPositiveClosure.EqualityFree (outgoingForm i j) :=
  ⟨True.intro, True.intro⟩

/-- Tree nodes only: labels, coding, logical rules and initialization are
excluded from this measure. -/
def formNodes : Form → Nat
  | .fMem _ _ | .fEq _ _ | .fBot => 1
  | .fImp a b | .fAnd a b | .fOr a b => 1 + formNodes a + formNodes b
  | .fAll a | .fEx a => 1 + formNodes a

theorem outgoingForm_four_nodes (i j : Nat) : formNodes (outgoingForm i j) = 4 := rfl

/-- The actual-model corollary uses only already represented PSC matrices. -/
theorem outgoing_iff_full_of_model (mem : V → V → Prop) (witness : V)
    (hModel : RawPSCModel.ModelsRawPSC mem) (a b : V) :
    Outgoing mem a b ↔ RawPSCProfile.Full mem a b :=
  outgoing_iff_full mem (RawPSCModel.twins_of_model mem witness hModel) a b

theorem sat_outgoingForm_full_of_model (mem : V → V → Prop) (witness : V)
    (hModel : RawPSCModel.ModelsRawPSC mem) (env : Nat → V) (i j : Nat) :
    Sat mem env (outgoingForm i j) ↔ RawPSCProfile.Full mem (env i) (env j) :=
  (sat_outgoingForm mem env i j).trans
    (outgoing_iff_full_of_model mem witness hModel (env i) (env j))

/-! ## Reserved-zero named translation -/

/-- The source named formula's equality is interpreted by the full profile. -/
def FullSat (mem : V → V → Prop) : (Nat → V) → Tarski.NF → Prop
  | env, .rel i j => mem (env i) (env j)
  | env, .eq i j => RawPSCProfile.Full mem (env i) (env j)
  | _, .bot => False
  | env, .imp a b => FullSat mem env a → FullSat mem env b
  | env, .all i a => ∀ d, FullSat mem (Tarski.update env i d) a

/-- Point zero is reserved; source variable n is represented at n+1. -/
def pointed (e : V) (env : Nat → V) : Nat → V
  | 0 => e
  | n + 1 => env n

/-- Positive translated binders preserve the reserved point, even when the
source binder itself is named zero. -/
theorem pointed_update (e : V) (env : Nat → V) (i : Nat) (d : V) :
    Tarski.update (pointed e env) (i + 1) d = pointed e (Tarski.update env i d) := by
  funext n
  cases n with
  | zero => simp [Tarski.update, pointed]
  | succ n => simp [Tarski.update, pointed]

/-- Named outgoing equality; its local zero binder only encloses atoms whose
endpoint labels are positive. It never binds a translated Bottom. -/
def namedOutgoing (i j : Nat) : Tarski.NF :=
  .all 0 (.imp (.rel (i + 1) 0) (.rel (j + 1) 0))

theorem sat_namedOutgoing (mem : V → V → Prop) (e : V) (env : Nat → V)
    (i j : Nat) :
    Tarski.Sat mem (pointed e env) (namedOutgoing i j) ↔
      Outgoing mem (env i) (env j) :=
  Iff.rfl

/-- Both occurrences and binders shift; equality introduces only the local
reserved-zero comparison, and Bottom becomes the designated atom R(0,0). -/
def translate : Tarski.NF → Tarski.NF
  | .rel i j => .rel (i + 1) (j + 1)
  | .eq i j => namedOutgoing i j
  | .bot => .rel 0 0
  | .imp a b => .imp (translate a) (translate b)
  | .all i a => .all (i + 1) (translate a)

/-- The target contains only membership, implication and forall. -/
def MembershipOnly : Tarski.NF → Prop
  | .rel _ _ => True
  | .eq _ _ | .bot => False
  | .imp a b => MembershipOnly a ∧ MembershipOnly b
  | .all _ a => MembershipOnly a

theorem translate_membershipOnly (f : Tarski.NF) : MembershipOnly (translate f) := by
  induction f with
  | rel _ _ => trivial
  | eq _ _ => exact ⟨True.intro, True.intro⟩
  | bot => trivial
  | imp _ _ iha ihb => exact ⟨iha, ihb⟩
  | all _ _ ih => exact ih

/-- Semantic translation for every named formula, with a fixed false point.
The premise is local at e; global irreflexivity is unnecessary. -/
theorem sat_translate (mem : V → V → Prop) (hTwins : TwinSingletons mem)
    (e : V) (hFalse : ¬ mem e e) (f : Tarski.NF) (env : Nat → V) :
    Tarski.Sat mem (pointed e env) (translate f) ↔ FullSat mem env f := by
  induction f generalizing env with
  | rel i j => rfl
  | eq i j =>
    exact (sat_namedOutgoing mem e env i j).trans
      (outgoing_iff_full mem hTwins (env i) (env j))
  | bot => exact ⟨fun h => (hFalse h).elim, fun h => h.elim⟩
  | imp a b iha ihb => exact imp_congr (iha env) (ihb env)
  | all i a ih =>
    change (∀ d, Tarski.Sat mem (Tarski.update (pointed e env) (i + 1) d) (translate a)) ↔
      ∀ d, FullSat mem (Tarski.update env i d) a
    apply forall_congr'
    intro d
    rw [pointed_update]
    exact ih (Tarski.update env i d)

/-- Actual raw PSC supplies one empty point for the simultaneous translation
of all formulas and environments. This does not assert a full interpretation
of the EPSC axiom schema or a derivation/numerical transport theorem. -/
theorem translation_of_model (mem : V → V → Prop) (witness : V)
    (hModel : RawPSCModel.ModelsRawPSC mem) :
    ∃ e, (∀ z, ¬ mem z e) ∧ ∀ f env,
      (Tarski.Sat mem (pointed e env) (translate f) ↔ FullSat mem env f) := by
  obtain ⟨e, he⟩ := RawPSCModel.empty_of_model mem witness hModel
  exact ⟨e, he, fun f env => sat_translate mem
    (RawPSCModel.twins_of_model mem witness hModel) e (he e) f env⟩

end SetTheory.BusyBeaver.ZFC.OutgoingProfile

#print axioms SetTheory.BusyBeaver.ZFC.OutgoingProfile.outgoing_iff_full
#print axioms SetTheory.BusyBeaver.ZFC.OutgoingProfile.outgoing_mem_congr
#print axioms SetTheory.BusyBeaver.ZFC.OutgoingProfile.sat_outgoingForm
#print axioms SetTheory.BusyBeaver.ZFC.OutgoingProfile.outgoingForm_four_nodes
#print axioms SetTheory.BusyBeaver.ZFC.OutgoingProfile.outgoing_iff_full_of_model
#print axioms SetTheory.BusyBeaver.ZFC.OutgoingProfile.sat_outgoingForm_full_of_model
#print axioms SetTheory.BusyBeaver.ZFC.OutgoingProfile.pointed_update
#print axioms SetTheory.BusyBeaver.ZFC.OutgoingProfile.sat_namedOutgoing
#print axioms SetTheory.BusyBeaver.ZFC.OutgoingProfile.translate_membershipOnly
#print axioms SetTheory.BusyBeaver.ZFC.OutgoingProfile.sat_translate
#print axioms SetTheory.BusyBeaver.ZFC.OutgoingProfile.translation_of_model
