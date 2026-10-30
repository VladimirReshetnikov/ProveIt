import BusyBeaver.ZFC.WellFoundedPartCore

/-!
Actual first-order formula relativization to the internally well-founded part.

The domain and its ambient defining formula are those of WellFoundedPart,
following the attributed well-founded-part interpretation in the pinned
busy-beaver source ZF/stdzf_r3/regcon/WF.v, upstream
297ab8df7e5de329605c3875b4934643b371a5e3. Quantifiers in the translated input
formula are guarded by the ambient wfForm; that defining guard is not itself
relativized. Atomic membership and logical equality keep their original slots.

This is a semantic formula adapter for any relation, with no model axioms,
nonempty-domain premise, choice of representatives or external well-foundedness
assumption. It does not by itself transport the set-theoretic axioms, establish
a ZF model, or prove a consistency comparison or machine endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.WFRelativization

open Form WellFoundedPart DeepPositiveClosure

universe u
variable {V : Type u}

/-- Every original De Bruijn slot is retained. The inserted guard refers to
the new bound variable at slot0 and is evaluated in the ambient structure. -/
def translate : Form → Form
  | fMem i j => fMem i j
  | fEq i j => fEq i j
  | fBot => fBot
  | fImp a b => fImp (translate a) (translate b)
  | fAnd a b => fAnd (translate a) (translate b)
  | fOr a b => fOr (translate a) (translate b)
  | fAll a => fAll (fImp (wfForm 0) (translate a))
  | fEx a => fEx (fAnd (wfForm 0) (translate a))

/-- Parameters are the underlying values of the supplied WF-domain objects;
no arbitrary ambient representative is selected. -/
def liftEnv (mem : V → V → Prop) (env : Nat → Domain mem) : Nat → V :=
  fun i => (env i).val

theorem liftEnv_scons (mem : V → V → Prop) (x : Domain mem)
    (env : Nat → Domain mem) :
    liftEnv mem (scons x env) = scons x.val (liftEnv mem env) := by
  funext n
  cases n <;> rfl

def envOfWF (mem : V → V → Prop) (env : Nat → V)
    (hWF : ∀ i, WF mem (env i)) : Nat → Domain mem :=
  fun i => ⟨env i, hWF i⟩

theorem liftEnv_envOfWF (mem : V → V → Prop) (env : Nat → V)
    (hWF : ∀ i, WF mem (env i)) :
    liftEnv mem (envOfWF mem env hWF) = env := rfl

theorem sat_guard (mem : V → V → Prop) (env : Nat → V) (x : V) :
    Sat mem (scons x env) (wfForm 0) ↔ WF mem x :=
  sat_wfForm mem (scons x env) 0

/-- Satisfaction in the actual WF subtype agrees with ambient satisfaction
of the translated actual Form, including arbitrary parameter valuations. -/
theorem sat_translate (mem : V → V → Prop) (phi : Form) :
    ∀ env : Nat → Domain mem,
      Sat mem (liftEnv mem env) (translate phi) ↔ Sat (domainMem mem) env phi := by
  induction phi with
  | fMem i j => intro env; rfl
  | fEq i j =>
    intro env
    change (env i).val = (env j).val ↔ env i = env j
    constructor
    · exact Subtype.ext
    · exact congrArg Subtype.val
  | fBot => intro env; rfl
  | fImp a b iha ihb =>
    intro env
    exact imp_congr (iha env) (ihb env)
  | fAnd a b iha ihb =>
    intro env
    exact and_congr (iha env) (ihb env)
  | fOr a b iha ihb =>
    intro env
    exact or_congr (iha env) (ihb env)
  | fAll a ih =>
    intro env
    change (∀ x : V, Sat mem (scons x (liftEnv mem env)) (wfForm 0) →
      Sat mem (scons x (liftEnv mem env)) (translate a)) ↔
        ∀ x : Domain mem, Sat (domainMem mem) (scons x env) a
    constructor
    · intro h x
      apply (ih (scons x env)).mp
      rw [liftEnv_scons]
      exact h x.val ((sat_guard mem (liftEnv mem env) x.val).mpr x.property)
    · intro h x hx
      let y : Domain mem := ⟨x, (sat_guard mem (liftEnv mem env) x).mp hx⟩
      have hy := (ih (scons y env)).mpr (h y)
      rwa [liftEnv_scons] at hy
  | fEx a ih =>
    intro env
    change (∃ x : V, Sat mem (scons x (liftEnv mem env)) (wfForm 0) ∧
      Sat mem (scons x (liftEnv mem env)) (translate a)) ↔
        ∃ x : Domain mem, Sat (domainMem mem) (scons x env) a
    constructor
    · rintro ⟨x, hx, ha⟩
      let y : Domain mem := ⟨x, (sat_guard mem (liftEnv mem env) x).mp hx⟩
      refine ⟨y, (ih (scons y env)).mp ?_⟩
      rw [liftEnv_scons]
      exact ha
    · rintro ⟨x, hx⟩
      refine ⟨x.val, (sat_guard mem (liftEnv mem env) x.val).mpr x.property, ?_⟩
      have ha := (ih (scons x env)).mpr hx
      rwa [liftEnv_scons] at ha

theorem sat_translate_of_wf (mem : V → V → Prop) (phi : Form)
    (env : Nat → V) (hWF : ∀ i, WF mem (env i)) :
    Sat mem env (translate phi) ↔
      Sat (domainMem mem) (envOfWF mem env hWF) phi := by
  exact sat_translate mem phi (envOfWF mem env hWF)

/-- The unary Separation matrix convention: its tested element occupies0. -/
theorem sat_translate_scons (mem : V → V → Prop) (phi : Form)
    (env : Nat → Domain mem) (x : Domain mem) :
    Sat mem (scons x.val (liftEnv mem env)) (translate phi) ↔
      Sat (domainMem mem) (scons x env) phi := by
  rw [← liftEnv_scons]
  exact sat_translate mem phi (scons x env)

/-- The inherited matrix convention has first argument0 and second argument1. -/
theorem sat_translate_matrix (mem : V → V → Prop) (phi : Form)
    (env : Nat → Domain mem) (x y : Domain mem) :
    MatrixRelation mem (translate phi) (liftEnv mem env) x.val y.val ↔
      MatrixRelation (domainMem mem) phi env x y := by
  change Sat mem (scons x.val (scons y.val (liftEnv mem env))) (translate phi) ↔ _
  rw [← liftEnv_scons mem y env, ← liftEnv_scons mem x (scons y env)]
  exact sat_translate mem phi (scons x (scons y env))

/-- The repository Replacement convention is output0,input1, written y,x. -/
theorem sat_translate_relOf (mem : V → V → Prop) (phi : Form)
    (env : Nat → Domain mem) (y x : Domain mem) :
    relOf mem (translate phi) (liftEnv mem env) y.val x.val ↔
      relOf (domainMem mem) phi env y x :=
  sat_translate_matrix mem phi env y x

/-- Relativization preserves precisely the original use of equality;
the inserted WF guards themselves are equality-free. -/
theorem equalityFree_translate (phi : Form) :
    EqualityFree (translate phi) ↔ EqualityFree phi := by
  induction phi with
  | fMem i j => rfl
  | fEq i j => rfl
  | fBot => rfl
  | fImp a b iha ihb => exact and_congr iha ihb
  | fAnd a b iha ihb => exact and_congr iha ihb
  | fOr a b iha ihb => exact and_congr iha ihb
  | fAll a ih =>
    change (EqualityFree (wfForm 0) ∧ EqualityFree (translate a)) ↔ EqualityFree a
    constructor
    · intro h; exact ih.mp h.2
    · intro h; exact ⟨equalityFree_wfForm 0, ih.mpr h⟩
  | fEx a ih =>
    change (EqualityFree (wfForm 0) ∧ EqualityFree (translate a)) ↔ EqualityFree a
    constructor
    · intro h; exact ih.mp h.2
    · intro h; exact ⟨equalityFree_wfForm 0, ih.mpr h⟩

end SetTheory.BusyBeaver.ZFC.WFRelativization
