import BusyBeaver.ZFC.ProfileModel

/-!
The explicit finite equality resource needed for one reverse model adapter.

Outgoing-profile faithfulness identifies objects with the same receiving
sets. Under this hypothesis, native equality in any actual Form can be
replaced by an equality-free outgoing-profile biconditional. Literal
equality-free GIC instances then supply all actual Form GIC instances.

Faithfulness is an explicit extra premise. Neither equality-free CP/GIC nor
ZF0 is assumed to supply it here. Actual singleton existence, and hence
ordinary native-equality Pairing, is a separate sufficient resource.
-/

namespace SetTheory.BusyBeaver.ZFC.EqualityGIC

open DeepPositiveClosure ProfileSyntax ProfileCollection ProfileModel

universe u
variable {V : Type u}

def Faithful (mem : V → V → Prop) : Prop :=
  ∀ x y, (∀ z, mem x z ↔ mem y z) → x = y

/-- A single finite sentence, with native equality only in the conclusion. -/
def faithfulForm : Form :=
  .fAll (.fAll (.fImp
    (.fAll (fIff (.fMem 2 0) (.fMem 1 0))) (.fEq 1 0)))

theorem sat_faithfulForm (mem : V → V → Prop) (env : Nat → V) :
    Sat mem env faithfulForm ↔ Faithful mem := by
  constructor
  · intro h x y hxy
    exact h x y (fun z => Sat_fIff.mpr (hxy z))
  · intro h x y hxy
    exact h x y (fun z => Sat_fIff.mp (hxy z))

/-- Equality of outgoing profiles; both endpoints shift under the binder.
This is the biconditional form of the two outgoing-inclusion directions. -/
def equalityForm (i j : Nat) : Form :=
  .fAll (fIff (.fMem (i + 1) 0) (.fMem (j + 1) 0))

theorem equalityFree_equalityForm (i j : Nat) : EqualityFree (equalityForm i j) :=
  ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩

theorem sat_equalityForm (mem : V → V → Prop) (hFaith : Faithful mem)
    (env : Nat → V) (i j : Nat) :
    Sat mem env (equalityForm i j) ↔ env i = env j := by
  constructor
  · intro h
    exact hFaith (env i) (env j) (fun z => Sat_fIff.mp (h z))
  · intro h z
    apply Sat_fIff.mpr
    change mem (env i) z ↔ mem (env j) z
    rw [h]

/-- All ordinary constructors are retained; only native equality is expanded. -/
def eraseEquality : Form → Form
  | .fMem i j => .fMem i j
  | .fEq i j => equalityForm i j
  | .fBot => .fBot
  | .fImp phi psi => .fImp (eraseEquality phi) (eraseEquality psi)
  | .fAnd phi psi => .fAnd (eraseEquality phi) (eraseEquality psi)
  | .fOr phi psi => .fOr (eraseEquality phi) (eraseEquality psi)
  | .fAll phi => .fAll (eraseEquality phi)
  | .fEx phi => .fEx (eraseEquality phi)

theorem equalityFree_eraseEquality (phi : Form) : EqualityFree (eraseEquality phi) := by
  induction phi with
  | fMem i j => trivial
  | fEq i j => exact equalityFree_equalityForm i j
  | fBot => trivial
  | fImp phi psi hp hq => exact ⟨hp, hq⟩
  | fAnd phi psi hp hq => exact ⟨hp, hq⟩
  | fOr phi psi hp hq => exact ⟨hp, hq⟩
  | fAll phi hp => exact hp
  | fEx phi hp => exact hp

theorem sat_eraseEquality (mem : V → V → Prop) (hFaith : Faithful mem)
    (phi : Form) (env : Nat → V) :
    Sat mem env (eraseEquality phi) ↔ Sat mem env phi := by
  induction phi generalizing env with
  | fMem i j => rfl
  | fEq i j => exact sat_equalityForm mem hFaith env i j
  | fBot => rfl
  | fImp phi psi hp hq => exact imp_congr (hp env) (hq env)
  | fAnd phi psi hp hq => exact and_congr (hp env) (hq env)
  | fOr phi psi hp hq => exact or_congr (hp env) (hq env)
  | fAll phi hp => exact forall_congr' (fun x => hp (scons x env))
  | fEx phi hp => exact exists_congr (fun x => hp (scons x env))

/-- The supplied relation is defined by an actual translated matrix. -/
theorem collection_of_matrix (mem : V → V → Prop) (hFaith : Faithful mem)
    (hGIC : ModelsGIC mem) (phi : Form) (env : Nat → V) :
    CollectionInstance mem (MatrixRelation mem phi env) := by
  exact instance_of_matrix mem hGIC (eraseEquality phi)
    (equalityFree_eraseEquality phi) env _
    (fun x y => sat_eraseEquality mem hFaith phi (scons x (scons y env)))

/-- Full GIC still ranges only over actual Form matrices and valuations. -/
theorem modelsFullGIC (mem : V → V → Prop) (hFaith : Faithful mem)
    (hGIC : ModelsGIC mem) :
    ∀ phi env, Sat mem env (gicForm phi) := by
  intro phi env
  exact (sat_gicForm mem phi env).mpr (collection_of_matrix mem hFaith hGIC phi env)

theorem faithful_of_singletons (mem : V → V → Prop)
    (hSingleton : ∀ x, ∃ s, ∀ y, mem y s ↔ y = x) : Faithful mem := by
  intro x y hxy
  obtain ⟨s, hs⟩ := hSingleton x
  have hx : mem x s := (hs x).mpr rfl
  exact ((hs y).mp ((hxy s).mp hx)).symm

theorem faithful_of_pairing (mem : V → V → Prop)
    (hPair : ∀ x y, ∃ p, ∀ z, mem z p ↔ z = x ∨ z = y) : Faithful mem := by
  apply faithful_of_singletons mem
  intro x
  obtain ⟨s, hs⟩ := hPair x x
  refine ⟨s, fun y => ⟨?_, ?_⟩⟩
  · intro hy
    exact ((hs y).mp hy).elim id id
  · intro hy
    exact (hs y).mpr (Or.inl hy)

end SetTheory.BusyBeaver.ZFC.EqualityGIC
