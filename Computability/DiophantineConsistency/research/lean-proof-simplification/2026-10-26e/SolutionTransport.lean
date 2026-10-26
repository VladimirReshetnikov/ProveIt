/-!
Proof-only proposal: transport guarded solution predicates without asserting
that witness maps are bijections. This file uses only Lean's core library.
Compilation status is recorded separately in VALIDATION.json.
-/
namespace ProofSimplification

universe u v w

def HasSolution {A : Sort u} (domain equation : A → Prop) : Prop :=
  ∃ x, domain x ∧ equation x

theorem hasSolution_congr {A : Sort u} {domain P Q : A → Prop}
    (h : ∀ x, domain x → (P x ↔ Q x)) :
    HasSolution domain P ↔ HasSolution domain Q :=
  ⟨fun ⟨x, hx, hp⟩ => ⟨x, hx, (h x hx).mp hp⟩,
   fun ⟨x, hx, hq⟩ => ⟨x, hx, (h x hx).mpr hq⟩⟩

/-- A semantic relation between solutions, not an equality or bijection of
assignments. It permits fresh seeds, auxiliary witnesses and many-to-one maps. -/
structure SolutionTransport {A : Sort u} {B : Sort v}
    (DA PA : A → Prop) (DB PB : B → Prop) : Prop where
  forward : ∀ x, DA x → PA x → ∃ y, DB y ∧ PB y
  backward : ∀ y, DB y → PB y → ∃ x, DA x ∧ PA x

theorem SolutionTransport.exists_iff {A : Sort u} {B : Sort v}
    {DA PA : A → Prop} {DB PB : B → Prop}
    (h : SolutionTransport DA PA DB PB) :
    HasSolution DA PA ↔ HasSolution DB PB :=
  ⟨fun ⟨x, hx, hp⟩ => h.forward x hx hp,
   fun ⟨y, hy, hq⟩ => h.backward y hy hq⟩

def SolutionTransport.trans {A : Sort u} {B : Sort v} {C : Sort w}
    {DA PA : A → Prop} {DB PB : B → Prop} {DC PC : C → Prop}
    (h : SolutionTransport DA PA DB PB)
    (k : SolutionTransport DB PB DC PC) : SolutionTransport DA PA DC PC where
  forward := fun x hx hp =>
    match h.forward x hx hp with
    | ⟨y, hy, hq⟩ => k.forward y hy hq
  backward := fun z hz hr =>
    match k.backward z hz hr with
    | ⟨y, hy, hq⟩ => h.backward y hy hq

#print axioms hasSolution_congr
#print axioms SolutionTransport.exists_iff
#print axioms SolutionTransport.trans

end ProofSimplification
