/-!
A relational calculus for locally closed certificates.
No assumption of finiteness, well-foundedness, or standardness of the item
or certificate types is made. This is a mechanism prototype, not an
integration into the internal set-theory modules.
-/
namespace CertificateClosure

universe u v

structure Operations (Item : Type u) (Cert : Type v) where
  mem : Item → Cert → Prop
  empty : Cert
  join : Cert → Cert → Cert
  singleton : Item → Cert
  mem_empty : ∀ x, ¬ mem x empty
  mem_join : ∀ x S T, mem x (join S T) ↔ mem x S ∨ mem x T
  mem_singleton : ∀ x y, mem x (singleton y) ↔ x = y

variable {Item : Type u} {Cert : Type v} (O : Operations Item Cert)

abbrev Included (S T : Cert) : Prop := ∀ x, O.mem x S → O.mem x T

def Closed (Good : Item → Prop) (Step : Cert → Item → Prop) (S : Cert) : Prop :=
  ∀ x, O.mem x S → Good x ∧ Step S x

variable {O} {Good : Item → Prop} {Step : Cert → Item → Prop}

/-- Only the step predicate is monotone; closed certificates are not in
    general upward-closed under arbitrary enlargement. -/
def StepMonotone : Prop :=
  ∀ {S T}, Included O S T → ∀ {x}, Step S x → Step T x

theorem closed_empty : Closed O Good Step O.empty := by
  intro x hx
  exact False.elim (O.mem_empty x hx)

theorem closed_join (mono : StepMonotone (O := O) (Step := Step))
    {S T : Cert} (hS : Closed O Good Step S) (hT : Closed O Good Step T) :
    Closed O Good Step (O.join S T) := by
  intro x hx
  rcases (O.mem_join x S T).mp hx with hx | hx
  · exact ⟨(hS x hx).1, mono (fun y hy => (O.mem_join y S T).mpr (Or.inl hy)) (hS x hx).2⟩
  · exact ⟨(hT x hx).1, mono (fun y hy => (O.mem_join y S T).mpr (Or.inr hy)) (hT x hx).2⟩

theorem closed_insert (mono : StepMonotone (O := O) (Step := Step))
    {S : Cert} {x : Item} (hS : Closed O Good Step S)
    (hg : Good x) (hs : Step S x) : Closed O Good Step (O.join S (O.singleton x)) := by
  have inc : Included O S (O.join S (O.singleton x)) :=
    fun y hy => (O.mem_join y S (O.singleton x)).mpr (Or.inl hy)
  intro y hy
  rcases (O.mem_join y S (O.singleton x)).mp hy with hy | hy
  · exact ⟨(hS y hy).1, mono inc (hS y hy).2⟩
  · have he : y = x := (O.mem_singleton y x).mp hy
    subst y
    exact ⟨hg, mono inc hs⟩

def Certified (O : Operations Item Cert) (Good : Item → Prop)
    (Step : Cert → Item → Prop) (x : Item) : Prop :=
  ∃ S, Closed O Good Step S ∧ O.mem x S

theorem certified_of_step (mono : StepMonotone (O := O) (Step := Step))
    {S : Cert} {x : Item} (hS : Closed O Good Step S)
    (hg : Good x) (hs : Step S x) : Certified O Good Step x := by
  exact ⟨O.join S (O.singleton x), closed_insert mono hS hg hs,
    (O.mem_join x S (O.singleton x)).mpr
      (Or.inr ((O.mem_singleton x x).mpr rfl))⟩

theorem certified_good {x : Item} (h : Certified O Good Step x) : Good x := by
  obtain ⟨S, hS, hx⟩ := h
  exact (hS x hx).1

#print axioms closed_join
#print axioms closed_insert
#print axioms certified_of_step
end CertificateClosure
