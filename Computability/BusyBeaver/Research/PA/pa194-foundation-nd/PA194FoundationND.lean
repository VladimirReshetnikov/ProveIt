import PA194FoundationLK
import PA194SourceAdjunctionConditional
namespace M6.PA.RelationalSource.ND
open LO LO.FirstOrder

abbrev Proof (Γ : List Form) (p : Form) := LO.FirstOrder.Derivation (p :: Γ.map Semiformula.neg)

def assumption {Γ : List Form} {p : Form} (h : p ∈ Γ) : Proof Γ p := by
  refine LO.FirstOrder.Derivation.contraction (LO.FirstOrder.Derivation.eta p) ?_
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · simp
  · simp only [List.mem_cons, List.mem_map]
    right
    exact ⟨p,h,Semiformula.neg_eq p⟩

def weaken {Γ Δ : List Form} {p : Form} (d : Proof Γ p) (h : ∀ q,q ∈ Γ → q ∈ Δ) : Proof Δ p := by
  refine LO.FirstOrder.Derivation.contraction d ?_
  intro q hq
  simp only [List.mem_cons, List.mem_map] at hq ⊢
  rcases hq with hp | ⟨r,hr,he⟩
  · exact Or.inl hp
  · exact Or.inr ⟨r,h r hr,he⟩

def closed {Γ : List Form} {p : Form} (d : LO.FirstOrder.Derivation [p]) : Proof Γ p :=
  d.contra (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; simp [hq])

def mp {Γ : List Form} {p q : Form} (d : Proof Γ p) (e : Proof Γ (p 🡒 q)) : Proof Γ q := by
  let N := Γ.map Semiformula.neg
  have hp : LO.FirstOrder.Derivation (p :: ∼p :: q :: N) :=
    (LO.FirstOrder.Derivation.eta p).contra (by simp)
  have hq : LO.FirstOrder.Derivation (∼q :: ∼p :: q :: N) :=
    (LO.FirstOrder.Derivation.eta q).contra (by simp)
  have hn : LO.FirstOrder.Derivation (∼(p 🡒 q) :: ∼p :: q :: N) := by
    simpa [Semiformula.imp_eq, Semiformula.neg_eq, Semiformula.neg, Semiformula.neg_neg] using LO.FirstOrder.Derivation.and hp hq
  have hc := LO.FirstOrder.Derivation.cut e hn
  have hc' : LO.FirstOrder.Derivation (∼p :: q :: N) := hc.contra (by intro x hx; dsimp [N] at *; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)
  have hr := LO.FirstOrder.Derivation.cut d hc'
  exact hr.contra (by intro x hx; dsimp [N] at *; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)

def impIntro {Γ : List Form} {p q : Form} (d : Proof (p::Γ) q) : Proof Γ (p 🡒 q) := by
  have h : LO.FirstOrder.Derivation (∼p :: q :: Γ.map Semiformula.neg) :=
    d.contra (by simp [Semiformula.neg_eq])
  exact LO.FirstOrder.Derivation.or h

def andIntro {Γ : List Form} {p q : Form} (d : Proof Γ p) (e : Proof Γ q) : Proof Γ (p ⋏ q) :=
  LO.FirstOrder.Derivation.and d e

def andLeft {Γ : List Form} {p q : Form} (d : Proof Γ (p ⋏ q)) : Proof Γ p := by
  let N := Γ.map Semiformula.neg
  have h : LO.FirstOrder.Derivation (∼p :: ∼q :: [p]) := (LO.FirstOrder.Derivation.eta p).contra (by simp)
  have j : LO.FirstOrder.Derivation (∼(p ⋏ q) :: [p]) := by
    simpa [Semiformula.neg_eq, Semiformula.neg] using LO.FirstOrder.Derivation.or h
  have k := LO.FirstOrder.Derivation.cut d j
  exact k.contra (by intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)

def andRight {Γ : List Form} {p q : Form} (d : Proof Γ (p ⋏ q)) : Proof Γ q := by
  have h : LO.FirstOrder.Derivation (∼p :: ∼q :: [q]) := (LO.FirstOrder.Derivation.eta q).contra (by simp)
  have j : LO.FirstOrder.Derivation (∼(p ⋏ q) :: [q]) := by
    simpa [Semiformula.neg_eq, Semiformula.neg] using LO.FirstOrder.Derivation.or h
  have k := LO.FirstOrder.Derivation.cut d j
  exact k.contra (by intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)

def orLeft {Γ : List Form} {p q : Form} (d : Proof Γ p) : Proof Γ (p ⋎ q) := by
  have h : LO.FirstOrder.Derivation (p :: q :: Γ.map Semiformula.neg) := d.contra (by simp)
  exact LO.FirstOrder.Derivation.or h

def orRight {Γ : List Form} {p q : Form} (d : Proof Γ q) : Proof Γ (p ⋎ q) := by
  have h : LO.FirstOrder.Derivation (p :: q :: Γ.map Semiformula.neg) := d.contra (by simp)
  exact LO.FirstOrder.Derivation.or h

def botElim {Γ : List Form} {p : Form} (d : Proof Γ ⊥) : Proof Γ p := by
  have h : LO.FirstOrder.Derivation (⊤ :: [p]) := LO.FirstOrder.Derivation.verum.contra (by simp)
  have k := LO.FirstOrder.Derivation.cut h d
  exact k.contra (by intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)

def contradiction {Γ : List Form} {p : Form} (d : Proof Γ p) (e : Proof Γ (∼p)) : Proof Γ ⊥ := by
  have k := LO.FirstOrder.Derivation.cut d e
  exact k.contra (by intro x hx; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)

def byContradiction {Γ : List Form} {p : Form} (d : Proof (∼p::Γ) ⊥) : Proof Γ p := by
  have h : LO.FirstOrder.Derivation (⊥ :: p :: Γ.map Semiformula.neg) := by
    simpa [Proof, Semiformula.neg_eq, Semiformula.neg_neg] using d
  have k := LO.FirstOrder.Derivation.cut LO.FirstOrder.Derivation.verum h
  exact k.contra (by simp)

def orElim {Γ : List Form} {p q r : Form} (d : Proof Γ (p ⋎ q))
    (dp : Proof (p::Γ) r) (dq : Proof (q::Γ) r) : Proof Γ r := by
  have hp : LO.FirstOrder.Derivation (∼p :: r :: Γ.map Semiformula.neg) :=
    dp.contra (by simp [Semiformula.neg_eq])
  have hq : LO.FirstOrder.Derivation (∼q :: r :: Γ.map Semiformula.neg) :=
    dq.contra (by simp [Semiformula.neg_eq])
  have hn : LO.FirstOrder.Derivation (∼(p ⋎ q) :: r :: Γ.map Semiformula.neg) := by
    simpa [Semiformula.neg_eq, Semiformula.neg] using LO.FirstOrder.Derivation.and hp hq
  have k := LO.FirstOrder.Derivation.cut d hn
  exact k.contra (by intro x hx; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)

def shifted (Γ : List Form) := Γ.map Semiformula.shift

def allIntro {Γ : List Form} {p : Semiproposition language 1}
    (d : Proof (shifted Γ) p.free) : Proof Γ (∀⁰ p) := by
  apply LO.FirstOrder.Derivation.all
  simpa [Proof, shifted, Rewriting.shifts, List.map_map, Function.comp_def,
    Semiformula.shift, ← Semiformula.neg_eq] using d

def allElim {Γ : List Form} (p : Semiproposition language 1) (t : Semiterm language Nat 0)
    (d : Proof Γ (∀⁰ p)) : Proof Γ (p/[t]) := by
  have hi : LO.FirstOrder.Derivation ((∼p)/[t] :: [p/[t]]) := by
    have eq1 : (∼p)/[t] = ∼(p/[t]) := by
      change Semiformula.rewAux _ (∼p) = _
      exact Semiformula.rewAux_neg _ _
    rw [eq1]
    exact (LO.FirstOrder.Derivation.eta (p/[t])).rotate
  have hn : LO.FirstOrder.Derivation (∼(∀⁰ p) :: [p/[t]]) := by
    rw [Semiformula.neg_all]
    exact LO.FirstOrder.Derivation.exs (φ := ∼p) (t := t) hi
  have k := LO.FirstOrder.Derivation.cut d hn
  exact k.contra (by intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)

def exsIntro {Γ : List Form} (p : Semiproposition language 1) (t : Semiterm language Nat 0)
    (d : Proof Γ (p/[t])) : Proof Γ (∃⁰ p) := LO.FirstOrder.Derivation.exs d

def exsElim {Γ : List Form} {p : Semiproposition language 1} {q : Form}
    (d : Proof Γ (∃⁰ p)) (e : Proof (p.free :: shifted Γ) q.shift) : Proof Γ q := by
  have he : LO.FirstOrder.Derivation ((∼p).free :: Rewriting.shifts (q :: Γ.map Semiformula.neg)) := by
    refine LO.FirstOrder.Derivation.contraction e ?_
    intro x hx
    simp only [Proof, shifted, List.map_cons, List.map_map, Function.comp_def, Rewriting.shifts, List.mem_cons,
      List.mem_map] at hx ⊢
    rcases hx with h | h | ⟨a,ha,h⟩
    · exact Or.inr (Or.inl h)
    · left
      have heq : (∼p).free = ∼p.free := by
        change Semiformula.rewAux _ (∼p) = _
        exact Semiformula.rewAux_neg _ _
      rw [heq]
      simpa only [Semiformula.neg_eq] using h
    · right; right
      exact ⟨a,ha,by simpa [Semiformula.shift, ← Semiformula.neg_eq] using h⟩
  have hn : LO.FirstOrder.Derivation (∼(∃⁰ p) :: q :: Γ.map Semiformula.neg) := by
    rw [Semiformula.neg_ex]
    exact LO.FirstOrder.Derivation.all he
  have k := LO.FirstOrder.Derivation.cut d hn
  exact k.contra (by intro x hx; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)

#print axioms allElim
#print axioms exsElim
#print axioms mp
#print axioms orElim
#print axioms andLeft
#print axioms assumption
#print axioms weaken
end M6.PA.RelationalSource.ND
