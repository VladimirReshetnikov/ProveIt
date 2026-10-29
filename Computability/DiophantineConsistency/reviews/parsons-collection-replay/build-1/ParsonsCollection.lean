import DiophantineConsistency.ParsonsPrenex
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsCollection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsPrenex
variable {L : Language} [L.ORing]

def unbounded (D : Semiproposition L 2) (n : SyntacticTerm L) : Proposition L :=
  “∀ i < !!n, ∃ y, !D i y”
def bounded (D : Semiproposition L 2) (n B : SyntacticTerm L) : Proposition L :=
  let B₁ : Semiterm L ℕ 1 := Rew.bShift B
  “∀ i < !!n, ∃ y < !!B₁, !D i y”
def collection (D : Semiproposition L 2) (n : SyntacticTerm L) : Proposition L :=
  let n₁ : Semiterm L ℕ 1 := Rew.bShift n
  “∃ b, ∀ i < !!n₁, ∃ y < b, !D i y”

def all_mono (A B : Semiproposition L 1)
    (d : Derivation [∼A.free, B.free]) : Derivation [∼(∀⁰ A), ∀⁰ B] := by
  have h0 : Derivation [(∼(Rewriting.shift A))/[&0], B.free] := by simpa using d
  have h1 : Derivation [∃⁰ ∼(Rewriting.shift A), B.free] := h0.exs
  have h2 : Derivation (B.free :: [∼(∀⁰ A)]⁺) := by
    simpa [Rewriting.shifts] using h1.contra
      (Γ := [B.free, ∃⁰ ∼(Rewriting.shift A)]) (by simp)
  exact h2.all.contra (by simp)

/-- Existential witnesses can discard any additional conjunct. -/
def erase_bound (R D : Semiproposition L 1) :
    Derivation [∼(∃⁰ (R ⋏ D)), ∃⁰ D] := by
  have h0 : Derivation [∼D.free, D.free, ∼R.free] := Derivation.close D.free (by simp) (by simp)
  have h1 : Derivation [∼R.free, ∼D.free, D.free] := h0.contra (by simp)
  have h2 : Derivation [∼(R ⋏ D).free, D.free] := by
    simpa using h1.or
  exact exists_mono (R ⋏ D) D h2

/-- Logical transport of an implication under a common antecedent. -/
def guarded_mono (K A B : Proposition L) (d : Derivation [∼A, B]) :
    Derivation [∼(K 🡒 A), K 🡒 B] := by
  have hK : Derivation [K, ∼K, B] := Derivation.close K (by simp) (by simp)
  have hA : Derivation [∼A, ∼K, B] := d.contra (by simp)
  have h : Derivation [∼(K 🡒 A), ∼K, B] := by
    simpa [Semiformula.imp_eq] using hK.and hA
  have h' : Derivation [∼K, B, ∼(K 🡒 A)] := h.contra (by simp)
  simpa [Semiformula.imp_eq] using h'.or.contra
    (Γ := [∼(K 🡒 A), (∼K) ⋎ B]) (by simp)

def leftBody (K : Semiproposition L 1) (R D : Semiproposition L 2) : Semiproposition L 1 :=
  K 🡒 (∃⁰ (R ⋏ D))
def rightBody (K : Semiproposition L 1) (D : Semiproposition L 2) : Semiproposition L 1 :=
  K 🡒 (∃⁰ D)

/-- The fixed-bound reverse direction of collection, with arbitrary outer
and witness guards, is pure LK. -/
def fixed_bound_reverse (K : Semiproposition L 1) (R D : Semiproposition L 2) :
    Derivation [(∀⁰ leftBody K R D) 🡒 (∀⁰ rightBody K D)] := by
  have h : Derivation [∼(leftBody K R D).free, (rightBody K D).free] := by
    have he := erase_bound R.free D.free
    have hm := guarded_mono K.free (∃⁰ (R.free ⋏ D.free)) (∃⁰ D.free) he
    simpa [leftBody, rightBody, ← TransitiveRewriting.comp_app] using hm
  have hm := all_mono (leftBody K R D) (rightBody K D) h
  simpa [Semiformula.imp_eq] using hm.or

def witnessGuard (B : SyntacticTerm L) : Semiproposition L 2 := by
  let B₂ : Semiterm L ℕ 2 := Rew.bShift (Rew.bShift B)
  exact “y i. y < !!B₂”

def outerGuard (n : SyntacticTerm L) : Semiproposition L 1 := by
  let n₁ : Semiterm L ℕ 1 := Rew.bShift n
  exact “i. i < !!n₁”

theorem fixed_left_eq (D : Semiproposition L 2) (n B : SyntacticTerm L) :
    (∀⁰ leftBody (outerGuard n) (witnessGuard B) (D ⇜ ![#1, #0])) = bounded D n B := by
  simp [leftBody, outerGuard, witnessGuard, bounded, Semiformula.ballLT, Semiformula.bexsLT, ball, bexs]

theorem fixed_right_eq (D : Semiproposition L 2) (n : SyntacticTerm L) :
    (∀⁰ rightBody (outerGuard n) (D ⇜ ![#1, #0])) = unbounded D n := by
  simp [rightBody, outerGuard, unbounded, Semiformula.ballLT, ball]

/-- Removing a fixed bound is proved in the rule calculus for every D,n,B. -/
def fixed_bound_proof {T : Theory L} (D : Semiproposition L 2) (n B : SyntacticTerm L) :
    Proof T (bounded D n B 🡒 unbounded D n) := by
  apply Proof.logical
  simpa [fixed_left_eq, fixed_right_eq] using fixed_bound_reverse (outerGuard n) (witnessGuard B) (D ⇜ ![#1, #0])

def collectionBody (D : Semiproposition L 2) (n : SyntacticTerm L) : Semiproposition L 1 := by
  let n₁ : Semiterm L ℕ 1 := Rew.bShift n
  exact “b. ∀ i < !!n₁, ∃ y < b, !D i y”

theorem collection_def (D : Semiproposition L 2) (n : SyntacticTerm L) :
    collection D n = ∃⁰ collectionBody D n := by
  simp [collection, collectionBody]

theorem body_open (D : Semiproposition L 2) (n : SyntacticTerm L) :
    (collectionBody D n).free = bounded (Rew.shift ▹ D) (Rew.shift n) (&0) := by
  have ht : (@Rew.free L 1).comp ((@Rew.bShift L ℕ 1).comp (@Rew.bShift L ℕ 0)) =
      (@Rew.bShift L ℕ 0).comp (@Rew.shift L 0) := by
    ext i
    · exact Fin.elim0 i
    · simp [Rew.comp_app]
  have hd : (@Rew.free L 2).comp (Rew.subst ![(#1 : Semiterm L ℕ 3), #0]) =
      (Rew.subst ![(#1 : Semiterm L ℕ 2), #0]).comp (@Rew.shift L 2) := by
    ext i
    · cases i using Fin.cases <;> simp [Rew.comp_app]
      change (@Rew.free L 2) (#(Fin.castSucc (1 : Fin 2))) = #(1 : Fin 2)
      exact Rew.free_bvar_castSucc _
    · simp [Rew.comp_app]
  simp [collectionBody, bounded, Semiformula.ballLT, Semiformula.bexsLT, ball, bexs,
    ← TransitiveRewriting.comp_app, ← Rew.comp_app, ht, hd,
    show (#2 : Semiterm L ℕ 3) = #(Fin.last 2) by rfl]

theorem unbounded_shift (D : Semiproposition L 2) (n : SyntacticTerm L) :
    Rewriting.shift (unbounded D n) = unbounded (Rew.shift ▹ D) (Rew.shift n) := by
  have ht : (@Rew.shift L 1).comp (@Rew.bShift L ℕ 0) =
      (@Rew.bShift L ℕ 0).comp (@Rew.shift L 0) := by
    ext i
    · exact Fin.elim0 i
    · simp [Rew.comp_app]
  have hd : (@Rew.shift L 2).comp (Rew.subst ![(#1 : Semiterm L ℕ 2), #0]) =
      (Rew.subst ![(#1 : Semiterm L ℕ 2), #0]).comp (@Rew.shift L 2) := by
    ext i
    · cases i using Fin.cases <;> simp [Rew.comp_app]
    · simp [Rew.comp_app]
  simp [unbounded, Semiformula.ballLT, ball, ← TransitiveRewriting.comp_app,
    ← Rew.comp_app, ht, hd]

private def sequentize (P Q : Proposition L) (d : Derivation [P 🡒 Q]) : Derivation [∼P, Q] := by
  have h1 : Derivation [P, ∼P, Q] := Derivation.close P (by simp) (by simp)
  have h2 : Derivation [∼Q, ∼P, Q] := Derivation.close Q (by simp) (by simp)
  have h3 : Derivation [∼(P 🡒 Q), ∼P, Q] := by
    simpa [Semiformula.imp_eq] using h1.and h2
  simpa using d.cut h3

/-- The reverse direction of the exact collection obligation is pure LK,
with arbitrary parameters: a common bound can be forgotten. -/
def collection_reverse (D : Semiproposition L 2) (n : SyntacticTerm L) :
    Derivation [collection D n 🡒 unbounded D n] := by
  let D' : Semiproposition L 2 := Rew.shift ▹ D
  let n' : SyntacticTerm L := Rew.shift n
  have hp : Derivation [bounded D' n' (&0) 🡒 unbounded D' n'] := by
    simpa [fixed_left_eq, fixed_right_eq] using
      fixed_bound_reverse (outerGuard n') (witnessGuard (&0)) (D' ⇜ ![#1, #0])
  have hs : Derivation [∼(bounded D' n' (&0)), unbounded D' n'] := sequentize _ _ hp
  have ho : Derivation ((∼(collectionBody D n)).free :: [unbounded D n]⁺) := by
    simpa [D', n', body_open, unbounded_shift, Rewriting.shifts] using hs
  have ha : Derivation [∼(collection D n), unbounded D n] := by
    simpa [collection_def] using ho.all
  simpa [Semiformula.imp_eq] using ha.or

def prove_collection_reverse {T : Theory L} (D : Semiproposition L 2) (n : SyntacticTerm L) :
    Proof T (collection D n 🡒 unbounded D n) := .logical (collection_reverse D n)

end DiophantineConsistency.ParsonsCollection
