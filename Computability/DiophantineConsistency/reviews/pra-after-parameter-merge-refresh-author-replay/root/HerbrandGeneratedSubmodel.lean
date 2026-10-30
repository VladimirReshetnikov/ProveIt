import DiophantineConsistency.PRAUniversalAxiomSyntax
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandGeneratedSubmodel
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate PRAUniversalAxiomSyntax

/-- A domain closed under all function symbols, with inherited relations. -/
structure ClosedDomain (L : Language) (M : Type) [Structure L M] where
  carrier : Set M
  closed : ∀ {k} (F : L.Func k) (v : Fin k → carrier), Structure.func F (fun i => (v i).val) ∈ carrier

@[reducible] def induced {L : Language} {M : Type} [Structure L M] (D : ClosedDomain L M) : Structure L D.carrier where
  func := fun {_} F v => ⟨Structure.func F (fun i => (v i).val), D.closed F v⟩
  rel := fun {_} R v => Structure.rel R (fun i => (v i).val)

theorem val_preserved {L : Language} {M : Type} [Structure L M] (D : ClosedDomain L M)
    {ξ : Type} {n : ℕ} (t : Semiterm L ξ n) (b : Fin n → D.carrier) (f : ξ → D.carrier) :
    (Semiterm.val (s := induced D) b f t).val = Semiterm.val (fun i => (b i).val) (fun x => (f x).val) t := by
  induction t with
  | bvar i => rfl
  | fvar x => rfl
  | func F v ih =>
      simp only [Semiterm.val_func]
      change Structure.func F (fun i => (Semiterm.val (s := induced D) b f (v i)).val) = _
      congr 1
      funext i
      exact ih i

/-- Genuine equality on the ambient model restricts to genuine equality on
the induced domain. -/
theorem induced_equality {M : Type} [Structure language M] [Structure.Eq language M]
    (D : ClosedDomain language M) :
    letI : Structure language D.carrier := induced D
    Structure.Eq language D.carrier := by
  letI : Structure language D.carrier := induced D
  constructor
  intro a b
  change Structure.rel (L := language) (M := D.carrier) Language.ORing.Rel.eq ![a,b] ↔ a = b
  change Structure.rel (L := language) Language.ORing.Rel.eq (fun i => (![a,b] i).val) ↔ a = b
  have hv : (fun i => (![a,b] i).val) = ![a.val,b.val] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv]
  change Structure.rel (L := language) Language.Eq.eq ![a.val,b.val] ↔ a = b
  rw [Structure.eq_lang]
  exact ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩

/-- Quantifier-free truth is absolute between a closed domain and its parent. -/
theorem eval_open {L : Language} {M : Type} [Structure L M] (D : ClosedDomain L M)
    {ξ : Type} {n : ℕ} (φ : Semiformula L ξ n) (h : φ.Open)
    (b : Fin n → D.carrier) (f : ξ → D.carrier) :
    Semiformula.Eval (s := induced D) b f φ ↔
      Semiformula.Eval (fun i => (b i).val) (fun x => (f x).val) φ := by
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v =>
      simp only [Semiformula.eval_rel]
      change Structure.rel r (fun i => (Semiterm.val (s := induced D) b f (v i)).val) ↔ _
      have he : (fun i => (Semiterm.val (s := induced D) b f (v i)).val) =
          (Semiterm.val (fun i => (b i).val) (fun x => (f x).val) ∘ v) := by
        funext i
        exact val_preserved D (v i) b f
      rw [he]
  | hnrel r v =>
      simp only [Semiformula.eval_nrel]
      change (¬Structure.rel r (fun i => (Semiterm.val (s := induced D) b f (v i)).val)) ↔ _
      have he : (fun i => (Semiterm.val (s := induced D) b f (v i)).val) =
          (Semiterm.val (fun i => (b i).val) (fun x => (f x).val) ∘ v) := by
        funext i
        exact val_preserved D (v i) b f
      rw [he]
  | hand p q ihp ihq =>
      have hpq : p.Open ∧ q.Open := by simpa [Semiformula.Open, Semiformula.qr] using h
      simp only [LogicalConnective.HomClass.map_and]
      exact and_congr (ihp hpq.1 b) (ihq hpq.2 b)
  | hor p q ihp ihq =>
      have hpq : p.Open ∧ q.Open := by simpa [Semiformula.Open, Semiformula.qr] using h
      simp only [LogicalConnective.HomClass.map_or]
      exact or_congr (ihp hpq.1 b) (ihq hpq.2 b)
  | hall p ih => simp [Semiformula.Open, Semiformula.qr] at h
  | hexs p ih => simp [Semiformula.Open, Semiformula.qr] at h

/-- Universal-prefix formulas are downward absolute for closed domains. -/
theorem universal_down {M : Type} [Structure language M] (D : ClosedDomain language M)
    {ξ : Type} {n : ℕ} (φ : Semiformula language ξ n) (h : UniversalPrefix φ)
    (b : Fin n → D.carrier) (f : ξ → D.carrier) :
    Semiformula.Eval (fun i => (b i).val) (fun x => (f x).val) φ →
      Semiformula.Eval (s := induced D) b f φ := by
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => exact (eval_open D _ h b f).mpr
  | hnrel r v => exact (eval_open D _ h b f).mpr
  | hand p q ihp ihq => exact (eval_open D _ h b f).mpr
  | hor p q ihp ihq => exact (eval_open D _ h b f).mpr
  | hall p ih =>
      simp only [UniversalPrefix] at h
      simp only [Semiformula.eval_all]
      intro hall x
      have hbase := hall x.val
      apply ih h (x :> b)
      have hb : (fun i => ((x :> b) i).val) = (x.val :> fun i => (b i).val) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [hb]
      exact hbase
  | hexs p ih => simp [UniversalPrefix, Semiformula.Open, Semiformula.qr] at h

/-- Every nonempty closed domain of a universal-theory model remains a
model of the candidate universal axioms. -/
theorem universal_model {M : Type} [Structure language M] [Nonempty M]
    (D : ClosedDomain language M) (hne : Nonempty D.carrier)
    (hM : M↓[language] ⊧* UniversalAxiom) :
    letI : Structure language D.carrier := induced D
    letI : Nonempty D.carrier := hne
    D.carrier↓[language] ⊧* UniversalAxiom := by
  letI : Structure language D.carrier := induced D
  letI : Nonempty D.carrier := hne
  letI : M↓[language] ⊧* UniversalAxiom := hM
  constructor
  intro σ hσ
  have hfull := Theory.models (T := UniversalAxiom) M hσ
  have hv : Semiformula.Eval (s := (inferInstance : Structure language M)) ![] Empty.elim σ := by simpa [models_iff] using hfull
  have hv' : Semiformula.Eval (s := (inferInstance : Structure language M))
      (fun i : Fin 0 => ((![] : Fin 0 → D.carrier) i).val)
      (fun x : Empty => (Empty.elim x : D.carrier).val) σ := by
    have hb : (fun i : Fin 0 => ((![] : Fin 0 → D.carrier) i).val) = ![] := Subsingleton.elim _ _
    have hf : (fun x : Empty => (Empty.elim x : D.carrier).val) = Empty.elim := Subsingleton.elim _ _
    rw [hb,hf]
    exact hv
  have hs := universal_down D σ (universalAxiom_isUniversal hσ) ![] Empty.elim hv'
  simpa [models_iff] using hs

/-- The subdomain generated by the values of all terms under one valuation. -/
noncomputable def generated {L : Language} {M : Type} [Structure L M]
    (f : ℕ → M) : ClosedDomain L M where
  carrier := {x | ∃ t : SyntacticTerm L, Semiterm.val ![] f t = x}
  closed := by
    intro k F v
    classical
    choose t ht using fun i => (v i).property
    refine ⟨Semiterm.func F t, ?_⟩
    simp only [Semiterm.val_func, Function.comp_def]
    congr 1
    funext i
    exact ht i

theorem generated_nonempty {L : Language} {M : Type} [Structure L M] (f : ℕ → M) :
    Nonempty (generated (L := L) f).carrier :=
  ⟨⟨f 0, ⟨&0, rfl⟩⟩⟩

theorem generated_contains {L : Language} {M : Type} [Structure L M] (f : ℕ → M) (i : ℕ) :
    f i ∈ (generated (L := L) f).carrier := ⟨&i, rfl⟩

/-- In the term-generated submodel, a universal counterexample relation
holds with a generated witness whenever the ambient model supplies a named
witness against each term value. This is the submodel step of the interactive
Herbrand compactness argument; it does not establish finite satisfiability. -/
theorem generated_countermodel {M : Type} [Structure language M] (e : ℕ → M)
    (ψ : Semiproposition language 2) (hψ : UniversalPrefix ψ)
    (hcounter : ∀ t : SyntacticTerm language, ∃ j : ℕ,
      ψ.Eval ![e j, Semiterm.val ![] e t] e) :
    let D := generated (L := language) e
    let e' : ℕ → D.carrier := fun i => ⟨e i, generated_contains e i⟩
    ∀ x : D.carrier, ∃ y : D.carrier, ψ.Eval (s := induced D) ![y,x] e' := by
  dsimp only
  let D := generated (L := language) e
  let e' : ℕ → D.carrier := fun i => ⟨e i, generated_contains e i⟩
  intro x
  obtain ⟨t,ht⟩ := x.property
  obtain ⟨j,hj⟩ := hcounter t
  let y : D.carrier := e' j
  refine ⟨y, ?_⟩
  apply universal_down D ψ hψ ![y,x] e'
  have hb : (fun i : Fin 2 => (![y,x] i).val) = ![y.val,x.val] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hf : (fun i => (e' i).val) = e := rfl
  rw [hb,hf]
  simpa [y,e', ← ht] using hj

/-- A universal-theory proof of an ∃∀ sentence excludes an ambient model
with named universal counterexamples against every term. This is the
submodel contradiction in the interactive extraction argument. -/
theorem no_countermodel {M : Type} [Structure language M] [Nonempty M]
    (hM : M↓[language] ⊧* UniversalAxiom) (e : ℕ → M)
    (ψ : Semiproposition language 2) (hψ : UniversalPrefix ψ)
    (p : UniversalAxiom ⊢ (∃⁰ (∀⁰ (∼ψ))).univCl) :
    ¬(∀ t : SyntacticTerm language, ∃ j : ℕ,
      ψ.Eval ![e j, Semiterm.val ![] e t] e) := by
  intro hcounter
  let D := generated (L := language) e
  let e' : ℕ → D.carrier := fun i => ⟨e i, generated_contains e i⟩
  letI : Structure language D.carrier := induced D
  letI : Nonempty D.carrier := generated_nonempty e
  have hD : D.carrier↓[language] ⊧* UniversalAxiom := universal_model D (generated_nonempty e) hM
  have hgoal := models_of_provable hD p
  simp only [models_iff, Semiformula.eval_univCl, Semiformula.eval_ex, Semiformula.eval_all,
    LogicalConnective.HomClass.map_neg] at hgoal
  obtain ⟨x,hx⟩ := hgoal e'
  obtain ⟨y,hy⟩ := generated_countermodel e ψ hψ hcounter x
  have hnot := hx y
  apply hnot
  simpa using hy
end DiophantineConsistency.HerbrandGeneratedSubmodel
