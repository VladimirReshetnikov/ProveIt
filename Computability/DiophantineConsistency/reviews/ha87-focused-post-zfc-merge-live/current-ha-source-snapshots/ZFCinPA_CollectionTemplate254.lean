import ZFCinPA.SetPlaceholders
import ZFCinPA.NativeZFContainers254
import ZFCinPA.CollectionResources254

set_option autoImplicit false
noncomputable section

/-!
Fixed extended-language Collection template. These are ordinary
finite syntax definitions, chosen before any arithmetic model or internal K.
Only three new schema sentences are added: witness-rank Separation, total
least-rank Replacement, output Separation. The R equality axiom remains an
explicit target proof callback. The conclusion is one fixed ordinary derivation, for later template translation.
-/
namespace LeanProofs.ZFCinPA.CollectionTemplate254
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.NativeZFContainers254
open _root_.SetTheory.BusyBeaver.ZFC
open _root_.SetTheory.BusyBeaver.ZFC.NamedZF
open _root_.SetTheory.BusyBeaver.ZFC.InternalOrd
open _root_.SetTheory.BusyBeaver.ZFC.InternalRank

abbrev arities : Fin 1 → Nat := fun _ => 2
abbrev Lang := setTemplateLanguage 1 arities
abbrev hom := setHom 1 arities

local instance : Language.Mem Lang := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- Proposition-valued atoms: SetPlaceholders.srcP/srcMem/srcEq intentionally
    accept CLOSED terms only, whereas these finite schema matrices have ordinary
    free parameters. No internal syntax is involved in these three helpers. -/
def predAt {n : Nat} (t u : SyntacticSemiterm Lang n) : Semiproposition Lang n :=
  .rel (placeholderRel (0 : Fin 1)) ![t,u]
def memAt {n : Nat} (t u : SyntacticSemiterm Lang n) : Semiproposition Lang n :=
  .rel (Sum.inl Language.Set.Rel.mem) ![t,u]
def eqAt {n : Nat} (t u : SyntacticSemiterm Lang n) : Semiproposition Lang n :=
  .rel (Sum.inl Language.Set.Rel.eq) ![t,u]

/-- Fixed binary source relation, with the INPUT at #0 and OUTPUT at #1. -/
def rAtom : Semisentence Lang 2 := .rel (placeholderRel (0 : Fin 1)) ![#0,#1]

/-- Only named syntax local to this fixed template, not an internal decoder. -/
inductive Named where
  | pure (p : NForm)
  | pred (input output : Nat)
  | mem (x y : Nat)
  | eq (x y : Nat)
  | bot
  | imp (p q : Named)
  | and (p q : Named)
  | or (p q : Named)
  | all (name : Nat) (p : Named)
  | ex (name : Nat) (p : Named)

def Named.neg (p : Named) := Named.imp p Named.bot

/-- New binder: preserve all old bound slots and bind only the chosen name. -/
def under {n : Nat} (slots : Nat → SyntacticSemiterm Lang n) (x i : Nat) :
    SyntacticSemiterm Lang (n+1) :=
  if i = x then #0 else Rew.bShift (slots i)

/-- The pure native named formula is first translated at depth0. Its free
    name i is then mapped by slots i; binders are handled by Rew.q. -/
def pureAt {n : Nat} (slots : Nat → SyntacticSemiterm Lang n) (p : NForm) :
    Semiproposition Lang n :=
  Rew.bind Fin.elim0 slots ▹
    Semiformula.lMap hom (toSet 0 (NamedZF.toForm id p))

def toFormula : {n : Nat} → (Nat → SyntacticSemiterm Lang n) → Named →
    Semiproposition Lang n
  | _, slots, .pure p => pureAt slots p
  | _, slots, .pred x y => predAt (slots x) (slots y)
  | _, slots, .mem x y => memAt (slots x) (slots y)
  | _, slots, .eq x y => eqAt (slots x) (slots y)
  | _, _, .bot => ⊥
  | _, slots, .imp p q => toFormula slots p 🡒 toFormula slots q
  | _, slots, .and p q => toFormula slots p ⋏ toFormula slots q
  | _, slots, .or p q => toFormula slots p ⋎ toFormula slots q
  | _, slots, .all x p => ∀⁰ toFormula (under slots x) p
  | _, slots, .ex x p => ∃⁰ toFormula (under slots x) p

/-- This is the literal pure IsV named formula; no rank-relation symbol or
    unstated rank axiom is added to the template. -/
def witness (x c : Nat) : Named :=
  .ex (c+x+1) (.ex (c+x+2)
    (.and (.pure (isVF c (c+x+1)))
      (.and (.mem (c+x+2) (c+x+1)) (.pred x (c+x+2)))))

/-- Only used at x=1,c=0; comparison binder4 is disjoint from both roles. -/
def least : Named :=
  .and (.pure (ordF 0)) (.and (witness 1 0)
    (.all 4 (.imp (.and (.pure (ordF 4)) (witness 1 4))
      (.or (.eq 0 4) (.mem 0 4)))))

def emptyAt (c : Nat) : Named := .all (c+1) (Named.neg (.mem (c+1) c))

/-- Input name1/output name0. Its fallback is empty, not the input itself:
    this ensures EVERY image member is an ordinal. -/
def totalLeast : Named :=
  .or least (.and (Named.neg (.ex 2 (.pred 1 2))) (emptyAt 0))

/-- Separation matrix: separated c=#0, parameter x=&0. -/
@[irreducible] def witnessMatrix : Semiproposition Lang 1 :=
  toFormula (fun i => if i=0 then #0 else &(i-1)) (witness 1 0)

/-- Replacement uses Foundation's order INPUT=#0,OUTPUT=#1.
    This deliberately swaps the native named graph's names1/0. -/
@[irreducible] def totalLeastMatrix : Semiproposition Lang 2 :=
  toFormula (fun i => if i=0 then #1 else if i=1 then #0 else &(i-2)) totalLeast

/-- Separation matrix: separated output y=#0; source set a=&0.
    Its existential input name1 is bound locally. -/
def outputMatrix : Semiproposition Lang 1 :=
  toFormula (fun i => if i=0 then #0 else if i=2 then &0 else &(i+1))
    (.ex 1 (.and (.mem 1 2) (.pred 1 0)))

/-- Exact analogue of Foundation Axiom.separationSchema in the expanded language. -/
def separation (K : Semiproposition Lang 1) : Sentence Lang :=
  .univCl “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ !K z”

/-- Exact globally total analogue of Foundation Axiom.replacementSchema. -/
def replacement (K : Semiproposition Lang 2) : Sentence Lang :=
  .univCl “(∀ x, ∃! y, !K x y) →
    ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !K x y”

def witnessSeparation : Sentence Lang := separation witnessMatrix
def rankReplacement : Sentence Lang := replacement totalLeastMatrix
def outputSeparation : Sentence Lang := separation outputMatrix

def predicateCongruence : Sentence Lang := Theory.Eq.relExt (placeholderRel (0 : Fin 1))

/-- Equality for the enlarged language is explicit. For this finite language
    it adds just the new R congruence axiom beyond lifted set-language equality.
    No extended Separation or Replacement schema family is silently included. -/
def collectionTheory : FirstOrder.Theory Lang :=
  (FirstOrder.Theory.lMap hom (𝗭𝗙 : SetTheory)) ∪
    ((𝗘𝗤 Lang) ∪ {witnessSeparation, rankReplacement, outputSeparation})

/-- The canonical G-style conclusion: every output of an input in A has an
    R-related representative in B; every B member is an R output.
    The candidate/source matrix itself has not been decoded here. -/
def collectionSentence : Sentence Lang :=
  “∀ A, ∃ B,
    (∀ x ∈ A, ∀ y, !rAtom x y → ∃ z, !rAtom x z ∧ z ∈ B) ∧
    (∀ y ∈ B, ∃ x, !rAtom x y)”

/-! ## Ordinary semantic bridge -/

instance : 𝗘𝗤 Lang ⪯ collectionTheory :=
  LO.Entailment.WeakerThan.ofSubset (fun _ h => Or.inr (Or.inl h))

section Semantics
variable {M : Type*} [Nonempty M] [SetStructure M]
variable [s : Structure Lang M] [Structure.Eq Lang M] [Structure.Mem Lang M]

abbrev relation (x y : M) : Prop :=
  Structure.rel (L := Lang) (placeholderRel (0 : Fin 1)) ![x,y]

omit [Nonempty M] in
/-- Actual equality and membership identify the pure language reduct. -/
private lemma reduct_standard :
    s.lMap hom = SetTheory.standardStructure M := by
  apply Structure.ext
  · funext k f
    exact f.elim
  · funext k r v
    cases r
    · change Structure.rel (L := Lang) (Sum.inl Language.Set.Rel.eq) v = (v 0 = v 1)
      exact propext (Structure.eq_lang (L := Lang) (M := M) (v := v))
    · change Structure.rel (L := Lang) (Sum.inl Language.Set.Rel.mem) v = (v 0 ∈ v 1)
      exact propext (Structure.mem_lang (L := Lang) (M := M) (v := v))

/-- Semantics of the named fixed syntax; pure formulas remain pure. -/
def NamedSat (rho : Nat → M) : Named → Prop
  | .pure p => NSat (memRel M) rho p
  | .pred x y => relation (rho x) (rho y)
  | .mem x y => rho x ∈ rho y
  | .eq x y => rho x = rho y
  | .bot => False
  | .imp p q => NamedSat rho p → NamedSat rho q
  | .and p q => NamedSat rho p ∧ NamedSat rho q
  | .or p q => NamedSat rho p ∨ NamedSat rho q
  | .all x p => ∀ d, NamedSat (upd rho x d) p
  | .ex x p => ∃ d, NamedSat (upd rho x d) p

private lemma eval_pureAt {n : Nat} (slots : Nat → SyntacticSemiterm Lang n)
    (p : NForm) (b : Fin n → M) (f : Nat → M) :
    (pureAt slots p).Eval b f ↔
      NSat (memRel M) (fun i => (slots i).val b f) p := by
  rw [pureAt, Semiformula.eval_rew, Semiformula.eval_lMap]
  rw [reduct_standard]
  let rho : Nat → M := fun i => (slots i).val b f
  have h := (eval_toSet (NamedZF.toForm id p) 0 ![] rho rho
    (fun i => i.elim0) (fun j => by simp)).trans
    (sat_toForm (memRel M) p id rho)
  simpa only [rho,Function.comp_def,Rew.bind_fvar,Rew.bind_bvar,Matrix.empty_eq,id_eq] using h

omit [Nonempty M] [SetStructure M] [Structure.Eq Lang M] [Structure.Mem Lang M] in
private lemma under_env {n : Nat} (slots : Nat → SyntacticSemiterm Lang n)
    (x : Nat) (d : M) (b : Fin n → M) (f : Nat → M) :
    (fun i => (under slots x i).val (d :> b) f) =
      upd (fun i => (slots i).val b f) x d := by
  funext i
  by_cases h : i=x <;> simp [under,upd,h]

/-- This lemma is uniform in binder depth and all named term environments. -/
theorem eval_toFormula (p : Named) :
    ∀ {n : Nat} (slots : Nat → SyntacticSemiterm Lang n)
      (b : Fin n → M) (f : Nat → M),
    (toFormula slots p).Eval b f ↔
      NamedSat (fun i => (slots i).val b f) p := by
  induction p with
  | pure p => exact fun slots b f => eval_pureAt slots p b f
  | pred x y => intro n slots b f; simp [toFormula,NamedSat,predAt,relation]
  | mem x y =>
      intro n slots b f
      have h := Structure.mem_lang (L := Lang)
        (v := ![(slots x).val b f,(slots y).val b f])
      change Structure.rel (L := Lang) (Sum.inl Language.Set.Rel.mem)
        ![(slots x).val b f,(slots y).val b f] ↔
          (slots x).val b f ∈ (slots y).val b f at h
      simpa only [toFormula,memAt,Semiformula.eval_rel,NamedSat,Matrix.comp₂] using h
  | eq x y =>
      intro n slots b f
      have h := Structure.eq_lang (L := Lang)
        (v := ![(slots x).val b f,(slots y).val b f])
      change Structure.rel (L := Lang) (Sum.inl Language.Set.Rel.eq)
        ![(slots x).val b f,(slots y).val b f] ↔
          (slots x).val b f = (slots y).val b f at h
      simpa only [toFormula,eqAt,Semiformula.eval_rel,NamedSat,Matrix.comp₂] using h
  | bot => intro n slots b f; simp [toFormula,NamedSat]
  | imp p q hp hq => intro n slots b f; simp [toFormula,NamedSat,hp,hq]
  | and p q hp hq => intro n slots b f; simp [toFormula,NamedSat,hp,hq]
  | or p q hp hq => intro n slots b f; simp [toFormula,NamedSat,hp,hq]
  | all x p hp =>
      intro n slots b f
      simp only [toFormula,Semiformula.eval_all,NamedSat]
      exact forall_congr' (fun d => (hp _ _ _).trans (by rw [under_env]))
  | ex x p hp =>
      intro n slots b f
      simp only [toFormula,Semiformula.eval_ex,NamedSat]
      exact exists_congr (fun d => (hp _ _ _).trans (by rw [under_env]))

omit [Nonempty M] [Structure.Eq Lang M] [Structure.Mem Lang M] in
private lemma named_witness (H : _root_.SetTheory.ZFAxioms (memRel M))
    (rho : Nat → M) (x c : Nat) :
    NamedSat rho (witness x c) ↔
      CollectionResources254.WitnessRank H relation (rho x) (rho c) := by
  simp only [witness,NamedSat]
  refine exists_congr (fun S => exists_congr (fun y => ?_))
  rw [nsat_isVF H]
  have hc1 : c ≠ c+x+1 := by omega
  have hc2 : c ≠ c+x+2 := by omega
  have hx1 : x ≠ c+x+1 := by omega
  have hx2 : x ≠ c+x+2 := by omega
  have h12 : c+x+1 ≠ c+x+2 := by omega
  simp only [upd,hc1,hc2,hx1,hx2,h12,if_false,if_true,memRel]

private lemma eval_witnessMatrix (H : _root_.SetTheory.ZFAxioms (memRel M))
    (c : M) (f : Nat → M) :
    witnessMatrix.Eval ![c] f ↔
      CollectionResources254.WitnessRank H relation (f 0) c := by
  rw [witnessMatrix,eval_toFormula,named_witness H]
  simp

omit [Nonempty M] [Structure.Eq Lang M] [Structure.Mem Lang M] in
private lemma named_totalLeast (H : _root_.SetTheory.ZFAxioms (memRel M))
    (rho : Nat → M) :
    NamedSat rho totalLeast ↔
      CollectionResources254.TotalRank H relation (rho 1) (rho 0) := by
  simp only [totalLeast,least,NamedSat,named_witness H,nsat_ordF]
  simp (disch := omega) [CollectionResources254.TotalRank,
    CollectionResources254.LeastRank,CollectionResources254.Empty,emptyAt,Named.neg,
    NamedSat,upd]

private lemma eval_totalLeastMatrix (H : _root_.SetTheory.ZFAxioms (memRel M))
    (x c : M) (f : Nat → M) :
    totalLeastMatrix.Eval ![x,c] f ↔
      CollectionResources254.TotalRank H relation x c := by
  rw [totalLeastMatrix,eval_toFormula,named_totalLeast H]
  simp

private lemma eval_outputMatrix (y : M) (f : Nat → M) :
    outputMatrix.Eval ![y] f ↔ ∃ x, x ∈ f 0 ∧ relation x y := by
  rw [outputMatrix,eval_toFormula]
  simp [NamedSat,upd]

/-- Only pure ZF is extracted. No new-predicate schema enters this bundle. -/
private lemma pure_models [M↓[Lang] ⊧* collectionTheory] :
    M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := by
  have h : (s.lMap hom).toStruc ⊧* (𝗭𝗙 : SetTheory) := by
    constructor
    intro p hp
    apply Semiformula.models_lMap.mp
    exact LO.FirstOrder.Theory.models M collectionTheory (Or.inl ⟨p,hp,rfl⟩)
  simpa only [reduct_standard] using h

omit [Structure.Eq Lang M] in
/-- Reduce the schema skeleton while its matrix is opaque. This keeps the
    large fixed rank matrix out of definitional simplification. -/
private lemma models_separation_iff (K : Semiproposition Lang 1) :
    M↓[Lang] ⊧ separation K ↔
      ∀ f : Nat → M, ∀ a : M, ∃ b : M, ∀ y : M,
        y ∈ b ↔ y ∈ a ∧ K.Eval ![y] f := by
  simp [models_iff,separation]

private lemma models_replacement_iff (K : Semiproposition Lang 2) :
    M↓[Lang] ⊧ replacement K ↔
      ∀ f : Nat → M, (∀ x : M, ∃! c, K.Eval ![x,c] f) →
        ∀ a : M, ∃ image : M, ∀ c : M,
          c ∈ image ↔ ∃ x, x ∈ a ∧ K.Eval ![x,c] f := by
  simp [models_iff,replacement]

/-- Extraction of precisely the three source sentences. -/
private lemma resources [M↓[Lang] ⊧* collectionTheory]
    [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)] :
    CollectionResources254.Resources (zfAxioms_of_models (V := M)) relation := by
  let H := zfAxioms_of_models (V := M)
  have hW := LO.FirstOrder.Theory.models M collectionTheory
    (Or.inr (Or.inr (show witnessSeparation ∈
      ({witnessSeparation,rankReplacement,outputSeparation} : Set (Sentence Lang)) from
        Or.inl rfl)))
  have hT := LO.FirstOrder.Theory.models M collectionTheory
    (Or.inr (Or.inr (show rankReplacement ∈
      ({witnessSeparation,rankReplacement,outputSeparation} : Set (Sentence Lang)) from
        Or.inr (Or.inl rfl))))
  have hO := LO.FirstOrder.Theory.models M collectionTheory
    (Or.inr (Or.inr (show outputSeparation ∈
      ({witnessSeparation,rankReplacement,outputSeparation} : Set (Sentence Lang)) from
        Or.inr (Or.inr rfl))))
  have hW' := (models_separation_iff witnessMatrix).mp hW
  have hT' := (models_replacement_iff totalLeastMatrix).mp hT
  have hO' := (models_separation_iff outputMatrix).mp hO
  change CollectionResources254.Resources H relation
  refine ⟨?_,?_,?_⟩
  · intro x a
    obtain ⟨z,hz⟩ := hW' (fun _ => x) a
    refine ⟨z,fun c => (hz c).trans ?_⟩
    exact and_congr_right (fun _ => eval_witnessMatrix H c (fun _ => x))
  · intro ht a
    let f : Nat → M := fun _ => a
    have htotal : ∀ x : M, ∃! c, totalLeastMatrix.Eval ![x,c] f := by
      intro x
      obtain ⟨c,hc,hu⟩ := ht x
      exact ⟨c,(eval_totalLeastMatrix H x c f).mpr hc,
        fun d hd => hu d ((eval_totalLeastMatrix H x d f).mp hd)⟩
    obtain ⟨image,hi⟩ := hT' f htotal a
    refine ⟨image,fun c => (hi c).trans ?_⟩
    exact exists_congr (fun x => and_congr_right
      (fun _ => eval_totalLeastMatrix H x c f))
  · intro a bound
    obtain ⟨z,hz⟩ := hO' (fun _ => a) bound
    refine ⟨z,fun y => (hz y).trans ?_⟩
    exact and_congr_right (fun _ => eval_outputMatrix y (fun _ => a))

/-- Semantic proof of the fixed ordinary source sentence, not internal
    completeness or truth for an arbitrary coded formula. -/
theorem models_collection [M↓[Lang] ⊧* collectionTheory] :
    M↓[Lang] ⊧ collectionSentence := by
  letI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models
  have h : ∀ A : M, ∃ B : M,
      (∀ x, x ∈ A → ∀ y, relation x y → ∃ z, relation x z ∧ z ∈ B) ∧
      (∀ y, y ∈ B → ∃ x, relation x y) := by
    intro A
    obtain ⟨B,hout,hcover⟩ := CollectionResources254.collection
      (zfAxioms_of_models (V := M)) (reg_clause (V := M)) (pow_clause (V := M))
      relation resources A
    exact ⟨B,fun x hx y hxy => by
      obtain ⟨z,hz,hxz⟩ := hcover x hx ⟨y,hxy⟩
      exact ⟨z,hxz,hz⟩,hout⟩
  simpa [models_iff,collectionSentence,rAtom,predAt,relation] using h
end Semantics

/-- One fixed ordinary derivation. Equality normalization is ordinary model
    quotienting; later target translation must supply R-congruence explicitly.
    This is an ordinary-model completeness application to one fixed sentence,
    independent of any later internal matrix interpretation. -/
theorem collection_provable : collectionTheory ⊢ collectionSentence := by
  apply LO.FirstOrder.Theory.Proof.complete.{0,0}
  apply consequence_iff_eq.{0,0}.mpr
  intro M _ s _ hT
  letI : SetStructure M := ⟨fun y x =>
    Structure.rel (L := Lang) (Sum.inl Language.Set.Rel.mem) ![x,y]⟩
  letI : Structure.Mem Lang M := ⟨fun _ _ => Iff.rfl⟩
  letI : M↓[Lang] ⊧* collectionTheory := hT
  exact models_collection
end LeanProofs.ZFCinPA.CollectionTemplate254
