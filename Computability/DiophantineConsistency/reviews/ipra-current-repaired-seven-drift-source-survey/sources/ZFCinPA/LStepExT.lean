import ZFCinPA.LStepEx

set_option autoImplicit false
noncomputable section

/-!
# The quantifier templates of the reflection generator

Over the six-placeholder language, `P₀` is the matrix predicate `P'`, `F₁` its
reflection function, `F₃` the witness-bounding function, and `P₄`, `F₅` the
conclusion. The witness formulas are parametrized by the predicate `qS` whose
witnesses are bounded (`P₀` for `∃`, `¬P₀` for `∀`):

* `hasWitS qS r t`: some `y ∈ L_r` has `qS (econs y t)`;
* `anyWitS qS t`: some constructible `y` has it;
* `witS qS a g`: every environment over `L_a` with a witness has one in `L_g`;
* `wbS qS a g`: `g` is the least such ordinal above `a`;
* `rkS qS t r`: `r` is the least stage carrying a witness (or `∅`), a total
  function of `t`.

In every template model, Replacement for `rkS` over a power set containing all
environments over `L_a` bounds the witnesses, and Separation for `witS`
selects the least bound, so `wbS qS` is a total witness-bounding function
(`wb_tot`).
-/

namespace LeanProofs.ZFCinPA.LStepExT

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant
open LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LStepEx
open LeanProofs.ZFCinPA.ConstructibleInterpretation (domL)

local instance : Language.Mem L6 := ⟨Sum.inl Language.Set.Rel.mem⟩

/-! ## The witness formulas -/

section Formulas

variable (qS : Semisentence L6 1)

def hasWitS : Semisentence L6 2 :=
  “r t. ∃ W, !(lift stageP) r W ∧ ∃ y, y ∈ W ∧ ∃ s, !(lift econsS) s y t ∧ !qS s”

def anyWitS : Semisentence L6 1 :=
  “t. ∃ y, !(lift domL) y ∧ ∃ s, !(lift econsS) s y t ∧ !qS s”

def witS : Semisentence L6 2 :=
  “a g. ∀ U, !(lift stageP) a U → ∀ t, !(lift envP) U t → !(anyWitS qS) t → !(hasWitS qS) g t”

def wbS : Semisentence L6 2 :=
  “a g. (!(lift ordP) g ∧ a ∈ g ∧ !(witS qS) a g) ∧
    ∀ h, (!(lift ordP) h ∧ a ∈ h ∧ !(witS qS) a h) → g ∈ h ∨ g = h”

/-- `h` is an ordinal above `a` bounding the witnesses (the separation matrix
of the least bound, with `a` as parameter). -/
def witSepS : Semisentence L6 2 :=
  “h a. !(lift ordP) h ∧ a ∈ h ∧ !(witS qS) a h”

def rkS : Semisentence L6 2 :=
  “t r. (!(anyWitS qS) t ∧ !(lift ordP) r ∧ !(hasWitS qS) r t ∧
      ∀ h, !(lift ordP) h → !(hasWitS qS) h t → r ∈ h ∨ r = h) ∨
    (¬!(anyWitS qS) t ∧ ∀ z, z ∉ r)”

end Formulas

/-! ## Generic ordinal facts -/

section OrdFacts

open SetTheory.BusyBeaver.ZFC.InternalOrd

variable {V : Type*} {mem : V → V → Prop} (H : _root_.SetTheory.ZFAxioms mem) (hR : Regular mem)
include H hR

/-- The least ordinal with a separable property. -/
theorem least_ord {Φ : V → Prop} (hsep : ∀ X, ∃ Z, ∀ h, mem h Z ↔ mem h X ∧ Φ h)
    {r₀ : V} (h₀ : Ord mem r₀) (hΦ : Φ r₀) :
    ∃ r, (Ord mem r ∧ Φ r) ∧ ∀ h, Ord mem h → Φ h → mem r h ∨ r = h := by
  obtain ⟨Z, hZ⟩ := hsep (_root_.SetTheory.vsucc H r₀)
  have hsucc : Ord mem (_root_.SetTheory.vsucc H r₀) := ord_succ H h₀
  obtain ⟨m, hmZ, hmin⟩ := hR Z ⟨r₀, (hZ r₀).2 ⟨_root_.SetTheory.vsucc_self H r₀, hΦ⟩⟩
  obtain ⟨hmX, hmΦ⟩ := (hZ m).1 hmZ
  have hmo : Ord mem m := ord_of_mem hsucc hmX
  refine ⟨m, ⟨hmo, hmΦ⟩, fun h ho hh => ?_⟩
  rcases trichotomy H hR m hmo h ho with hmh | rfl | hhm
  · exact Or.inl hmh
  · exact Or.inr rfl
  · exact absurd ⟨h, hhm, (hZ h).2 ⟨hsucc.1 m hmX h hhm, hh⟩⟩ hmin

omit hR in
/-- A union of ordinals is an ordinal. -/
theorem ord_vunion {B : V} (hB : ∀ r, mem r B → Ord mem r) : Ord mem (_root_.SetTheory.vunion H B) := by
  refine ⟨fun x hx z hz => ?_, fun x hx => ?_⟩
  · obtain ⟨r, hxr, hrB⟩ := (_root_.SetTheory.vunion_spec H B x).1 hx
    exact (_root_.SetTheory.vunion_spec H B z).2 ⟨r, (hB r hrB).1 x hxr z hz, hrB⟩
  · obtain ⟨r, hxr, hrB⟩ := (_root_.SetTheory.vunion_spec H B x).1 hx
    exact (hB r hrB).2 x hxr

/-- An ordinal contained in an ordinal `m` is a member of its successor. -/
theorem mem_vsucc_of_sub {r m : V} (hr : Ord mem r) (hm : Ord mem m) (hsub : ∀ z, mem z r → mem z m) :
    mem r (_root_.SetTheory.vsucc H m) := by
  rcases trichotomy H hR r hr m hm with h | rfl | h
  · exact (_root_.SetTheory.vsucc_spec H m r).2 (Or.inl h)
  · exact _root_.SetTheory.vsucc_self H r
  · exact absurd (hsub m h) (mem_irrefl H hR m)

end OrdFacts

/-! ## Readings in template models -/

section Readings

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.Constructible
  SetTheory.BusyBeaver.ZFC.ConstructibleDef LeanProofs.BoundedZFCConsistency

variable {M : Type} [Nonempty M] [SetStructure M] [Structure L6 M] [Structure.Eq L6 M]
  [Structure.Mem L6 M] [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)]

variable (qS : Semisentence L6 1)

omit [Structure L6 M] [Structure.Eq L6 M] [Structure.Mem L6 M] in
/-- `econsS` reads `econs` at a functional third argument. -/
theorem eval_econsS (s y t : M)
    (hfun : ∀ x z z', _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) x z ∈ t →
      _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) x z' ∈ t → z = z') :
    econsS.Eval ![s, y, t] Empty.elim ↔
      s = econs (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) y t := by
  rw [econsS, eval_piece, nsat_econsAtomF (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) _ 0 1 2 hfun]
  rfl

theorem eval_hasWitS (r t : M)
    (hfun : ∀ x z z', _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) x z ∈ t →
      _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) x z' ∈ t → z = z') :
    (hasWitS qS).Eval ![r, t] Empty.elim ↔
      ∃ W, IsL (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
          (ConstructibleInterpretation.power_of_modelsZF (V := M)) r W ∧
        ∃ y, y ∈ W ∧ qS.Eval ![econs (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) y t] Empty.elim := by
  simp [hasWitS, eval_stageP (H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
      (hP := ConstructibleInterpretation.power_of_modelsZF (V := M)),
    fun s y => eval_econsS s y t hfun]

theorem eval_anyWitS (t : M)
    (hfun : ∀ x z z', _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) x z ∈ t →
      _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) x z' ∈ t → z = z') :
    (anyWitS qS).Eval ![t] Empty.elim ↔
      ∃ y, InL (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
          (ConstructibleInterpretation.power_of_modelsZF (V := M)) y ∧
        qS.Eval ![econs (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) y t] Empty.elim := by
  simp [anyWitS, ConstructibleInterpretation.eval_domL (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
      (ConstructibleInterpretation.power_of_modelsZF (V := M)),
    fun s y => eval_econsS s y t hfun]

theorem eval_witS (a g : M) :
    (witS qS).Eval ![a, g] Empty.elim ↔
      Wit (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
        (ConstructibleInterpretation.power_of_modelsZF (V := M))
        (fun x => qS.Eval ![x] Empty.elim) a g := by
  simp only [witS, Wit]
  simp [eval_stageP (H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
      (hP := ConstructibleInterpretation.power_of_modelsZF (V := M)),
    eval_envP (H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))]
  refine forall_congr' fun U => imp_congr_right fun _ => forall_congr' fun t => ?_
  refine imp_congr_right fun ht => ?_
  rw [eval_anyWitS qS t ht.1.1, eval_hasWitS qS g t ht.1.1]
  simp only [forall_exists_index, and_imp]

theorem eval_wbS (a g : M) :
    (wbS qS).Eval ![a, g] Empty.elim ↔
      WB (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
        (ConstructibleInterpretation.power_of_modelsZF (V := M))
        (fun x => qS.Eval ![x] Empty.elim) a g := by
  simp [wbS, WB, eval_witS]

omit [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)] in
/-- The least-stage relation, read without unfolding its parts. -/
theorem eval_rkS (t r : M) :
    (rkS qS).Eval ![t, r] Empty.elim ↔
      ((anyWitS qS).Eval ![t] Empty.elim ∧ Ord (memRel M) r ∧ (hasWitS qS).Eval ![r, t] Empty.elim ∧
        ∀ h, Ord (memRel M) h → (hasWitS qS).Eval ![h, t] Empty.elim → r ∈ h ∨ r = h) ∨
      (¬ (anyWitS qS).Eval ![t] Empty.elim ∧ ∀ z, z ∉ r) := by
  simp [rkS]

end Readings

/-! ## The witness-bounding function in template models -/

section Resources

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.Constructible
  SetTheory.BusyBeaver.ZFC.ConstructibleDef LeanProofs.BoundedZFCConsistency

variable {M : Type} [Nonempty M] [SetStructure M] [s : Structure L6 M] [Structure.Eq L6 M]
  [Structure.Mem L6 M] [M↓[L6] ⊧* templTheory 6 ar6]

variable (qS : Semisentence L6 1)

/-- **The witness-bounding formula defines a total function**, bounding
witnesses, in every template model. -/
theorem wb_tot :
    haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
    Tot (fun a g : M => (wbS qS).Eval ![a, g] Empty.elim) ∧
      ∀ a g : M, (wbS qS).Eval ![a, g] Empty.elim →
        Wit (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
          (ConstructibleInterpretation.power_of_modelsZF (V := M))
          (fun x => qS.Eval ![x] Empty.elim) a g := by
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  have hR := ConstructibleInterpretation.regular_of_modelsZF (V := M)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  set hP := ConstructibleInterpretation.power_of_modelsZF (V := M)
  set Qs : M → Prop := fun x => qS.Eval ![x] Empty.elim
  -- separation for the bounding property
  have hsep : ∀ a X : M, ∃ Z : M, ∀ h, h ∈ Z ↔ h ∈ X ∧ (Ord (memRel M) h ∧ a ∈ h ∧ Wit H hP Qs a h) := by
    intro a X
    obtain ⟨Z, hZ⟩ := sep_iff (k := 6) (arities := ar6)
      ((Rewriting.emb (witSepS qS) : Semiproposition L6 2) ⇜ ![#0, &0]) (fun _ => a) X
    refine ⟨Z, fun h => (hZ h).trans (and_congr_right fun _ => ?_)⟩
    simp only [witSepS]
    simp [eval_witS]
    exact fun _ _ => Iff.rfl
  -- separation for carrying a witness, at a parameter `t`
  have hsepHW : ∀ t X : M, ∃ Z : M, ∀ r, r ∈ Z ↔ r ∈ X ∧ (hasWitS qS).Eval ![r, t] Empty.elim := by
    intro t X
    obtain ⟨Z, hZ⟩ := sep_iff (k := 6) (arities := ar6)
      ((Rewriting.emb (hasWitS qS) : Semiproposition L6 2) ⇜ ![#0, &0]) (fun _ => t) X
    exact ⟨Z, fun r => (hZ r).trans (and_congr_right fun _ => by simp)⟩
  -- a constructible witness lies in some stage
  have hAW_raw : ∀ t, (anyWitS qS).Eval ![t] Empty.elim →
      ∃ r₀, Ord (memRel M) r₀ ∧ (hasWitS qS).Eval ![r₀, t] Empty.elim := by
    intro t hA
    simp only [anyWitS] at hA
    simp [ConstructibleInterpretation.eval_domL H hP] at hA
    obtain ⟨y, ⟨r₀, W₀, hr₀, hW₀, hyW₀⟩, s', hs, hq⟩ := hA
    refine ⟨r₀, hr₀, ?_⟩
    simp only [hasWitS]
    simp [eval_stageP (H := H) (hP := hP)]
    exact ⟨W₀, hW₀, y, hyW₀, s', hs, hq⟩
  -- the least stage carrying a witness is a total function of `t`
  have hrk : ∀ t : M, ∃! r, (rkS qS).Eval ![t, r] Empty.elim := by
    intro t
    by_cases hA : (anyWitS qS).Eval ![t] Empty.elim
    · obtain ⟨r₀, hr₀, hHW₀⟩ := hAW_raw t hA
      obtain ⟨r, ⟨hro, hrW⟩, hleast⟩ := least_ord H hR (hsepHW t) hr₀ hHW₀
      refine ⟨r, (eval_rkS qS t r).2 (Or.inl ⟨hA, hro, hrW, hleast⟩), fun r' hr' => ?_⟩
      rcases (eval_rkS qS t r').1 hr' with ⟨-, hro', hrW', hleast'⟩ | ⟨hnA, -⟩
      · rcases hleast r' hro' hrW' with h | h
        · rcases hleast' r hro hrW with h' | h'
          · exact absurd (hro.1 r' h' r h) (mem_irrefl H hR r)
          · exact h'
        · exact h.symm
      · exact absurd hA hnA
    · refine ⟨_root_.SetTheory.vempty H,
        (eval_rkS qS t _).2 (Or.inr ⟨hA, fun z => _root_.SetTheory.vempty_spec H z⟩), fun r' hr' => ?_⟩
      rcases (eval_rkS qS t r').1 hr' with ⟨hA', -⟩ | ⟨-, hz⟩
      · exact absurd hA' hA
      · exact H.ext _ _ fun z =>
          ⟨fun h => absurd h (hz z), fun h => absurd h (_root_.SetTheory.vempty_spec H z)⟩
  -- one bound for each ordinal
  have hbound : ∀ a : M, Ord (memRel M) a → ∃ g, Ord (memRel M) g ∧ a ∈ g ∧ Wit H hP Qs a g := by
    intro a ha
    obtain ⟨U, hU⟩ := isL_exists H hR hP ha
    obtain ⟨P₁, hP₁⟩ := hP (_root_.SetTheory.vcup H (_root_.SetTheory.omegaV H) U)
    obtain ⟨P₂, hP₂⟩ := hP P₁
    obtain ⟨X, hX⟩ := hP P₂
    have henvX : ∀ t, IsEnvOn H U t → t ∈ X := by
      intro t ht
      refine (hX t).2 fun p hp => ?_
      obtain ⟨n, y, hn, rfl⟩ := ht.1.2.2 p hp
      have hy : y ∈ U := ht.2 n y hp
      refine (hP₂ _).2 fun q hq => ?_
      refine (hP₁ q).2 fun z hz => ?_
      rcases (_root_.SetTheory.kpair_mem H n y q).1 hq with rfl | rfl
      · rw [(_root_.SetTheory.vsingle_spec H n z).1 hz]
        exact (_root_.SetTheory.vcup_spec H _ _ n).2 (Or.inl hn)
      · rcases (_root_.SetTheory.vpair_spec H n y z).1 hz with rfl | rfl
        · exact (_root_.SetTheory.vcup_spec H _ _ _).2 (Or.inl hn)
        · exact (_root_.SetTheory.vcup_spec H _ _ _).2 (Or.inr hy)
    obtain ⟨B, hB⟩ := repl_iff (k := 6) (arities := ar6) (Rewriting.emb (rkS qS)) (fun _ => a)
      (by simpa using hrk) X
    have hB' : ∀ r, r ∈ B ↔ ∃ t, t ∈ X ∧ (rkS qS).Eval ![t, r] Empty.elim := by simpa using hB
    have hBo : ∀ r, r ∈ B → Ord (memRel M) r := by
      intro r hr
      obtain ⟨t, -, hrk'⟩ := (hB' r).1 hr
      rcases (eval_rkS qS t r).1 hrk' with ⟨-, hro, -⟩ | ⟨-, hz⟩
      · exact hro
      · exact ⟨fun x hx => absurd hx (hz x), fun x hx => absurd hx (hz x)⟩
    have hUo : Ord (memRel M) (_root_.SetTheory.vunion H B) := ord_vunion H hBo
    have hmo : Ord (memRel M) (_root_.SetTheory.vcup H a (_root_.SetTheory.vunion H B)) := by
      rcases LStepAnd.vcup_ord H hR ha hUo with h | h <;> rw [h] <;> assumption
    refine ⟨_, ord_succ H hmo,
      mem_vsucc_of_sub H hR ha hmo fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inl hz), ?_⟩
    intro U' hU' t ht hw
    rw [isL_unique H hR hP ha hU' hU] at ht
    obtain ⟨r, hrk', -⟩ := hrk t
    have hA : (anyWitS qS).Eval ![t] Empty.elim := (eval_anyWitS qS t ht.1.1).2 hw
    rcases (eval_rkS qS t r).1 hrk' with ⟨-, hro, hrW, -⟩ | ⟨hnA, -⟩
    · have hrB : r ∈ B := (hB' r).2 ⟨t, henvX t ht, hrk'⟩
      have hrg := mem_vsucc_of_sub H hR hro hmo fun z hz =>
        (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inr ((_root_.SetTheory.vunion_spec H B z).2 ⟨r, hz, hrB⟩))
      obtain ⟨W, hW, y, hyW, hq⟩ := (eval_hasWitS qS r t ht.1.1).1 hrW
      obtain ⟨W', hW'⟩ := isL_exists H hR hP (ord_succ H hmo)
      exact ⟨W', hW', y, isL_mono H hR hP (ord_succ H hmo) hrg hW hW' y hyW, hq⟩
    · exact absurd hA hnA
  have hfun : (fun a g : M => (wbS qS).Eval ![a, g] Empty.elim) = WB H hP Qs :=
    funext fun a => funext fun g => propext (eval_wbS qS a g)
  exact ⟨by rw [hfun]; exact wb_exists H hR hP hbound hsep,
    fun a g h => ((eval_wbS qS a g).1 h).1.2.2⟩

end Resources

/-! ## The quantifier templates -/

/-- The existential body, literally the shape of `EnvTransform.exsWrap`. -/
def exBody : Semisentence L6 1 := ∃⁰ ∃⁰ (lift econsS ⋏ (lift domYS ⋏ (P₀ ⇜ ![#0])))

/-- The universal body, literally the shape of `EnvTransform.allWrap`. -/
def allBody : Semisentence L6 1 := ∀⁰ ∀⁰ (∼lift econsS ⋎ (∼lift domYS ⋎ (P₀ ⇜ ![#0])))

/-- `P₄` is the existential quantification of `P₀` over `L`. -/
def exDefP : Sentence L6 := ∀⁰ (P₄ 🡘 exBody)

/-- `P₄` is the universal quantification of `P₀` over `L`. -/
def allDefP : Sentence L6 := ∀⁰ (P₄ 🡘 allBody)

/-- `F₃` is the witness-bounding function of `qS`. -/
def wbDef (qS : Semisentence L6 1) : Sentence L6 := ∀⁰ ∀⁰ (F₃ 🡘 wbS qS)

/-- **The existential template.** -/
def exTemplate : Sentence L6 :=
  (totS F₁ ⋏ reflS P₀ F₁ ⋏ exDefP ⋏ wbDef P₀ ⋏ maxDefF) 🡒 (totS F₅ ⋏ reflS P₄ F₅)

/-- **The universal template.** -/
def allTemplate : Sentence L6 :=
  (totS F₁ ⋏ reflS P₀ F₁ ⋏ allDefP ⋏ wbDef (∼P₀) ⋏ maxDefF) 🡒 (totS F₅ ⋏ reflS P₄ F₅)

section TemplateReadings

open SetTheory.BusyBeaver.ZFC.Constructible LeanProofs.BoundedZFCConsistency

variable {M : Type} [Nonempty M] [SetStructure M] [Structure L6 M] [Structure.Eq L6 M]
  [Structure.Mem L6 M] [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)]

omit [Structure L6 M] [Structure.Eq L6 M] [Structure.Mem L6 M] in
theorem eval_domYS (s y t : M) :
    domYS.Eval ![s, y, t] Empty.elim ↔
      InL (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
        (ConstructibleInterpretation.power_of_modelsZF (V := M)) y := by
  simp [domYS, ConstructibleInterpretation.eval_domL (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
    (ConstructibleInterpretation.power_of_modelsZF (V := M))]

theorem eval_exBody (t : M)
    (hfun : ∀ x z z', _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) x z ∈ t →
      _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) x z' ∈ t → z = z') :
    exBody.Eval ![t] Empty.elim ↔
      ∃ y, InL (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
          (ConstructibleInterpretation.power_of_modelsZF (V := M)) y ∧
        P₀.Eval ![econs (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) y t] Empty.elim := by
  simp [exBody, eval_domYS, fun s y => eval_econsS s y t hfun]

theorem eval_allBody (t : M)
    (hfun : ∀ x z z', _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) x z ∈ t →
      _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) x z' ∈ t → z = z') :
    allBody.Eval ![t] Empty.elim ↔
      ∀ y, InL (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
          (ConstructibleInterpretation.power_of_modelsZF (V := M)) y →
        P₀.Eval ![econs (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) y t] Empty.elim := by
  simp [allBody, eval_domYS, fun s y => eval_econsS s y t hfun, or_iff_not_imp_left]

omit [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)] [SetStructure M] [Structure.Eq L6 M] [Structure.Mem L6 M] in
theorem models_wbDef (qS : Semisentence L6 1) (h : M↓[L6] ⊧ wbDef qS) :
    ∀ a g : M, F₃.Eval ![a, g] Empty.elim ↔ (wbS qS).Eval ![a, g] Empty.elim := by
  simp only [models_iff, wbDef] at h
  simp at h
  exact fun a g => h g a

end TemplateReadings

/-- **The existential template is a theorem of the template theory.** -/
theorem exTemplate_provable : templTheory 6 ar6 ⊢ exTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  simp only [exTemplate, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨htot, hrefl, hdefP, hwb, hdefF⟩
  rw [models_totS] at htot ⊢
  rw [models_reflS] at hrefl ⊢
  rw [models_maxDefF] at hdefF
  have hP4 : ∀ t : M, P₄.Eval ![t] Empty.elim ↔ exBody.Eval ![t] Empty.elim := by
    simpa [models_iff, exDefP] using hdefP
  have hF3 := models_wbDef P₀ hwb
  obtain ⟨htotWB, hWit⟩ := wb_tot (M := M) P₀
  have hG : (fun a g : M => F₃.Eval ![a, g] Empty.elim) =
      fun a g => (wbS P₀).Eval ![a, g] Empty.elim :=
    funext fun a => funext fun g => propext (hF3 a g)
  have htotG : Tot (fun a g : M => F₃.Eval ![a, g] Empty.elim) := by rw [hG]; exact htotWB
  exact ex_step (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
    (ConstructibleInterpretation.regular_of_modelsZF (V := M))
    (ConstructibleInterpretation.power_of_modelsZF (V := M)) htot hrefl htotG
    (fun a g h => hWit a g ((hF3 a g).1 h))
    (fun U t ht => (hP4 t).trans (eval_exBody t ht.1.1)) hdefF

/-- **The universal template is a theorem of the template theory.** -/
theorem allTemplate_provable : templTheory 6 ar6 ⊢ allTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  simp only [allTemplate, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨htot, hrefl, hdefP, hwb, hdefF⟩
  rw [models_totS] at htot ⊢
  rw [models_reflS] at hrefl ⊢
  rw [models_maxDefF] at hdefF
  have hP4 : ∀ t : M, P₄.Eval ![t] Empty.elim ↔ allBody.Eval ![t] Empty.elim := by
    simpa [models_iff, allDefP] using hdefP
  have hF3 := models_wbDef (∼P₀) hwb
  obtain ⟨htotWB, hWit⟩ := wb_tot (M := M) (∼P₀)
  have hG : (fun a g : M => F₃.Eval ![a, g] Empty.elim) =
      fun a g => (wbS (∼P₀)).Eval ![a, g] Empty.elim :=
    funext fun a => funext fun g => propext (hF3 a g)
  have htotG : Tot (fun a g : M => F₃.Eval ![a, g] Empty.elim) := by rw [hG]; exact htotWB
  have hneg : (fun x : M => (∼P₀).Eval ![x] Empty.elim) = fun x => ¬ P₀.Eval ![x] Empty.elim :=
    funext fun x => by simp
  exact all_step (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
    (ConstructibleInterpretation.regular_of_modelsZF (V := M))
    (ConstructibleInterpretation.power_of_modelsZF (V := M)) htot hrefl htotG
    (fun a g h => by rw [← hneg]; exact hWit a g ((hF3 a g).1 h))
    (fun U t ht => (hP4 t).trans (eval_allBody t ht.1.1)) hdefF

end LeanProofs.ZFCinPA.LStepExT
