import ZFCinPA.SeedBundleTemplates222
import ZFCinPA.ModelCodedDecoderCollection254
import ZFCinPA.ModelCodedBinderAbsorption
import BusyBeaver.ZFC.ArithmeticSeedTemplates222

set_option autoImplicit false
noncomputable section

/-!
# The decoded C222 seed bundle is an internal ZF theorem

For internal labels `a, b, c` with the actual bundle gates `c ≠ a`, `c ≠ b`,
`𝗭𝗙` internally proves `decode (bundle222 a b c)` (`zf_decoded_bundle222_provable`).
The bundle is `¬(vrel → nks)`. `vrel` is an equality-free vacuity instance.
The negation of `nks` is read off the compiled seed templates of
`SeedBundleTemplates222`: with `K := binaryBody a b (decoded c)` (or, for `a = b`,
the input slot bound to the fresh label `c`), the named decoded formula is
literally the translated template, by the label-binding laws
(`binaryBody_subst`, absorption, commutation, and freshness of the matrix's
own code label). The code `c = 0` is handled through `decoded 0 ↔ ⊤`.
-/

namespace LeanProofs.ZFCinPA.ModelCodedDecoderBundle222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedBinderAbsorption
open LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254
open LeanProofs.ZFCinPA.ModelCodedBindTwoSlots
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254
open LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254
open LeanProofs.ZFCinPA.ModelCodedDecoderContainer254
open LeanProofs.ZFCinPA.ModelCodedDecoderCollection254
open LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254
open LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SeedBundleTemplates222
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticTemplates254 ArithmeticSeedTemplates222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ)
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := ℒₛₑₜ)

/-! ## A non-consecutive absorption law -/

private instance bindOneAt_delta' : 𝚫₁-Function₃[V] (bindOneAt ℒₛₑₜ) :=
  bindOneAt_defined.graph_delta.to_definable

lemma termBindOneAt_absorb_any {depth term : V} (ht : IsSemiterm ℒₛₑₜ depth term) :
    ∀ chosen e : V,
    termBindOneAt ℒₛₑₜ chosen e (termBindOneAt ℒₛₑₜ chosen depth term) =
      termBindOneAt ℒₛₑₜ chosen depth term :=
  LeanProofs.ZFCinPA.ModelCodedBinderAbsorption.termBindOneAt_absorb_any ht

/-- A label bound once is absent: binding it again, at any index, is the identity. -/
theorem bindOneAt_absorb_any {depth p : V} (hp : IsSemiformula ℒₛₑₜ depth p) :
    ∀ chosen e : V,
    bindOneAt ℒₛₑₜ chosen e (bindOneAt ℒₛₑₜ chosen depth p) = bindOneAt ℒₛₑₜ chosen depth p :=
  LeanProofs.ZFCinPA.ModelCodedBinderAbsorption.bindOneAt_absorb_any hp

/-! ## Named pieces of the interpreted circuit -/

noncomputable def reqN (b k : V) (p : Formula V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  namedFormula b (p 🡒 ((namedFormula b (p 🡒 (memNamed b k 🡒 ⊥))) 🡒 ⊥))

noncomputable def closN (a b k : V) (p : Formula V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  namedFormula b (memNamed b k 🡒 ((namedFormula a (p 🡒 ((namedFormula a
    ((namedFormula k (memNamed k a 🡒 memNamed k b)) 🡒 reqN b k p)) 🡒 ⊥))) 🡒 ⊥))

noncomputable def nksN (a b c : V) (p : Formula V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  namedFormula c (closN a b c p 🡒 (reqN b c p 🡒 ⊥))

noncomputable def vrelN (a b c : V) : Formula V ℒₛₑₜ :=
  memNamed a b 🡒 namedFormula c (memNamed a b)

theorem interpret_nks (a b c : V) :
    interpret nksTemplate a b c 0 = nksN a b c (decoded c) := by
  simp [interpret, nksTemplate, nksC, closC, reqC, Circuit.neg, Circuit.al, Circuit.im,
    Circuit.el, nksN, closN, reqN, memNamed, Circuit.eval]

theorem interpret_vrel (a b c : V) :
    interpret vrelTemplate a b c 0 = vrelN a b c := by
  simp [interpret, vrelTemplate, vrelC, Circuit.al, Circuit.im, Circuit.el, vrelN, memNamed,
    Circuit.eval]

theorem interpret_bundle (a b c : V) :
    interpret bundleTemplate a b c 0 = ((vrelN a b c 🡒 nksN a b c (decoded c)) 🡒 ⊥) := by
  rw [← interpret_nks, ← interpret_vrel]
  simp [interpret, bundleTemplate, ArithmeticSeedTemplates222.bundleC, Circuit.neg, Circuit.im,
    nksTemplate, vrelTemplate]

/-! ## Typed label binding -/

local instance (k : Nat) : GödelQuote (Language.Set.Rel k) V := gödelQuoteRel (L := ℒₛₑₜ) k

private lemma mem_symbol : (ℒₛₑₜ).IsRel (2 : V) ((1 : Nat) : V) := by
  simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 1)).mpr
    ⟨Language.Set.Rel.mem,rfl⟩

noncomputable def bindT {n : Nat} (chosen : V)
    (p : Bootstrapping.Semiformula V ℒₛₑₜ n) : Bootstrapping.Semiformula V ℒₛₑₜ (n+1) :=
  ⟨bindOneAt ℒₛₑₜ chosen n p.val, by
    simpa only [Nat.cast_add,Nat.cast_one] using bindOneAt_isSemiformula p.isSemiformula chosen⟩
noncomputable def termBindT {n : Nat} (chosen : V)
    (t : Bootstrapping.Semiterm V ℒₛₑₜ n) : Bootstrapping.Semiterm V ℒₛₑₜ (n+1) :=
  ⟨termBindOneAt ℒₛₑₜ chosen n t.val, by
    simpa only [Nat.cast_add,Nat.cast_one] using termBindOneAt_isSemiterm t.isSemiterm chosen⟩
@[simp] lemma bindT_val {n : Nat} (chosen : V) (p : Bootstrapping.Semiformula V ℒₛₑₜ n) :
    (bindT chosen p).val = bindOneAt ℒₛₑₜ chosen n p.val := rfl
@[simp] lemma namedBody_bindT (chosen : V) (p : Formula V ℒₛₑₜ) :
    namedBody chosen p = bindT chosen p := rfl
@[simp] lemma bindT_imp {n : Nat} (chosen : V) (p q : Bootstrapping.Semiformula V ℒₛₑₜ n) :
    bindT chosen (p 🡒 q) = bindT chosen p 🡒 bindT chosen q := ModelCodedDecoderContainer254.bindT_imp chosen p q
@[simp] lemma bindT_all {n : Nat} (chosen : V) (p : Bootstrapping.Semiformula V ℒₛₑₜ (n+1)) :
    bindT chosen (∀⁰ p) = ∀⁰ bindT chosen p := ModelCodedDecoderContainer254.bindT_all chosen p
@[simp] lemma bindT_bot {n : Nat} (chosen : V) :
    bindT chosen (⊥ : Bootstrapping.Semiformula V ℒₛₑₜ n) = ⊥ := by
  apply Bootstrapping.Semiformula.ext
  simp [bindT]
@[simp] lemma termBindT_bvar {n : Nat} (chosen : V) (i : Fin n) :
    termBindT chosen (Bootstrapping.Semiterm.bvar i) = Bootstrapping.Semiterm.bvar i.castSucc := ModelCodedDecoderContainer254.termBindT_bvar chosen i
@[simp] lemma termBindT_fvar {n : Nat} (chosen x : V) :
    termBindT chosen (Bootstrapping.Semiterm.fvar x : Bootstrapping.Semiterm V ℒₛₑₜ n) =
      if x = chosen then Bootstrapping.Semiterm.bvar (Fin.last n) else Bootstrapping.Semiterm.fvar x := ModelCodedDecoderContainer254.termBindT_fvar chosen x
@[simp] lemma bindT_mem {n : Nat} (chosen : V) (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    bindT chosen (memAtom t u) = memAtom (termBindT chosen t) (termBindT chosen u) := ModelCodedDecoderContainer254.bindT_mem chosen t u
/-! ## Leaf identities -/

section Leaves

variable {P : V} (hP : IsFormula ℒₛₑₜ P)
include hP

/-- A fresh label disappears from any chain built over `P`. -/
lemma fresh_remove {c : V} (hf : ∀ depth : V, bindOneAt ℒₛₑₜ c depth P = P)
    (x y : V) (hcx : c ≠ x) (hcy : c ≠ y) (d e f : V) :
    bindOneAt ℒₛₑₜ c d (bindOneAt ℒₛₑₜ x e (bindOneAt ℒₛₑₜ y f P)) =
      bindOneAt ℒₛₑₜ x e (bindOneAt ℒₛₑₜ y f P) := by
  rw [bindOneAt_commute (bindOneAt_isUFormula hP.isUFormula y f) c x d e hcx,
    bindOneAt_commute hP.isUFormula c y d f hcy, hf d]

lemma fresh_remove1 {c : V} (hf : ∀ depth : V, bindOneAt ℒₛₑₜ c depth P = P)
    (x : V) (hcx : c ≠ x) (d e : V) :
    bindOneAt ℒₛₑₜ c d (bindOneAt ℒₛₑₜ x e P) = bindOneAt ℒₛₑₜ x e P := by
  rw [bindOneAt_commute hP.isUFormula c x d e hcx, hf d]

/-- A second binding of an already bound label is the identity. -/
lemma absorb0 (x e : V) :
    bindOneAt ℒₛₑₜ x e (bindOneAt ℒₛₑₜ x 0 P) = bindOneAt ℒₛₑₜ x 0 P :=
  bindOneAt_absorb_any (by simpa using hP) x e

end Leaves

lemma isSF_mono {k n p : V} (h : IsSemiformula ℒₛₑₜ k p) (hkn : k ≤ n) :
    IsSemiformula ℒₛₑₜ n p :=
  isSemiformula_iff.mpr ⟨h.isUFormula, le_trans h.bv_le hkn⟩

lemma isSF_bind0 {P : V} (hP : IsFormula ℒₛₑₜ P) (x : V) :
    IsSemiformula ℒₛₑₜ 1 (bindOneAt ℒₛₑₜ x 0 P) := by
  simpa using bindOneAt_isSemiformula hP x

/-! ### Distinct labels: the five matrix occurrences -/

section DistinctLeaves

variable {a b c P : V} (hP : IsFormula ℒₛₑₜ P) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
  (hf : ∀ depth : V, bindOneAt ℒₛₑₜ c depth P = P)
include hP hab hca hcb hf

lemma leafB1 : bindOneAt ℒₛₑₜ a 2 (bindOneAt ℒₛₑₜ c 1 (bindOneAt ℒₛₑₜ b 0 P)) =
    bindOneAt ℒₛₑₜ b 0 (bindOneAt ℒₛₑₜ a 2 P) := by
  rw [fresh_remove1 hP hf b hcb 1 0]
  exact bindOneAt_commute hP.isUFormula a b 2 0 hab

lemma leafB2 : bindOneAt ℒₛₑₜ a 3 (bindOneAt ℒₛₑₜ c 2 (bindOneAt ℒₛₑₜ b 1
    (bindOneAt ℒₛₑₜ b 0 P))) = bindOneAt ℒₛₑₜ b 0 (bindOneAt ℒₛₑₜ a 3 P) := by
  rw [absorb0 hP b 1, fresh_remove1 hP hf b hcb 2 0]
  exact bindOneAt_commute hP.isUFormula a b 3 0 hab

lemma leafB3 : bindOneAt ℒₛₑₜ a 3 (bindOneAt ℒₛₑₜ c 2 (bindOneAt ℒₛₑₜ b 1
    (bindOneAt ℒₛₑₜ a 0 P))) = bindOneAt ℒₛₑₜ b 1 (bindOneAt ℒₛₑₜ a 0 P) := by
  rw [fresh_remove hP hf b a hcb hca 2 1 0,
    bindOneAt_commute (bindOneAt_isUFormula hP.isUFormula a 0) a b 3 1 hab, absorb0 hP a 3]

lemma leafB4 : bindOneAt ℒₛₑₜ a 5 (bindOneAt ℒₛₑₜ c 4 (bindOneAt ℒₛₑₜ b 3
    (bindOneAt ℒₛₑₜ a 2 (bindOneAt ℒₛₑₜ a 1 (bindOneAt ℒₛₑₜ b 0 P))))) =
      bindOneAt ℒₛₑₜ b 0 (bindOneAt ℒₛₑₜ a 1 P) := by
  have hB0 := isSF_bind0 hP b
  rw [bindOneAt_absorb_any hB0 a 2,
    bindOneAt_commute hB0.isUFormula b a 3 1 (Ne.symm hab), absorb0 hP b 3,
    fresh_remove hP hf a b hca hcb 4 1 0, bindOneAt_absorb_any hB0 a 5]
  exact bindOneAt_commute hP.isUFormula a b 1 0 hab

lemma leafB5 : bindOneAt ℒₛₑₜ a 6 (bindOneAt ℒₛₑₜ c 5 (bindOneAt ℒₛₑₜ b 4
    (bindOneAt ℒₛₑₜ a 3 (bindOneAt ℒₛₑₜ a 2 (bindOneAt ℒₛₑₜ b 1 (bindOneAt ℒₛₑₜ b 0 P)))))) =
      bindOneAt ℒₛₑₜ b 0 (bindOneAt ℒₛₑₜ a 2 P) := by
  have hB0 := isSF_bind0 hP b
  have hB2 : IsSemiformula ℒₛₑₜ 2 (bindOneAt ℒₛₑₜ b 0 P) := isSF_mono hB0 one_le_two
  rw [absorb0 hP b 1, bindOneAt_absorb_any hB2 a 3,
    bindOneAt_commute hB0.isUFormula b a 4 2 (Ne.symm hab), absorb0 hP b 4,
    fresh_remove hP hf a b hca hcb 5 2 0, bindOneAt_absorb_any hB2 a 6]
  exact bindOneAt_commute hP.isUFormula a b 2 0 hab

end DistinctLeaves

/-! ### Coincident labels: every occurrence collapses to one binding -/

section DiagonalLeaves

variable {a c P : V} (hP : IsFormula ℒₛₑₜ P) (hca : c ≠ a)
  (hf : ∀ depth : V, bindOneAt ℒₛₑₜ c depth P = P)
include hP hca hf

lemma leafD2 : bindOneAt ℒₛₑₜ c 1 (bindOneAt ℒₛₑₜ a 0 P) = bindOneAt ℒₛₑₜ a 0 P :=
  fresh_remove1 hP hf a hca 1 0

lemma leafD3 : bindOneAt ℒₛₑₜ c 2 (bindOneAt ℒₛₑₜ a 1 (bindOneAt ℒₛₑₜ a 0 P)) =
    bindOneAt ℒₛₑₜ a 0 P := by
  rw [absorb0 hP a 1, fresh_remove1 hP hf a hca 2 0]

lemma leafD5 : bindOneAt ℒₛₑₜ c 4 (bindOneAt ℒₛₑₜ a 3 (bindOneAt ℒₛₑₜ a 2
    (bindOneAt ℒₛₑₜ a 1 (bindOneAt ℒₛₑₜ a 0 P)))) = bindOneAt ℒₛₑₜ a 0 P := by
  rw [absorb0 hP a 1, absorb0 hP a 2, absorb0 hP a 3, fresh_remove1 hP hf a hca 4 0]

lemma leafD6 : bindOneAt ℒₛₑₜ c 5 (bindOneAt ℒₛₑₜ a 4 (bindOneAt ℒₛₑₜ a 3 (bindOneAt ℒₛₑₜ a 2
    (bindOneAt ℒₛₑₜ a 1 (bindOneAt ℒₛₑₜ a 0 P))))) = bindOneAt ℒₛₑₜ a 0 P := by
  rw [absorb0 hP a 1, absorb0 hP a 2, absorb0 hP a 3, absorb0 hP a 4,
    fresh_remove1 hP hf a hca 5 0]

end DiagonalLeaves


/-! ## Translation of the template shapes -/

section Translate

variable (K : Bootstrapping.Semiformula V ℒₛₑₜ 2)

lemma tr_all {n : Nat} (p : Semiproposition LB (n+1)) :
    translateFormula (fun _ : Fin 1 => K) (∀⁰ p) = ∀⁰ translateFormula (fun _ : Fin 1 => K) p := rfl
lemma tr_bot {n : Nat} :
    translateFormula (V := V) (fun _ : Fin 1 => K) (⊥ : Semiproposition LB n) = ⊥ := rfl
lemma tr_rA {n : Nat} (i j : Fin n) :
    translateFormula (fun _ : Fin 1 => K) (Rewriting.emb (rA i j) : Semiproposition LB n) =
      K.subst ![#'i, #'j] := by
  simp [rA, translateFormula, placeholderRel, Rew.emb_bvar]
  congr 1
  funext k
  match k with
  | 0 => rfl
  | 1 => rfl
lemma tr_mA {n : Nat} (i j : Fin n) :
    translateFormula (fun _ : Fin 1 => K) (Rewriting.emb (mA i j) : Semiproposition LB n) =
      memAtom (#'i) (#'j) := by
  simp [mA, translateFormula, memAtom, Rew.emb_bvar]
  congr 1
  funext k
  match k with
  | 0 => rfl
  | 1 => rfl

end Translate

/-! ## The two template identities -/

section Identities

variable {a b c : V} (P : Formula V ℒₛₑₜ)

private lemma cast_fin {m : Nat} (i : Fin m) : ((i : ℕ) : V) = ((i : ℕ) : V) := rfl

variable (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
  (hf : ∀ depth : V, bindOneAt ℒₛₑₜ c depth P.val = P.val)
include hab hca hcb hf

lemma tleafB1 : bindT a (bindT c (bindT b P)) = (binaryBody a b P).subst ![#'2, #'0] := by
  apply Bootstrapping.Semiformula.ext
  rw [binaryBody_subst a b P (2 : Fin 3) 0 hab]
  simpa using leafB1 P.isSemiformula hab hca hcb hf

lemma tleafB2 : bindT a (bindT c (bindT b (bindT b P))) = (binaryBody a b P).subst ![#'3, #'0] := by
  apply Bootstrapping.Semiformula.ext
  rw [binaryBody_subst a b P (3 : Fin 4) 0 hab]
  simpa using leafB2 P.isSemiformula hab hca hcb hf

lemma tleafB3 : bindT a (bindT c (bindT b (bindT a P))) = (binaryBody a b P).subst ![#'0, #'1] := by
  apply Bootstrapping.Semiformula.ext
  rw [binaryBody_subst a b P (0 : Fin 4) 1 hab]
  simpa using leafB3 P.isSemiformula hab hca hcb hf

lemma tleafB4 : bindT a (bindT c (bindT b (bindT a (bindT a (bindT b P))))) =
    (binaryBody a b P).subst ![#'1, #'0] := by
  apply Bootstrapping.Semiformula.ext
  rw [binaryBody_subst a b P (1 : Fin 6) 0 hab]
  simpa using leafB4 P.isSemiformula hab hca hcb hf

lemma tleafB5 : bindT a (bindT c (bindT b (bindT a (bindT a (bindT b (bindT b P)))))) =
    (binaryBody a b P).subst ![#'2, #'0] := by
  apply Bootstrapping.Semiformula.ext
  rw [binaryBody_subst a b P (2 : Fin 7) 0 hab]
  simpa using leafB5 P.isSemiformula hab hca hcb hf

/-- **Distinct labels: the named `∀a ¬nks` is the translated template.** -/
theorem nksB_identity :
    namedFormula a (nksN a b c P 🡒 ⊥) =
      translateFormula (fun _ : Fin 1 => binaryBody a b P) (Rewriting.emb nksB) := by
  simp only [nksN, closN, reqN, namedFormula, namedBody_bindT, bindT_imp, bindT_all, bindT_bot,
    memNamed, bindT_mem, termBindT_fvar, termBindT_bvar, Ne.symm hab, hca, Ne.symm hca, hcb,
    Ne.symm hcb, if_true, if_false]
  rw [tleafB1 P hab hca hcb hf, tleafB2 P hab hca hcb hf, tleafB3 P hab hca hcb hf,
    tleafB4 P hab hca hcb hf, tleafB5 P hab hca hcb hf]
  simp only [nksB, closB, reqRoot, reqInner, Rewriting.app_all, Rew.q_emb,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_bot,
    translateFormula_imp, tr_all, tr_bot, tr_rA, tr_mA]
  rfl

end Identities

section DiagonalIdentity

variable {a c : V} (P : Formula V ℒₛₑₜ) (hca : c ≠ a)
  (hf : ∀ depth : V, bindOneAt ℒₛₑₜ c depth P.val = P.val)
include hca hf

private lemma diag_subst {m : Nat} (i : Fin m) :
    ((binaryBody c a P).subst ![#'i, #'i]).val = bindOneAt ℒₛₑₜ a (i : V) P.val := by
  rw [binaryBody_subst c a P i i hca, hf]

lemma tleafD2 : bindT c (bindT a P) = (binaryBody c a P).subst ![#'0, #'0] := by
  apply Bootstrapping.Semiformula.ext
  rw [diag_subst P hca hf]
  simpa using leafD2 P.isSemiformula hca hf

lemma tleafD3 : bindT c (bindT a (bindT a P)) = (binaryBody c a P).subst ![#'0, #'0] := by
  apply Bootstrapping.Semiformula.ext
  rw [diag_subst P hca hf]
  simpa using leafD3 P.isSemiformula hca hf

lemma tleafD5 : bindT c (bindT a (bindT a (bindT a (bindT a P)))) =
    (binaryBody c a P).subst ![#'0, #'0] := by
  apply Bootstrapping.Semiformula.ext
  rw [diag_subst P hca hf]
  simpa using leafD5 P.isSemiformula hca hf

lemma tleafD6 : bindT c (bindT a (bindT a (bindT a (bindT a (bindT a P))))) =
    (binaryBody c a P).subst ![#'0, #'0] := by
  apply Bootstrapping.Semiformula.ext
  rw [diag_subst P hca hf]
  simpa using leafD6 P.isSemiformula hca hf

/-- **Coincident labels: the named `¬nks` is the translated diagonal template.** -/
theorem nksD_identity :
    (nksN a a c P 🡒 ⊥) =
      translateFormula (fun _ : Fin 1 => binaryBody c a P) (Rewriting.emb nksD) := by
  simp only [nksN, closN, reqN, namedFormula, namedBody_bindT, bindT_imp, bindT_all, bindT_bot,
    memNamed, bindT_mem, termBindT_fvar, termBindT_bvar, hca, Ne.symm hca, if_true, if_false]
  rw [tleafD2 P hca hf, tleafD3 P hca hf, tleafD5 P hca hf, tleafD6 P hca hf]
  simp only [nksD, closD, reqDiag1, reqDiag4, Rewriting.app_all, Rew.q_emb,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_bot,
    translateFormula_imp, tr_all, tr_bot, tr_rA, tr_mA]
  rfl

end DiagonalIdentity

/-! ## Assembly -/

/-- `nks` is congruent in its matrix. -/
theorem nksN_equiv (a b c : V) (p q : Formula V ℒₛₑₜ)
    (hpq : (𝗭𝗙 : SetTheory).internalize V ⊢ p 🡘 q) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nksN a b c p 🡘 nksN a b c q := by
  have hGen : ∀ (label : V) (r : V), Provable (𝗭𝗙 : SetTheory) r →
      Provable (𝗭𝗙 : SetTheory) (namedAll ℒₛₑₜ label r) := fun label _ hr => zf_provable_namedAll label hr
  have hreq : (𝗭𝗙 : SetTheory).internalize V ⊢ reqN b c p 🡘 reqN b c q := by
    unfold reqN
    apply namedFormula_equiv _ b (hGen b)
    apply ECC!_of_E!_of_E! hpq
    apply ECC!_of_E!_of_E! _ ⟨E_Id⟩
    apply namedFormula_equiv _ b (hGen b)
    exact ECC!_of_E!_of_E! hpq ⟨E_Id⟩
  unfold nksN
  apply namedFormula_equiv _ c (hGen c)
  refine ECC!_of_E!_of_E! ?_ (ECC!_of_E!_of_E! hreq ⟨E_Id⟩)
  unfold closN
  apply namedFormula_equiv _ b (hGen b)
  apply ECC!_of_E!_of_E! ⟨E_Id⟩
  apply ECC!_of_E!_of_E! _ ⟨E_Id⟩
  apply namedFormula_equiv _ a (hGen a)
  apply ECC!_of_E!_of_E! hpq
  apply ECC!_of_E!_of_E! _ ⟨E_Id⟩
  apply namedFormula_equiv _ a (hGen a)
  exact ECC!_of_E!_of_E! ⟨E_Id⟩ hreq

/-- A named universal instantiated at its own label is the body. -/
theorem namedFormula_self (a : V) (X : Formula V ℒₛₑₜ) :
    (namedBody a X).subst ![&'a] = X := by
  apply Bootstrapping.Semiformula.ext
  simpa [namedBody, Bootstrapping.Semiformula.val_substs, substs1] using
    bindOneAt_open X.isSemiformula a

/-- The matrix used in the templates: `⊤` for the code `0`, else the decoded matrix. -/
noncomputable def freshMatrix (c : V) : Formula V ℒₛₑₜ := by
  classical
  exact if c = 0 then ⊤ else decoded c

lemma freshMatrix_fresh (c depth : V) :
    bindOneAt ℒₛₑₜ c depth (freshMatrix c).val = (freshMatrix c).val := by
  classical
  by_cases hz : c = 0
  · simp [freshMatrix, hz]
  · simp only [freshMatrix, hz, if_false, decoded_val]
    exact positive_code_fresh c (lt_of_le_of_ne (by simp) (Ne.symm hz)) depth

lemma freshMatrix_equiv (c : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ decoded c 🡘 freshMatrix c := by
  classical
  by_cases hz : c = 0
  · subst hz
    simpa [freshMatrix] using decoded_zero_equiv_top ((𝗭𝗙 : SetTheory).internalize V)
  · simp only [freshMatrix, hz, if_false]
    exact ⟨E_Id⟩

/-- **The negated `nks` clause is an internal ZF theorem**, under the gates. -/
theorem zf_not_nks (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nksN a b c (decoded c) 🡒 ⊥ := by
  have he := nksN_equiv a b c _ _ (freshMatrix_equiv c)
  have hfresh := freshMatrix_fresh (V := V) c
  have hneg : (𝗭𝗙 : SetTheory).internalize V ⊢ nksN a b c (freshMatrix c) 🡒 ⊥ := by
    by_cases hab : a = b
    · subst hab
      rw [nksD_identity (freshMatrix c) hca hfresh]
      exact SeedBundleTemplates222.zf_nksD _
    · have hall : (𝗭𝗙 : SetTheory).internalize V ⊢
          namedFormula a (nksN a b c (freshMatrix c) 🡒 ⊥) := by
        rw [nksB_identity (freshMatrix c) hab hca hcb hfresh]
        exact SeedBundleTemplates222.zf_nksB _
      simpa only [namedFormula_self] using TProof.specialize! hall (&'a)
  exact C!_trans (C_of_E_mp! he) hneg

/-- The vacuity half of the bundle. -/
theorem zf_vrel (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ vrelN a b c := by
  have hv := decoded_wel_vacuity 𝗭𝗙 a b c hca hcb
  have hd : (𝗭𝗙 : SetTheory).internalize V ⊢ decoded (vrel a b c) := by
    rw [vrel_eq]
    exact (tprovable_iff_provable (σ := decoded _)).mpr hv
  have he := zf_decoded_circuit_equiv vrelTemplate a b c 0
  rw [interpret_vrel] at he
  exact (iff_of_E! he).mp hd

/-- **The decoded C222 seed bundle is an internal ZF theorem.** -/
theorem zf_decoded_bundle222_provable (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundle222 a b c)) := by
  classical
  have hv := zf_vrel a b c hca hcb
  have hn := zf_not_nks a b c hca hcb
  have hb : (𝗭𝗙 : SetTheory).internalize V ⊢
      ((vrelN a b c 🡒 nksN a b c (decoded c)) 🡒 ⊥) := by
    cl_prover [hv, hn]
  have he := zf_decoded_circuit_equiv bundleTemplate a b c 0
  rw [interpret_bundle] at he
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! he).mpr hb

end LeanProofs.ZFCinPA.ModelCodedDecoderBundle222
