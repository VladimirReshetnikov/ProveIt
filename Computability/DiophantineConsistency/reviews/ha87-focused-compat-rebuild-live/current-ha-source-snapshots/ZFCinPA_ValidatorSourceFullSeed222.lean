import ZFCinPA.ValidatorImplicationContext
import ZFCinPA.ValidatorSeedPadding222
import ZFCinPA.ValidatorSourceNegation222
import ZFCinPA.ValidatorExistentialRules222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Literal full-seed source images for the actual C222 checker. This file
retains both closure and root request; no raw GIC/CP or tagged interpretation
is used as a premise. Arbitrary source matrices are internally coded. -/
namespace LeanProofs.ZFCinPA.ValidatorSourceFullSeed222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorEind222
open ValidatorSeedWitness222 ValidatorSeedImage222 ValidatorSeedPadding222
open ValidatorFormulaEncoder222 ValidatorEnvironmentVacuity222
open ValidatorEnvironmentAlpha222 ValidatorEnvironmentStreams222
open ValidatorAtomicTransport222 ValidatorEindContext222
open ValidatorEnvironmentSubstitution222 ValidatorExistentialRules222
open ValidatorSourceNegation222
open ArithmeticSeedTemplates222 (req clos)
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "d0" => (ValidatorImplicationContext.h0 CProv)
local notation "d1" => (ValidatorImplicationContext.h1 CProv)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)
private lemma lift {p : V} (h : V) (hp : CProv p) : CProv (wim h p) :=
  cProv_mp (cProv_k p h) hp

theorem bounded_seed_pair (bound P a b : V) (ha : a≤bound) (hb : b≤bound) :
    CProv (ex (seedLabel bound P)
      (conj (clos a b (seedLabel bound P) P) (req b (seedLabel bound P) P))) := by
  let c := seedLabel bound P
  have hP := seedLabel_equiv bound P
  have point : CProv (wim (conj (clos a b c c) (req b c c))
      (conj (clos a b c P) (req b c P))) := by
    apply conj_under
    · exact compose (conj_left _ _) (closure_congr a b c c P hP.1 hP.2).1
    · exact compose (conj_right _ _) (request_congr b c c P hP.1 hP.2).1
  exact cProv_mp (ex_mono c point)
    (seed_pair a b c (ne_of_gt (lt_of_le_of_lt ha (bound_lt_seedLabel bound P)))
      (ne_of_gt (lt_of_le_of_lt hb (bound_lt_seedLabel bound P))))

private lemma iff_conj {p p' q q' : V} (hp : CodeIff p p') (hq : CodeIff q q') :
    CodeIff (conj p q) (conj p' q') :=
  codeIff_neg (codeIff_imp hp (codeIff_neg hq))
private lemma iff_ex (x : V) {p q : V} (h : CodeIff p q) :
    CodeIff (ex x p) (ex x q) := codeIff_neg (codeIff_all x (codeIff_neg h))
private lemma under_of_iff (h : V) {p q : V} (hpq : CodeIff p q) : EqUnder h p q :=
  ⟨lift h hpq.1,lift h hpq.2⟩
private lemma under_trans {h p q r : V} (hpq : EqUnder h p q) (hqr : EqUnder h q r) :
    EqUnder h p r :=
  ⟨ded2 (.mp (.mp (.ax hqr.1) d1) (.mp (.mp (.ax hpq.1) d1) d0)),
   ded2 (.mp (.mp (.ax hpq.2) d1) (.mp (.mp (.ax hqr.2) d1) d0))⟩
private lemma under_pre {h h' p q : V} (hh : CProv (wim h h')) (hpq : EqUnder h' p q) :
    EqUnder h p q := ⟨compose hh hpq.1,compose hh hpq.2⟩
private lemma under_all (x : V) {h p q : V} (hv : Vac x h) (hpq : EqUnder h p q) :
    EqUnder h (wal x p) (wal x q) := by
  constructor
  · exact ded2 (.mp (.mp (.ax (all_distribution x p q))
      (.mp (.ax (compose hv (all_mono x hpq.1))) d1)) d0)
  · exact ded2 (.mp (.mp (.ax (all_distribution x q p))
      (.mp (.ax (compose hv (all_mono x hpq.2))) d1)) d0)
private lemma under_ex (x : V) {h p q : V} (hv : Vac x h) (hpq : EqUnder h p q) :
    EqUnder h (ex x p) (ex x q) := eqUnder_neg (under_all x hv (eqUnder_neg hpq))
private lemma under_member {h x x' y y' : V}
    (hx : CProv (wim h (Eind x x'))) (hy : CProv (wim h (Eind y y'))) :
    EqUnder h (wel x y) (wel x' y') := by
  constructor
  · exact ded2 (.mp (.mp (.mp (.ax (rel_congr x x' y y'))
      (.mp (.ax hx) d1)) (.mp (.ax hy) d1)) d0)
  · exact ded2 (.mp (.mp (.mp (.ax (rel_congr x' x y' y))
      (.mp (.ax (compose hx (eind_symm x x'))) d1))
      (.mp (.ax (compose hy (eind_symm y y'))) d1)) d0)

/-- Finite binder conversion from actual Eind certificates. Cross-body
vacuity is explicit; neither binder is claimed vacuous in its own body. -/
private lemma rename_all (x y p q : V) (h : EqUnder (Eind x y) p q)
    (hx : Vac x q) (hy : Vac y p) : CodeIff (wal x p) (wal y q) := by
  have f (x y p q : V) (h : CProv (wim (Eind x y) (wim p q)))
      (hx : Vac x q) (hy : Vac y p) : CProv (wim (wal x p) (wal y q)) := by
    have he := compose (Eq_Eind x y) h
    exact cProv_mp (all_relational 0 p q x y (lift 0 he)
      (vac_truth x) hx (vac_truth y) (vac_all x hy)) cProv_truth
  exact ⟨f x y p q h.1 hx hy,
    f y x q p (compose (eind_symm y x) h.2) hy hx⟩
private lemma rename_ex (x y p q : V) (h : EqUnder (Eind x y) p q)
    (hx : Vac x q) (hy : Vac y p) : CodeIff (ex x p) (ex y q) :=
  codeIff_neg (rename_all x y (neg p) (neg q) (eqUnder_neg h)
    (vac_neg hx) (vac_neg hy))

section Matrix

private lemma freshPair_same (F B s t : V)
    (hs : StreamFree s F) (ht : StreamFree t F)
    (hsB : StreamEnv s B) (htB : StreamEnv t B) (hap : Apart s t) :
    FreshPair F B B s t := ⟨hs,ht,hsB,hsB,htB,htB,hap⟩

/-- Same-stack stream transport, including overlapping streams. The
intermediate starts above the whole stack, not just its displayed labels. -/
theorem encode_stack_relabel {n p : V} (hp : IsSemiformula ℒₛₑₜ n p)
    (F B s t : V) (hB : len B=n) (hs : StreamFree s F) (ht : StreamFree t F)
    (hsB : StreamEnv s B) (htB : StreamEnv t B) :
    CodeIff (encode F B s p) (encode F B t p) := by
  have direct (s t : V) (hs : StreamFree s F) (ht : StreamFree t F)
      (hsB : StreamEnv s B) (htB : StreamEnv t B) (hap : Apart s t) :
      CodeIff (encode F B s p) (encode F B t p) := by
    have h := encode_eq_under hp F B B s t hB hB
      (freshPair_same F B s t hs ht hsB htB hap)
    exact ⟨cProv_mp h.1 (eindContext_diagonal B),cProv_mp h.2 (eindContext_diagonal B)⟩
  classical
  by_cases hmod : s%2=t%2
  · let u := alternateStart (F+B+B) s
    have hu := alternateStart_resources F B B s
    have htu : Apart t u := apart_of_mod_ne (by
      rw [←hmod]; exact alternateStart_mod_ne (F+B+B) s)
    exact codeIff_trans (direct s u hs hu.1 hsB hu.2.1 hu.2.2.2)
      (codeIff_symm (direct t u ht hu.1 htB hu.2.1 htu))
  · exact direct s t hs ht hsB htB (apart_of_mod_ne hmod)

private lemma stream_pair (r x y : V) (hx : x<r) (hy : y<r) :
    StreamEnv r (y∷x∷(0 : V)) := by
  intro k
  exact avoid_cons (avoid_cons (avoid_nil _) ((stream_of_lt hx) k).symm)
    ((stream_of_lt hy) k).symm

def matrix (F r p x y : V) : V := encode F (y∷x∷0) r p

/-- A fixed fresh matrix stream supports congruence of both live slots.
The opposite-parity intermediary is above both complete bound stacks. -/
theorem matrix_congr {p : V} (hp : IsSemiformula ℒₛₑₜ 2 p)
    (F r x x' y y' h : V) (hr : StreamFree r F)
    (hx : x<r) (hx' : x'<r) (hy : y<r) (hy' : y'<r)
    (heX : CProv (wim h (Eind x x'))) (heY : CProv (wim h (Eind y y'))) :
    EqUnder h (matrix F r p x y) (matrix F r p x' y') := by
  let B := y∷x∷(0 : V)
  let B' := y'∷x'∷(0 : V)
  let u := alternateStart (F+B+B') r
  have hu := alternateStart_resources F B B' r
  have hBr : StreamEnv r B := stream_pair r x y hx hy
  have hB'r : StreamEnv r B' := stream_pair r x' y' hx' hy'
  have ha := encode_eq_under hp F B B' r u (by simp [B,one_add_one_eq_two]) (by simp [B',one_add_one_eq_two])
    ⟨hr,hu.1,hBr,hB'r,hu.2.1,hu.2.2.1,hu.2.2.2⟩
  have hb := encode_stack_relabel hp F B' u r (by simp [B',one_add_one_eq_two])
    hu.1 hr hu.2.2.1 hB'r
  have hc : CProv (wim h (eindContext B B')) := by
    apply compose _ (eindContext_cons_backward (x∷0) (x'∷0) y y')
    apply conj_under heY
    apply compose _ (eindContext_cons_backward 0 0 x x')
    exact conj_under heX (by simpa using lift h (cProv_truth (V := V)))
  exact under_trans (under_pre hc ha) (under_of_iff h hb)

theorem matrix_vac {p : V} (hp : IsSemiformula ℒₛₑₜ 2 p)
    (F r x y z : V) (hzF : FreeAvoid z F) (hzr : StreamAvoid z r)
    (hzx : z≠x) (hzy : z≠y) : Vac z (matrix F r p x y) :=
  encode_vac hp F (y∷x∷0) r z (by simp [one_add_one_eq_two]) hzF
    (avoid_cons (avoid_cons (avoid_nil z) hzx) hzy) hzr

end Matrix

/-- Fixed membership atoms at their literal source binder depths. -/
def seedMem (n : ℕ) (i j : Fin n) : SetTheorySemiproposition n :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#i,#j]

def seedSubset : SetTheorySemiproposition 5 :=
  ∀⁰ (seedMem 6 0 1 🡒 seedMem 6 0 3)

theorem seedSubset_quote :
    (⌜seedSubset⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 5) =
      ∀⁰ ((⌜seedMem 6 0 1⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 6) 🡒 ⌜seedMem 6 0 3⌝) := by
  simp [seedSubset]

/-- K's slot0 is output; slot1 is input. Original free parameters survive. -/
def fullSeedBodyMeta (K : SetTheorySemiproposition 2) : SetTheoryProposition :=
  ∀⁰ ∃⁰ ((∀⁰ (seedMem 3 0 1 🡒 ∃⁰
      ((K ⇜ ![(#1 : SyntacticSemiterm ℒₛₑₜ 4),#0]) ⋏
        (∀⁰ (seedSubset 🡒 ∀⁰
          ((K ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 6),#1]) 🡒
            ∃⁰ ((K ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 7),#2]) ⋏ seedMem 7 0 5))))))) ⋏
    (∀⁰ ((K ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 3),#2]) 🡒
      ∃⁰ ((K ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 4),#3]) ⋏ seedMem 4 0 2))))

abbrev seedPairMatrix (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) : Bootstrapping.Semiformula V ℒₛₑₜ 2 :=
  ((∀⁰ ((⌜seedMem 3 0 1⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3) 🡒 ∃⁰
      ((K.subst ![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝,⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝]) ⋏
        (∀⁰ ((⌜seedSubset⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 5) 🡒 ∀⁰
          ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 6)⌝,⌜(#1 : SyntacticSemiterm ℒₛₑₜ 6)⌝]) 🡒
            ∃⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 7)⌝,⌜(#2 : SyntacticSemiterm ℒₛₑₜ 7)⌝]) ⋏
              (⌜seedMem 7 0 5⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 7)))))))) ⋏
    (∀⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝,⌜(#2 : SyntacticSemiterm ℒₛₑₜ 3)⌝]) 🡒
      ∃⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝,⌜(#3 : SyntacticSemiterm ℒₛₑₜ 4)⌝]) ⋏
        (⌜seedMem 4 0 2⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 4)))))

def fullSeedBody (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Bootstrapping.Semiformula V ℒₛₑₜ 0 :=
  ∀⁰ ∃⁰ seedPairMatrix K

theorem fullSeedBody_quote (K : SetTheorySemiproposition 2) :
    (⌜fullSeedBodyMeta K⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 0) = fullSeedBody ⌜K⌝ := by
  unfold fullSeedBodyMeta fullSeedBody seedPairMatrix
  simp [Matrix.comp_vecCons',Matrix.constant_eq_singleton]

def fullSeedBodyVal (k : V) : V :=
  ^∀ ^∃ ((^∀ (Bootstrapping.imp ℒₛₑₜ (⌜seedMem 3 0 1⌝ : V) (^∃
      ((subst ℒₛₑₜ (^#1∷^#0∷0) k) ^⋏
        ^∀ (Bootstrapping.imp ℒₛₑₜ (⌜seedSubset⌝ : V) (^∀
          (Bootstrapping.imp ℒₛₑₜ (subst ℒₛₑₜ (^#0∷^#1∷0) k)
            (^∃ ((subst ℒₛₑₜ (^#0∷^#2∷0) k) ^⋏ (⌜seedMem 7 0 5⌝ : V)))))))))) ^⋏
    (^∀ (Bootstrapping.imp ℒₛₑₜ (subst ℒₛₑₜ (^#0∷^#2∷0) k)
      (^∃ ((subst ℒₛₑₜ (^#0∷^#3∷0) k) ^⋏ (⌜seedMem 4 0 2⌝ : V))))))

theorem fullSeedBodyVal_eq (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    fullSeedBodyVal K.val = (fullSeedBody K).val := by
  simp [fullSeedBodyVal,fullSeedBody,seedPairMatrix,FirstOrder.Semiformula.quote_def]

/-- Exact raw-code binding for the meta-level body, including all five
substitution vectors. This is syntax equality, not a semantic equivalence. -/
theorem fullSeedBodyVal_quote (K : SetTheorySemiproposition 2) :
    fullSeedBodyVal (⌜K⌝ : V) = (⌜fullSeedBodyMeta K⌝ : V) := by
  rw [FirstOrder.Semiformula.quote_def K,fullSeedBodyVal_eq,
    FirstOrder.Semiformula.quote_def,fullSeedBody_quote]

/- The following finite interface packages only already justified matrix
congruence and vacuity, not a seed or source-image premise. Its actual typed
instance below is obtained from matrix_congr/matrix_vac. -/
private structure Frame where
  val : V → V → V
  small : V → Prop
  fresh : V → Prop
  congr : ∀ h x x' y y', small x → small x' → small y → small y' →
    CProv (wim h (Eind x x')) → CProv (wim h (Eind y y')) →
    EqUnder h (val x y) (val x' y')
  vac : ∀ x y z, fresh z → z≠x → z≠y → Vac z (val x y)

private def typedFrame {p : V}
    (hp : IsSemiformula ℒₛₑₜ 2 p) (F r : V) (hr : StreamFree r F) : Frame (V := V) where
  val := matrix F r p
  small := fun x => x<r
  fresh := fun z => FreeAvoid z F ∧ StreamAvoid z r
  congr := fun h x x' y y' hx hx' hy hy' heX heY =>
    matrix_congr hp F r x x' y y' h hr hx hx' hy hy' heX heY
  vac := fun x y z hz hzx hzy => matrix_vac hp F r x y z hz.1 hz.2 hzx hzy

private lemma vac_ex (x : V) {z p : V} (h : Vac z p) : Vac z (ex x p) :=
  vac_neg (vac_all x (vac_neg h))
private def request (A : Frame (V := V)) (a c y z : V) : V :=
  wal y (wim (A.val a y) (ex z (conj (A.val a z) (wel z c))))
private def subcode (a b w : V) : V := wal w (wim (wel w a) (wel w b))
private def closure (A : Frame (V := V)) (b c x v w z : V) : V :=
  wal b (wim (wel b c)
    (ex x (conj (A.val x b) (wal v (wim (subcode v b w) (request A v c w z))))))

private lemma request_vac (A : Frame (V := V)) (a c y z t : V)
    (hf : A.fresh t) (ha : t≠a) (hc : t≠c) (hy : t≠y) (hz : t≠z) :
    Vac t (request A a c y z) :=
  vac_all y (vac_imp (A.vac a y t hf ha hy)
    (vac_ex z (vac_conj (A.vac a z t hf ha hz) (vac_rel z c t hz hc))))
private lemma subcode_vac (a b w t : V) (ha : t≠a) (hb : t≠b) (hw : t≠w) :
    Vac t (subcode a b w) := vac_all w (vac_imp (vac_rel w a t hw ha) (vac_rel w b t hw hb))

private lemma request_under (A : Frame (V := V)) (h a a' c c' y z : V)
    (ha : A.small a) (ha' : A.small a') (hy : A.small y) (hz : A.small z)
    (heA : CProv (wim h (Eind a a'))) (heC : CProv (wim h (Eind c c')))
    (vy : Vac y h) (vz : Vac z h) :
    EqUnder h (request A a c y z) (request A a' c' y z) := by
  apply under_all y vy
  apply eqUnder_imp
  · exact A.congr h a a' y y ha ha' hy hy heA (lift h (eind_refl y))
  · apply under_ex z vz
    exact eqUnder_conj
      (A.congr h a a' z z ha ha' hz hz heA (lift h (eind_refl z)))
      (under_member (lift h (eind_refl z)) heC)

private lemma subcode_under (h a a' b b' w : V)
    (heA : CProv (wim h (Eind a a'))) (heB : CProv (wim h (Eind b b')))
    (vw : Vac w h) : EqUnder h (subcode a b w) (subcode a' b' w) :=
  under_all w vw (eqUnder_imp (under_member (lift h (eind_refl w)) heA)
    (under_member (lift h (eind_refl w)) heB))

/-- Normalize the request's inner negative universal and move only its
inner output binder. The outer output binder remains unchanged. -/
private lemma request_native_inner (A : Frame (V := V)) (a b c z : V)
    (ha : A.small a) (hb : A.small b) (hz : A.small z)
    (fb : A.fresh b) (fz : A.fresh z)
    (hba : b≠a) (hbc : b≠c) (hbz : b≠z) (hza : z≠a) (hzc : z≠c) :
    CodeIff (req b c (A.val a b)) (request A a c b z) := by
  have hm := A.congr (Eind b z) a a b z ha ha hb hz
    (lift _ (eind_refl a)) (Kalmar.self_imp cProv_classical _)
  have he : CodeIff (ex b (conj (A.val a b) (wel b c)))
      (ex z (conj (A.val a z) (wel z c))) :=
    rename_ex b z _ _ (eqUnder_conj hm
      (under_member (Kalmar.self_imp cProv_classical _) (lift _ (eind_refl c))))
      (vac_conj (A.vac a z b fb hba hbz) (vac_rel z c b hbz hbc))
      (vac_conj (A.vac a b z fz hza hbz.symm) (vac_rel b c z hbz.symm hzc))
  exact codeIff_all b (codeIff_imp (codeIff_refl _)
    (codeIff_trans (not_all_imp_ex_conj b (A.val a b) (wel b c)) he))

private lemma request_move_output (A : Frame (V := V)) (a c b u z : V)
    (ha : A.small a) (hb : A.small b) (hu : A.small u)
    (fb : A.fresh b) (fu : A.fresh u)
    (hba : b≠a) (hbc : b≠c) (hbu : b≠u) (hbz : b≠z)
    (hua : u≠a) (huc : u≠c) (huz : u≠z) :
    CodeIff (request A a c b z) (request A a c u z) := by
  apply rename_all b u
  · exact eqUnder_imp (A.congr (Eind b u) a a b u ha ha hb hu
      (lift _ (eind_refl a)) (Kalmar.self_imp cProv_classical _)) (eqUnder_refl _ _)
  · exact vac_imp (A.vac a u b fb hba hbu)
      (vac_ex z (vac_conj (A.vac a z b fb hba hbz) (vac_rel z c b hbz hbc)))
  · exact vac_imp (A.vac a b u fu hua hbu.symm)
      (vac_ex z (vac_conj (A.vac a z u fu hua huz) (vac_rel z c u huz huc)))

private lemma subcode_rename (a b c w : V)
    (hca : c≠a) (hcb : c≠b) (hcw : c≠w) (hwa : w≠a) (hwb : w≠b) :
    CodeIff (subcode a b c) (subcode a b w) := by
  apply rename_all c w
  · exact eqUnder_imp
      (under_member (Kalmar.self_imp cProv_classical _) (lift _ (eind_refl a)))
      (under_member (Kalmar.self_imp cProv_classical _) (lift _ (eind_refl b)))
  · exact vac_imp (vac_rel w a c hcw hca) (vac_rel w b c hcw hcb)
  · exact vac_imp (vac_rel c a w hcw.symm hwa) (vac_rel c b w hcw.symm hwb)

private structure Layout (A : Frame (V := V)) where
  label : Fin 7 → V
  injective : Function.Injective label
  small : ∀ i, A.small (label i)
  fresh : ∀ i, A.fresh (label i)

private lemma Layout.ne {A : Frame (V := V)} (L : Layout A) {i j : Fin 7} (h : i≠j) :
    L.label i≠L.label j := fun e => h (L.injective e)

private def tail (A : Frame (V := V)) (b c v w z : V) : V :=
  wal v (wim (subcode v b w) (request A v c w z))

private lemma tail_vac (A : Frame (V := V)) (b c v w z t : V)
    (hf : A.fresh t) (hb : t≠b) (hc : t≠c) (hv : t≠v) (hw : t≠w) (hz : t≠z) :
    Vac t (tail A b c v w z) :=
  vac_all v (vac_imp (subcode_vac v b w t hv hb hw)
    (request_vac A v c w z t hf hv hc hw hz))

/-- Six ordinary role labels plus the independent container slot. Reused
native binders are changed from the inside out, so no self-body vacuity is
needed when the same native name is shadowed. -/
private lemma closure_native (A : Frame (V := V)) (L : Layout A) (c : V)
    (hc : ∀ i, c≠L.label i) :
    CodeIff (clos (L.label 0) (L.label 2) c (A.val (L.label 0) (L.label 2)))
      (closure A (L.label 2) c (L.label 3) (L.label 4) (L.label 5) (L.label 6)) := by
  let a := L.label 0
  let b := L.label 2
  let x := L.label 3
  let v := L.label 4
  let w := L.label 5
  let z := L.label 6
  have hr : CodeIff (req b c (A.val a b)) (request A a c w z) :=
    codeIff_trans
      (request_native_inner A a b c z (L.small 0) (L.small 2) (L.small 6)
        (L.fresh 2) (L.fresh 6) (L.ne (by decide)) (hc 2).symm
        (L.ne (by decide)) (L.ne (by decide)) (hc 6).symm)
      (request_move_output A a c b w z (L.small 0) (L.small 2) (L.small 5)
        (L.fresh 2) (L.fresh 5) (L.ne (by decide)) (hc 2).symm
        (L.ne (by decide)) (L.ne (by decide)) (L.ne (by decide))
        (hc 5).symm (L.ne (by decide)))
  have hs := subcode_rename a b c w (hc 0) (hc 2) (hc 5)
    (L.ne (by decide)) (L.ne (by decide))
  have hvw : Vac w (Eind a v) := Eind_vac a v w (L.ne (by decide)) (L.ne (by decide))
  have hvz : Vac z (Eind a v) := Eind_vac a v z (L.ne (by decide)) (L.ne (by decide))
  have hn : CodeIff (wal a (wim (subcode a b c) (req b c (A.val a b))))
      (tail A b c v w z) := by
    apply codeIff_trans (codeIff_all a (codeIff_imp hs hr))
    apply rename_all a v
    · exact eqUnder_imp
        (subcode_under (Eind a v) a v b b w (Kalmar.self_imp cProv_classical _)
          (lift _ (eind_refl b)) hvw)
        (request_under A (Eind a v) a v c c w z (L.small 0) (L.small 4)
          (L.small 5) (L.small 6) (Kalmar.self_imp cProv_classical _)
          (lift _ (eind_refl c)) hvw hvz)
    · exact vac_imp (subcode_vac v b w a (L.ne (by decide)) (L.ne (by decide)) (L.ne (by decide)))
        (request_vac A v c w z a (L.fresh 0) (L.ne (by decide)) (hc 0).symm
          (L.ne (by decide)) (L.ne (by decide)))
    · exact vac_imp (subcode_vac a b w v (L.ne (by decide)) (L.ne (by decide)) (L.ne (by decide)))
        (request_vac A a c w z v (L.fresh 4) (L.ne (by decide)) (hc 4).symm
          (L.ne (by decide)) (L.ne (by decide)))
  have he : CodeIff (ex a (conj (A.val a b) (tail A b c v w z)))
      (ex x (conj (A.val x b) (tail A b c v w z))) := by
    apply rename_ex a x
    · exact eqUnder_conj
        (A.congr (Eind a x) a x b b (L.small 0) (L.small 3) (L.small 2) (L.small 2)
          (Kalmar.self_imp cProv_classical _) (lift _ (eind_refl b)))
        (eqUnder_refl _ _)
    · exact vac_conj (A.vac x b a (L.fresh 0) (L.ne (by decide)) (L.ne (by decide)))
        (tail_vac A b c v w z a (L.fresh 0) (L.ne (by decide)) (hc 0).symm
          (L.ne (by decide)) (L.ne (by decide)) (L.ne (by decide)))
    · exact vac_conj (A.vac a b x (L.fresh 3) (L.ne (by decide)) (L.ne (by decide)))
        (tail_vac A b c v w z x (L.fresh 3) (L.ne (by decide)) (hc 3).symm
          (L.ne (by decide)) (L.ne (by decide)) (L.ne (by decide)))
  exact codeIff_all b (codeIff_imp (codeIff_refl _)
    (codeIff_trans (not_all_imp_ex_conj a (A.val a b)
      (wal a (wim (subcode a b c) (req b c (A.val a b)))))
      (codeIff_trans (iff_ex a (iff_conj (codeIff_refl _) hn)) he)))

private def pairBody (A : Frame (V := V)) (L : Layout A) (c : V) : V :=
  conj (closure A (L.label 2) c (L.label 3) (L.label 4) (L.label 5) (L.label 6))
    (request A (L.label 0) c (L.label 2) (L.label 3))

private lemma pair_native (A : Frame (V := V)) (L : Layout A) (c : V)
    (hc : ∀ i, c≠L.label i) :
    CodeIff (conj (clos (L.label 0) (L.label 2) c (A.val (L.label 0) (L.label 2)))
      (req (L.label 2) c (A.val (L.label 0) (L.label 2)))) (pairBody A L c) :=
  iff_conj (closure_native A L c hc)
    (request_native_inner A (L.label 0) (L.label 2) c (L.label 3)
      (L.small 0) (L.small 2) (L.small 3) (L.fresh 2) (L.fresh 3)
      (L.ne (by decide)) (hc 2).symm (L.ne (by decide))
      (L.ne (by decide)) (hc 3).symm)

private lemma pair_vac (A : Frame (V := V)) (L : Layout A) (c t : V)
    (hf : A.fresh t) (hc : t≠c)
    (h0 : t≠L.label 0) (h2 : t≠L.label 2) (h3 : t≠L.label 3)
    (h4 : t≠L.label 4) (h5 : t≠L.label 5) (h6 : t≠L.label 6) :
    Vac t (pairBody A L c) :=
  vac_conj
    (vac_all (L.label 2) (vac_imp (vac_rel _ _ t h2 hc)
      (vac_ex (L.label 3) (vac_conj (A.vac _ _ t hf h3 h2)
        (tail_vac A _ _ _ _ _ t hf h2 hc h4 h5 h6)))))
    (request_vac A _ _ _ _ t hf h0 hc h2 h3)

private lemma pair_container (A : Frame (V := V)) (L : Layout A) (c d : V)
    (hc : ∀ i, c≠L.label i)
    (hd : ∀ i : Fin 7, i≠1 → d≠L.label i) :
    EqUnder (Eind c d) (pairBody A L c) (pairBody A L d) := by
  have hv (i : Fin 7) (hi : i≠1) : Vac (L.label i) (Eind c d) :=
    Eind_vac c d _ (hc i).symm (hd i hi).symm
  have er := Kalmar.self_imp cProv_classical (Eind c d)
  apply eqUnder_conj
  · apply under_all (L.label 2) (hv 2 (by decide))
    apply eqUnder_imp
    · exact under_member (lift _ (eind_refl _)) er
    · apply under_ex (L.label 3) (hv 3 (by decide))
      apply eqUnder_conj (eqUnder_refl _ _)
      apply under_all (L.label 4) (hv 4 (by decide))
      apply eqUnder_imp (eqUnder_refl _ _)
      exact request_under A _ (L.label 4) (L.label 4) c d (L.label 5) (L.label 6)
        (L.small 4) (L.small 4) (L.small 5) (L.small 6)
        (lift _ (eind_refl _)) er (hv 5 (by decide)) (hv 6 (by decide))
  · exact request_under A _ (L.label 0) (L.label 0) c d (L.label 2) (L.label 3)
      (L.small 0) (L.small 0) (L.small 2) (L.small 3)
      (lift _ (eind_refl _)) er (hv 2 (by decide)) (hv 3 (by decide))

private lemma seed_binder (A : Frame (V := V)) (L : Layout A) (c : V)
    (hc : ∀ i, c≠L.label i) (fc : A.fresh c) :
    CodeIff (ex c (conj
      (clos (L.label 0) (L.label 2) c (A.val (L.label 0) (L.label 2)))
      (req (L.label 2) c (A.val (L.label 0) (L.label 2)))))
      (ex (L.label 1) (pairBody A L (L.label 1))) := by
  apply codeIff_trans (iff_ex c (pair_native A L c hc))
  apply rename_ex c (L.label 1)
  · exact pair_container A L c (L.label 1) hc (fun i hi => L.ne hi.symm)
  · exact pair_vac A L _ c fc (hc 1) (hc 0) (hc 2) (hc 3) (hc 4) (hc 5) (hc 6)
  · exact pair_vac A L _ (L.label 1) (L.fresh 1) (hc 1).symm
      (L.ne (by decide)) (L.ne (by decide)) (L.ne (by decide))
      (L.ne (by decide)) (L.ne (by decide)) (L.ne (by decide))

section TypedImage
private abbrev SF (n : ℕ) := Bootstrapping.Semiformula V ℒₛₑₜ n

private def role (s : V) : ℕ → V
  | 0 => s
  | n+1 => role s n+2
private lemma role_eq (s : V) (n : ℕ) : role s n=s+2*(n : V) := by
  induction n with
  | zero => simp [role]
  | succ n ih => simp only [role,ih,coe_add_one]; ring
private lemma role_lt (s : V) {i j : ℕ} (h : i<j) : role s i<role s j := by
  simp only [role_eq,add_lt_add_iff_left]
  exact mul_lt_mul_of_pos_left (by exact_mod_cast h) (by simp)
private lemma role_free (F s : V) (hs : StreamFree s F) (i : ℕ) :
    FreeAvoid (role s i) F := by simpa only [role_eq] using hs (i : V)
private lemma role_stream (F s : V) (hs : StreamFree s F) (i : ℕ) :
    StreamFree (role s i) F := by
  intro j
  have h := hs ((i : V)+j)
  convert h using 1
  simp only [role_eq]
  ring
private def canonicalLayout (K : SF (V := V) 2) (F s : V) (hs : StreamFree s F) :
    Layout (typedFrame K.isSemiformula F (role s 7) (role_stream F s hs 7)) where
  label i := role s i.val
  injective := by
    intro i j hij
    by_contra h
    rcases lt_or_gt_of_ne (Fin.val_injective.ne h) with hlt|hgt
    · exact (ne_of_lt (role_lt s hlt)) hij
    · exact (ne_of_gt (role_lt s hgt)) hij
  small i := role_lt s i.isLt
  fresh i := ⟨role_free F s hs i.val,stream_of_lt (role_lt s i.isLt)⟩

private lemma enc_imp (F B s : V) {n : ℕ} (p q : SF (V := V) n) :
    CodeIff (encode F B s (p 🡒 q).val)
      (wim (encode F B s p.val) (encode F B s q.val)) := by
  change CodeIff (encode F B s ((∼p) ⋎ q).val) _
  rw [Bootstrapping.Semiformula.val_or,
    encode_or F B s (∼p).isUFormula q.isUFormula]
  exact codeIff_imp (codeIff_neg_swap (encode_neg p.isSemiformula F B s)) (codeIff_refl _)
private lemma enc_impIff (F B s : V) {n : ℕ} (p q : SF (V := V) n) {a b : V}
    (hp : CodeIff (encode F B s p.val) a) (hq : CodeIff (encode F B s q.val) b) :
    CodeIff (encode F B s (p 🡒 q).val) (wim a b) :=
  codeIff_trans (enc_imp F B s p q) (codeIff_imp hp hq)
private lemma enc_allIff (F B s : V) {n : ℕ} (p : SF (V := V) (n+1)) {a : V}
    (hp : CodeIff (encode F (s∷B) (s+2) p.val) a) :
    CodeIff (encode F B s (∀⁰ p).val) (wal s a) := by
  rw [Bootstrapping.Semiformula.val_all,encode_all F B s p.isUFormula]
  exact codeIff_all s hp
private lemma enc_exIff (F B s : V) {n : ℕ} (p : SF (V := V) (n+1)) {a : V}
    (hp : CodeIff (encode F (s∷B) (s+2) p.val) a) :
    CodeIff (encode F B s (∃⁰ p).val) (ex s a) := by
  rw [Bootstrapping.Semiformula.val_exs,encode_exs F B s p.isUFormula]
  exact iff_ex s hp
private lemma enc_conjIff (F B s : V) {n : ℕ} (p q : SF (V := V) n) {a b : V}
    (hp : CodeIff (encode F B s p.val) a) (hq : CodeIff (encode F B s q.val) b) :
    CodeIff (encode F B s (p ⋏ q).val) (conj a b) := by
  rw [Bootstrapping.Semiformula.val_and,encode_and F B s p.isUFormula q.isUFormula]
  exact iff_conj hp hq

private lemma enc_mem {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (⌜seedMem n i j⌝ : SF (V := V) n).val = wel B.[(i : V)] B.[(j : V)] := by
  have hu := (⌜seedMem n i j⌝ : SF (V := V) n).isUFormula
  change IsUFormula ℒₛₑₜ
    (Bootstrapping.Semiformula.rel Language.Mem.mem
      ![Bootstrapping.Semiterm.bvar i,Bootstrapping.Semiterm.bvar j]).val at hu
  change encode F B s (Bootstrapping.Semiformula.rel Language.Mem.mem
      ![Bootstrapping.Semiterm.bvar i,Bootstrapping.Semiterm.bvar j]).val = _
  rw [Bootstrapping.Semiformula.rel_val] at hu
  rw [Bootstrapping.Semiformula.rel_val,
    encode_rel F B s (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2]
  have hv := (IsUFormula.rel.mp hu).2
  have h0 := ValidatorEnvironmentLabels254.TermLabels.vec_nth F B hv (show (0 : V)<↑(2 : ℕ) by simp)
  have h1 := ValidatorEnvironmentLabels254.TermLabels.vec_nth F B hv (show (1 : V)<↑(2 : ℕ) by simp)
  simp only [atom,nth_adjoin_zero,nth_adjoin_one]
  rw [if_neg (by change ((1 : ℕ) : V)≠0; simp),h0,h1]
  simp [Matrix.vecHead,Matrix.vecTail]

private lemma enc_copy (K : SF (V := V) 2) (F B s r : V) {n : ℕ} (i j : Fin n)
    (hs : StreamFree s F) (hr : StreamFree r F)
    (hsi : B.[(i : V)]<s) (hsj : B.[(j : V)]<s)
    (hri : B.[(i : V)]<r) (hrj : B.[(j : V)]<r) :
    CodeIff (encode F B s (K.subst (m := n)
      ![⌜(#i : SyntacticSemiterm ℒₛₑₜ n)⌝,⌜(#j : SyntacticSemiterm ℒₛₑₜ n)⌝]).val)
      (matrix F r K.val B.[(j : V)] B.[(i : V)]) := by
  have he := encode_subst_pair K.isSemiformula
    (Bootstrapping.Semiterm.bvar (V := V) i).isSemiterm
    (Bootstrapping.Semiterm.bvar (V := V) j).isSemiterm F B s
  change CodeIff (encode F B s (subst ℒₛₑₜ (^#(i : V)∷^#(j : V)∷0) K.val)) _
  simp only [Bootstrapping.Semiterm.bvar_val,
    ValidatorEnvironmentLabels254.TermLabels.term_bvar] at he
  rw [he]
  exact encode_stack_relabel K.isSemiformula F _ s r (by simp [one_add_one_eq_two])
    hs hr (stream_pair _ _ _ hsj hsi) (stream_pair _ _ _ hrj hri)

private lemma nth_two (a b c d : V) : (a∷b∷c∷d).[2]=c := by
  rw [←one_add_one_eq_two,nth_adjoin_succ,nth_adjoin_one,nth_adjoin_zero]
private lemma nth_three (a b c d e : V) : (a∷b∷c∷d∷e).[3]=d := by
  rw [show (3 : V)=2+1 by norm_num,nth_adjoin_succ,nth_two]
private lemma nth_four (a b c d e f : V) : (a∷b∷c∷d∷e∷f).[4]=e := by
  rw [show (4 : V)=3+1 by norm_num,nth_adjoin_succ,nth_three]
private lemma nth_five (a b c d e f g : V) : (a∷b∷c∷d∷e∷f∷g).[5]=f := by
  rw [show (5 : V)=4+1 by norm_num,nth_adjoin_succ,nth_four]
private def stack (s : V) : ℕ → V
  | 0 => 0
  | n+1 => role s n∷stack s n

/-- All five literal matrix copies retain the original free environment. -/
private lemma source_body_code (K : SF (V := V) 2) (F s : V) (hs : StreamFree s F) :
    CodeIff (encode F 0 s (fullSeedBody K).val)
      (wal s (ex (role s 1) (pairBody
        (typedFrame K.isSemiformula F (role s 7) (role_stream F s hs 7))
        (canonicalLayout K F s hs) (role s 1)))) := by
  have cp (n : ℕ) (i j : Fin n)
      (hi : (stack s n).[(i : V)]<role s n)
      (hj : (stack s n).[(j : V)]<role s n)
      (hi7 : (stack s n).[(i : V)]<role s 7)
      (hj7 : (stack s n).[(j : V)]<role s 7) :=
    enc_copy K F (stack s n) (role s n) (role s 7) i j
      (role_stream F s hs n) (role_stream F s hs 7) hi hj hi7 hj7
  have c4 := cp 4 1 0
    (by simpa [stack,nth_adjoin_one] using role_lt s (show 2<4 by decide))
    (by simpa [stack,nth_adjoin_zero] using role_lt s (show 3<4 by decide))
    (by simpa [stack,nth_adjoin_one] using role_lt s (show 2<7 by decide))
    (by simpa [stack,nth_adjoin_zero] using role_lt s (show 3<7 by decide))
  have c6 := cp 6 0 1
    (by simpa [stack,nth_adjoin_zero] using role_lt s (show 5<6 by decide))
    (by simpa [stack,nth_adjoin_one] using role_lt s (show 4<6 by decide))
    (by simpa [stack,nth_adjoin_zero] using role_lt s (show 5<7 by decide))
    (by simpa [stack,nth_adjoin_one] using role_lt s (show 4<7 by decide))
  have c7 := cp 7 0 2
    (by simpa [stack,nth_adjoin_zero] using role_lt s (show 6<7 by decide))
    (by simpa [stack,nth_two] using role_lt s (show 4<7 by decide))
    (by simpa [stack,nth_adjoin_zero] using role_lt s (show 6<7 by decide))
    (by simpa [stack,nth_two] using role_lt s (show 4<7 by decide))
  have c3 := cp 3 0 2
    (by simpa [stack,nth_adjoin_zero] using role_lt s (show 2<3 by decide))
    (by simpa [stack,nth_two] using role_lt s (show 0<3 by decide))
    (by simpa [stack,nth_adjoin_zero] using role_lt s (show 2<7 by decide))
    (by simpa [stack,nth_two] using role_lt s (show 0<7 by decide))
  have c4' := cp 4 0 3
    (by simpa [stack,nth_adjoin_zero] using role_lt s (show 3<4 by decide))
    (by simpa [stack,nth_three] using role_lt s (show 0<4 by decide))
    (by simpa [stack,nth_adjoin_zero] using role_lt s (show 3<7 by decide))
    (by simpa [stack,nth_three] using role_lt s (show 0<7 by decide))
  simp [stack,nth_three] at c4 c6 c7 c3 c4'
  dsimp only [pairBody,closure,request,subcode,canonicalLayout,typedFrame,role]
  unfold fullSeedBody seedPairMatrix
  apply enc_allIff
  apply enc_exIff
  apply enc_conjIff
  · apply enc_allIff
    apply enc_impIff
    · rw [enc_mem]; simpa [role] using codeIff_refl (wel (role s 2) (role s 1))
    · apply enc_exIff
      apply enc_conjIff
      · simpa [role] using c4
      · apply enc_allIff
        apply enc_impIff
        · rw [seedSubset_quote]
          apply enc_allIff
          apply enc_impIff
          · rw [enc_mem]; simpa [role] using codeIff_refl (wel (role s 5) (role s 4))
          · rw [enc_mem]; simpa [nth_three,role] using codeIff_refl (wel (role s 5) (role s 2))
        · apply enc_allIff
          apply enc_impIff
          · simpa [role] using c6
          · apply enc_exIff
            apply enc_conjIff
            · simpa [role] using c7
            · rw [enc_mem]; simpa [nth_five,role] using codeIff_refl (wel (role s 6) (role s 1))
  · apply enc_allIff
    apply enc_impIff
    · simpa [role] using c3
    · apply enc_exIff
      apply enc_conjIff
      · simpa [role] using c4'
      · rw [enc_mem]; simpa [nth_two,role] using codeIff_refl (wel (role s 3) (role s 1))

/-- The numerical seed is padded only after encoding the original matrix.
All source-role labels and both complete environments are below its bound. -/
private lemma fullSeed_image_odd (K : SF (V := V) 2) (F s : V)
    (hs : StreamFree s F) (hodd : s%2=1) :
    CProv (encode F 0 s (fullSeedBody K).val) := by
  let r := role s 7
  let A := typedFrame K.isSemiformula F r (role_stream F s hs 7)
  let L := canonicalLayout K F s hs
  let B := role s 2∷role s 0∷(0 : V)
  let P := matrix F r K.val (role s 0) (role s 2)
  let bound := F+B+r
  let c := seedLabel bound P
  have hrole (i : Fin 7) : L.label i≤bound :=
    le_trans (le_of_lt (role_lt s i.isLt)) (le_add_of_nonneg_left (Arithmetic.zero_le (F+B)))
  have hc (i : Fin 7) : c≠L.label i :=
    ne_of_gt (lt_of_le_of_lt (hrole i) (bound_lt_seedLabel bound P))
  have hrOdd : r%2=1 := by simp [r,role_eq,hodd]
  have hF : F≤bound := le_trans (le_add_of_nonneg_right (Arithmetic.zero_le B))
    (le_add_of_nonneg_right (Arithmetic.zero_le r))
  have fc : A.fresh c := ⟨seedLabel_free bound P F hF,seedLabel_stream bound P r hrOdd⟩
  have seed := bounded_seed_pair bound P (L.label 0) (L.label 2) (hrole 0) (hrole 2)
  have hx : CProv (ex (L.label 1) (pairBody A L (L.label 1))) :=
    cProv_mp (seed_binder A L c hc fc).1 seed
  exact cProv_mp (source_body_code K F s hs).2 (cProv_gen s hx)

/-- Actual C222 image for every internally typed two-slot matrix. The
requested free-safe stream may be even, odd, or overlap the auxiliary one.
No source axiom image or source interpretation is supplied as a premise. -/
theorem fullSeed_image (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) (F s : V)
    (hs : StreamFree s F) : CProv (encode F 0 s (fullSeedBody K).val) := by
  let u := alternateStart F 0
  have hu : StreamFree u F := alternateStart_free F 0 F (le_refl F)
  have ho : u%2=1 := by simp [u,alternateStart]
  exact cProv_mp
    (encode_formula_relabel (fullSeedBody K).isSemiformula F u s hu hs).1
    (fullSeed_image_odd K F u hu ho)

/-- Raw internal code interface. The typing hypothesis ranges over every
matrix code in the arithmetic model, not only standard quoted matrices. -/
theorem typed_fullSeed_image {p : V} (hp : IsSemiformula ℒₛₑₜ 2 p)
    (F s : V) (hs : StreamFree s F) :
    CProv (encode F 0 s (fullSeedBodyVal p)) := by
  rw [fullSeedBodyVal_eq (⟨p,hp⟩ : Bootstrapping.Semiformula V ℒₛₑₜ 2)]
  exact fullSeed_image ⟨p,hp⟩ F s hs

theorem typed_fullSeed_witness {p : V} (hp : IsSemiformula ℒₛₑₜ 2 p)
    (F s : V) (hs : StreamFree s F) :
    ∃ d : V, ArithmeticHistory222.value d=encode F 0 s (fullSeedBodyVal p)+1 :=
  typed_fullSeed_image hp F s hs

/-- The same endpoint for the literal meta-level source construction;
its original free parameters are interpreted by the unchanged F. -/
theorem quoted_fullSeed_image (K : SetTheorySemiproposition 2) (F s : V)
    (hs : StreamFree s F) :
    CProv (encode F 0 s (⌜fullSeedBodyMeta K⌝ : V)) := by
  rw [FirstOrder.Semiformula.quote_def,fullSeedBody_quote]
  exact fullSeed_image ⌜K⌝ F s hs

end TypedImage
end LeanProofs.ZFCinPA.ValidatorSourceFullSeed222
