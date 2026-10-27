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

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
private lemma h0 {G : List V} {a : V} : D (a::G) a := .cons_head
private lemma h1 {G : List V} {a b : V} : D (b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
private lemma h2 {G : List V} {a b c : V} : D (c::b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
private lemma ofDer {p : V} (h : D [] p) : CProv p :=
  h.sound cProv_classical (fun _ hm => absurd hm List.not_mem_nil)
private lemma ded1 {a p : V} (h : D [a] p) : CProv (wim a p) :=
  ofDer (Kalmar.deduction cProv_classical h)
private lemma ded2 {a b p : V} (h : D [b,a] p) : CProv (wim a (wim b p)) :=
  ofDer (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical h))
private lemma ded3 {a b c p : V} (h : D [c,b,a] p) :
    CProv (wim a (wim b (wim c p))) :=
  ofDer (Kalmar.deduction cProv_classical
    (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical h)))
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
  ⟨ded2 (.mp (.mp (.ax hqr.1) h1) (.mp (.mp (.ax hpq.1) h1) h0)),
   ded2 (.mp (.mp (.ax hpq.2) h1) (.mp (.mp (.ax hqr.2) h1) h0))⟩
private lemma under_pre {h h' p q : V} (hh : CProv (wim h h')) (hpq : EqUnder h' p q) :
    EqUnder h p q := ⟨compose hh hpq.1,compose hh hpq.2⟩
private lemma under_all (x : V) {h p q : V} (hv : Vac x h) (hpq : EqUnder h p q) :
    EqUnder h (wal x p) (wal x q) := by
  constructor
  · exact ded2 (.mp (.mp (.ax (all_distribution x p q))
      (.mp (.ax (compose hv (all_mono x hpq.1))) h1)) h0)
  · exact ded2 (.mp (.mp (.ax (all_distribution x q p))
      (.mp (.ax (compose hv (all_mono x hpq.2))) h1)) h0)
private lemma under_ex (x : V) {h p q : V} (hv : Vac x h) (hpq : EqUnder h p q) :
    EqUnder h (ex x p) (ex x q) := eqUnder_neg (under_all x hv (eqUnder_neg hpq))
private lemma under_member {h x x' y y' : V}
    (hx : CProv (wim h (Eind x x'))) (hy : CProv (wim h (Eind y y'))) :
    EqUnder h (wel x y) (wel x' y') := by
  constructor
  · exact ded2 (.mp (.mp (.mp (.ax (rel_congr x x' y y'))
      (.mp (.ax hx) h1)) (.mp (.ax hy) h1)) h0)
  · exact ded2 (.mp (.mp (.mp (.ax (rel_congr x' x y' y))
      (.mp (.ax (compose hx (eind_symm x x'))) h1))
      (.mp (.ax (compose hy (eind_symm y y'))) h1)) h0)

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
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] in
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

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] in
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

/-- K's slot0 is output; slot1 is input. Original free parameters survive. -/
def fullSeedBodyMeta (K : SetTheorySemiproposition 2) : SetTheoryProposition :=
  ∀⁰ ∃⁰ ((∀⁰ (seedMem 3 0 1 🡒 ∃⁰
      ((K ⇜ ![(#1 : SyntacticSemiterm ℒₛₑₜ 4),#0]) ⋏
        (∀⁰ (seedSubset 🡒 ∀⁰
          ((K ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 6),#1]) 🡒
            ∃⁰ ((K ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 7),#2]) ⋏ seedMem 7 0 5))))))) ⋏
    (∀⁰ ((K ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 3),#2]) 🡒
      ∃⁰ ((K ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 4),#3]) ⋏ seedMem 4 0 2))))

def fullSeedBody (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Bootstrapping.Semiformula V ℒₛₑₜ 0 :=
  ∀⁰ ∃⁰ ((∀⁰ ((⌜seedMem 3 0 1⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3) 🡒 ∃⁰
      ((K.subst ![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝,⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝]) ⋏
        (∀⁰ ((⌜seedSubset⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 5) 🡒 ∀⁰
          ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 6)⌝,⌜(#1 : SyntacticSemiterm ℒₛₑₜ 6)⌝]) 🡒
            ∃⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 7)⌝,⌜(#2 : SyntacticSemiterm ℒₛₑₜ 7)⌝]) ⋏
              (⌜seedMem 7 0 5⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 7)))))))) ⋏
    (∀⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝,⌜(#2 : SyntacticSemiterm ℒₛₑₜ 3)⌝]) 🡒
      ∃⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝,⌜(#3 : SyntacticSemiterm ℒₛₑₜ 4)⌝]) ⋏
        (⌜seedMem 4 0 2⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 4)))))

theorem fullSeedBody_quote (K : SetTheorySemiproposition 2) :
    (⌜fullSeedBodyMeta K⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 0) = fullSeedBody ⌜K⌝ := by
  unfold fullSeedBodyMeta fullSeedBody
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
  simp [fullSeedBodyVal,fullSeedBody]

end LeanProofs.ZFCinPA.ValidatorSourceFullSeed222
