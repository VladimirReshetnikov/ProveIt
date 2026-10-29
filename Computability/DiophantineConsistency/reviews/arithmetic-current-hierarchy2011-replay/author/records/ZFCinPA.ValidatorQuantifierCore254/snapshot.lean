import ZFCinPA.ValidatorProvability254

set_option autoImplicit false
noncomputable section

/-!
Finite derived quantifier and vacuity arguments for the literal validator.
All formula/label arguments are arbitrary internal arithmetic values. Each
proof uses the checked CProv row closures and the polymorphic finite Kalmar
deduction theorem; there is no induction over ordinary formula syntax.

The final two-binder bridge exposes the four vacuity proof witnesses that
an eventual represented environment/alpha induction must supply. It does
not rename arbitrary accepted proofs or theory bundles.
-/
namespace LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254
open ValidatorProvability254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev neg (p : V) : V := wim p 1
abbrev conj (p q : V) : V := neg (wim p (neg q))
abbrev ex (i p : V) : V := neg (wal i (neg p))
def Vac (i p : V) : Prop := CProv (wim p (wal i p))

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
private lemma h0 {G : List V} {a : V} : D (a::G) a := .cons_head
private lemma h1 {G : List V} {a b : V} : D (b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
private lemma h2 {G : List V} {a b c : V} : D (c::b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
private lemma ofDer {p : V} (d : D [] p) : CProv p :=
  d.sound cProv_classical (fun _ hm => absurd hm List.not_mem_nil)
private lemma ded1 {a p : V} (d : D [a] p) : CProv (wim a p) :=
  ofDer (Kalmar.deduction cProv_classical d)
private lemma ded2 {a b p : V} (d : D [b,a] p) : CProv (wim a (wim b p)) :=
  ofDer (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical d))
private lemma ded3 {a b c p : V} (d : D [c,b,a] p) :
    CProv (wim a (wim b (wim c p))) :=
  ofDer (Kalmar.deduction cProv_classical
    (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical d)))

lemma compose {a b c : V} (hab : CProv (wim a b)) (hbc : CProv (wim b c)) :
    CProv (wim a c) := ded1 (.mp (.ax hbc) (.mp (.ax hab) h0))

lemma contrapose (a b : V) :
    CProv (wim (wim a b) (wim (neg b) (neg a))) :=
  ded3 (.mp h1 (.mp h2 h0))
lemma contrapose_of {a b : V} (h : CProv (wim a b)) :
    CProv (wim (neg b) (neg a)) := cProv_mp (contrapose a b) h
lemma double_neg_elim (a : V) : CProv (wim (neg (neg a)) a) := by
  apply ded1
  have inner : D [neg (neg a)] (wim (neg a) a) :=
    Kalmar.deduction cProv_classical (.mp (.ax (cProv_ex_falso a)) (.mp h1 h0))
  exact .mp (.ax (cProv_peirce a 1)) inner
lemma double_neg_intro (a : V) : CProv (wim a (neg (neg a))) :=
  ded2 (.mp h0 h1)

lemma all_distribution (i p q : V) :
    CProv (wim (wal i (wim p q)) (wim (wal i p) (wal i q))) := by
  change CProv (ArithmeticTemplates254.rho2 i p q)
  exact cProv_rho2 i p q
lemma all_swap (i j p : V) :
    CProv (wim (wal i (wal j p)) (wal j (wal i p))) := by
  change CProv (ArithmeticTemplates254.rho4 i j p)
  exact cProv_rho4 i j p
lemma ex_all_elim (i p : V) : CProv (wim (ex i (wal i p)) p) := by
  change CProv (ArithmeticTemplates254.rho6 i p)
  exact cProv_rho6 i p
lemma ex_equality (i j : V) : CProv (ex i (weq i j)) := cProv_rho1 i j

lemma all_mono (i : V) {p q : V} (h : CProv (wim p q)) :
    CProv (wim (wal i p) (wal i q)) :=
  cProv_mp (all_distribution i p q) (cProv_gen i h)
lemma ex_mono (i : V) {p q : V} (h : CProv (wim p q)) :
    CProv (wim (ex i p) (ex i q)) :=
  contrapose_of (all_mono i (contrapose_of h))
lemma ex_elim_of_vac {i p : V} (h : Vac i p) : CProv (wim (ex i p) p) :=
  compose (ex_mono i h) (ex_all_elim i p)
lemma vac_neg {i p : V} (h : Vac i p) : Vac i (neg p) :=
  compose (contrapose_of (ex_elim_of_vac h)) (double_neg_elim (wal i (neg p)))

lemma conj_left (a b : V) : CProv (wim (conj a b) a) := by
  apply ded1
  have hnna : D [conj a b] (neg (neg a)) := by
    apply Kalmar.deduction cProv_classical
    have hm : D [neg a,conj a b] (wim a (neg b)) := by
      apply Kalmar.deduction cProv_classical
      exact .mp (.ax (cProv_ex_falso (neg b))) (.mp h1 h0)
    exact .mp h1 hm
  exact .mp (.ax (double_neg_elim a)) hnna
lemma conj_right (a b : V) : CProv (wim (conj a b) b) := by
  apply ded1
  have hnnb : D [conj a b] (neg (neg b)) := by
    apply Kalmar.deduction cProv_classical
    have hm : D [neg b,conj a b] (wim a (neg b)) :=
      .mp (.ax (cProv_k (neg b) a)) h0
    exact .mp h1 hm
  exact .mp (.ax (double_neg_elim b)) hnnb
lemma conj_intro {a b : V} (ha : CProv a) (hb : CProv b) : CProv (conj a b) :=
  ded1 (.mp (.mp h0 (.ax ha)) (.ax hb))

/-- The two gated atomic projections share the same bundle certificate. -/
private lemma vac_atoms (a b i : V) (ha : i≠a) (hb : i≠b) :
    Vac i (wel a b) ∧ Vac i (weq a b) := by
  let m : V := wim (wel a b) (wal i (wel a b))
  let e : V := wim (weq a b) (wal i (weq a b))
  have hall : CProv (conj
      (conj (ArithmeticTemplates254.bundleC a b i) (ArithmeticTemplates254.bundleG a b i))
      (conj m e)) := by
    change CProv (ArithmeticTemplates254.bundle a b i)
    exact cProv_bundle a b i ha hb
  have hv := cProv_mp (conj_right _ _) hall
  exact ⟨cProv_mp (conj_left m e) hv, cProv_mp (conj_right m e) hv⟩

lemma vac_rel (a b i : V) (ha : i≠a) (hb : i≠b) : Vac i (wel a b) :=
  (vac_atoms a b i ha hb).1
lemma vac_eq (a b i : V) (ha : i≠a) (hb : i≠b) : Vac i (weq a b) :=
  (vac_atoms a b i ha hb).2

lemma vac_truth (i : V) : Vac i (0 : V) :=
  cProv_mp (cProv_k (wal i 0) 0) (cProv_gen i cProv_truth)
lemma vac_falsum (i : V) : Vac i (1 : V) := cProv_ex_falso (wal i 1)

private lemma imp_cases (a b c : V) :
    CProv (wim (wim (neg a) c) (wim (wim b c) (wim (wim a b) c))) := by
  apply ded3
  have inner : D [neg c,wim a b,wim b c,wim (neg a) c] c := by
    have na : D [neg c,wim a b,wim b c,wim (neg a) c] (neg a) :=
      Kalmar.deduction cProv_classical
        (.mp (.hyp (a := neg c) (by simp))
          (.mp (.hyp (a := wim b c) (by simp))
            (.mp (.hyp (a := wim a b) (by simp)) h0)))
    exact .mp (.hyp (a := wim (neg a) c) (by simp)) na
  exact .mp (.ax (cProv_peirce c 1)) (Kalmar.deduction cProv_classical inner)

lemma vac_imp {i a b : V} (ha : Vac i a) (hb : Vac i b) : Vac i (wim a b) := by
  have hna : CProv (wim (neg a) (wal i (wim a b))) :=
    compose (vac_neg ha)
      (all_mono i (ded2 (.mp (.ax (cProv_ex_falso b)) (.mp h1 h0))))
  have hbb : CProv (wim b (wal i (wim a b))) :=
    compose hb (all_mono i (cProv_k b a))
  exact cProv_mp (cProv_mp (imp_cases a b (wal i (wim a b))) hna) hbb
lemma vac_all (j : V) {i p : V} (hp : Vac i p) : Vac i (wal j p) :=
  compose (all_mono j hp) (all_swap j i p)

lemma all_imp_ex (i p q : V) :
    CProv (wim (wal i (wim p q)) (wim (ex i p) (ex i q))) := by
  have h1' : CProv (wim (wal i (wim p q)) (wal i (wim (neg q) (neg p)))) :=
    all_mono i (contrapose p q)
  have h3 := compose h1' (all_distribution i (neg q) (neg p))
  apply ded2
  apply Kalmar.deduction cProv_classical
  exact .mp h1 (.mp (.mp (.ax h3) h2) h0)

/-- Generalize a theorem under two assumptions whose vacuity is supplied. -/
lemma all_under_two (i : V) {h p q : V}
    (hpq : CProv (wim h (wim p q))) (hh : Vac i h) (hp : Vac i p) :
    CProv (wim h (wim p (wal i q))) := by
  have hg := compose hh (all_mono i hpq)
  apply ded2
  exact .mp (.mp (.ax (all_distribution i p q)) (.mp (.ax hg) h1))
    (.mp (.ax hp) h0)

/-- A finite two-binder congruence step with every freshness resource explicit.
No global proof renaming or ordinary syntax induction is used. -/
lemma all_relational (h p q x y : V)
    (hpq : CProv (wim h (wim (weq x y) (wim p q))))
    (vxh : Vac x h) (vxq : Vac x q)
    (vyh : Vac y h) (vyall : Vac y (wal x p)) :
    CProv (wim h (wim (wal x p) (wal y q))) := by
  have hs : CProv (wim h (wim p (wim (weq x y) q))) :=
    ded3 (.mp (.mp (.mp (.ax hpq) h2) h0) h1)
  have hx := compose vxh (all_mono x hs)
  have hi : CProv (wim h (wim (wal x p) (wal x (wim (weq x y) q)))) := by
    apply ded2
    exact .mp (.mp (.ax (all_distribution x p (wim (weq x y) q)))
      (.mp (.ax hx) h1)) h0
  have he : CProv (wim (wal x (wim (weq x y) q)) (ex x q)) :=
    ded1 (.mp (.mp (.ax (all_imp_ex x (weq x y) q)) h0) (.ax (ex_equality x y)))
  have hq : CProv (wim h (wim (wal x p) q)) := by
    apply ded2
    exact .mp (.ax (ex_elim_of_vac vxq))
      (.mp (.ax he) (.mp (.mp (.ax hi) h1) h0))
  exact all_under_two y hq vyh vyall

end LeanProofs.ZFCinPA.ValidatorQuantifierCore254
