import ZFCinPA.ValidatorRelationalCore222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Fixed indiscernibility deductions for the actual internal C222 checker.
This is the arithmetic-value counterpart of the finite KEind222 argument,
without importing that external Nat derivability or model-completeness proof.
Only membership vacuity and the exact primitive-equality helper binder are
used. No arbitrary-binder primitive equality vacuity is assumed. -/
namespace LeanProofs.ZFCinPA.ValidatorEind222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222
open ValidatorEqualityCore222 (cProv_refl cProv_rho7 cProv_helper)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def biff (p q : V) : V := conj (wim p q) (wim q p)
def Bin (v a b : V) : V := biff (wel v a) (wel v b)
def Bout (v a b : V) : V := biff (wel a v) (wel b v)
def Ev (v a b : V) : V := conj (wal v (Bin v a b)) (wal v (Bout v a b))
def aux (a b : V) : V := a + b + 1
def Eind (a b : V) : V := Ev (aux a b) a b
def fresh3 (a b c : V) : V := a + b + c + 1

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
private lemma h0 {G : List V} {a : V} : D (a :: G) a := .cons_head
private lemma h1 {G : List V} {a b : V} : D (b :: a :: G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
private lemma ofDer {p : V} (d : D [] p) : CProv p :=
  d.sound cProv_classical (fun _ h => absurd h List.not_mem_nil)
private lemma ded1 {a p : V} (d : D [a] p) : CProv (wim a p) :=
  ofDer (Kalmar.deduction cProv_classical d)
private lemma ded2 {a b p : V} (d : D [b, a] p) : CProv (wim a (wim b p)) :=
  ofDer (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical d))
private lemma self_imp (p : V) : CProv (wim p p) := ded1 h0

theorem eq_symm (a b : V) : CProv (wim (weq a b) (weq b a)) :=
  ded1 (.mp (.mp (.ax (cProv_rho7 b a a)) h0) (.ax (cProv_refl a)))

theorem eq_mem_right (a b c : V) :
    CProv (wim (weq a b) (wim (wel c a) (wel c b))) := by
  change CProv (ArithmeticTemplates254.rho3 a b c)
  exact cProv_rho3 a b c

theorem eq_mem_left (a b c : V) :
    CProv (wim (weq a b) (wim (wel a c) (wel b c))) := by
  change CProv (ArithmeticTemplates254.rho5 b c a)
  exact cProv_rho5 b c a

private lemma biff_transport (h p p' q q' : V)
    (hp : CProv (wim h (wim p p'))) (hp' : CProv (wim h (wim p' p)))
    (hq : CProv (wim h (wim q q'))) (hq' : CProv (wim h (wim q' q))) :
    CProv (wim h (wim (biff p q) (biff p' q'))) := by
  apply ded2
  have pp : D [biff p q, h] (wim p' p) := .mp (.ax hp') h1
  have pq : D [biff p q, h] (wim p q) := .mp (.ax (conj_left _ _)) h0
  have qq : D [biff p q, h] (wim q q') := .mp (.ax hq) h1
  have qp : D [biff p q, h] (wim q p) := .mp (.ax (conj_right _ _)) h0
  have qr : D [biff p q, h] (wim q' q) := .mp (.ax hq') h1
  have pr : D [biff p q, h] (wim p p') := .mp (.ax hp) h1
  have f : D [biff p q, h] (wim p' q') :=
    Kalmar.deduction cProv_classical (.mp qq.weaken (.mp pq.weaken (.mp pp.weaken h0)))
  have g : D [biff p q, h] (wim q' p') :=
    Kalmar.deduction cProv_classical (.mp pr.weaken (.mp qp.weaken (.mp qr.weaken h0)))
  exact .mp (.mp (.ax (conj_rule _ _)) f) g

theorem bin_congr (v w a b : V) :
    CProv (wim (weq v w) (wim (Bin v a b) (Bin w a b))) :=
  biff_transport _ _ _ _ _ (eq_mem_left v w a)
    (compose (eq_symm v w) (eq_mem_left w v a)) (eq_mem_left v w b)
    (compose (eq_symm v w) (eq_mem_left w v b))

theorem bout_congr (v w a b : V) :
    CProv (wim (weq v w) (wim (Bout v a b) (Bout w a b))) :=
  biff_transport _ _ _ _ _ (eq_mem_right v w a)
    (compose (eq_symm v w) (eq_mem_right w v a)) (eq_mem_right v w b)
    (compose (eq_symm v w) (eq_mem_right w v b))

theorem vac_bin (i v a b : V) (hv : i ≠ v) (ha : i ≠ a) (hb : i ≠ b) :
    Vac i (Bin v a b) :=
  vac_conj (vac_imp (vac_rel v a i hv ha) (vac_rel v b i hv hb))
    (vac_imp (vac_rel v b i hv hb) (vac_rel v a i hv ha))

theorem vac_bout (i v a b : V) (hv : i ≠ v) (ha : i ≠ a) (hb : i ≠ b) :
    Vac i (Bout v a b) :=
  vac_conj (vac_imp (vac_rel a v i ha hv) (vac_rel b v i hb hv))
    (vac_imp (vac_rel b v i hb hv) (vac_rel a v i ha hv))

theorem vac_ev (i v a b : V) (hv : i ≠ v) (ha : i ≠ a) (hb : i ≠ b) :
    Vac i (Ev v a b) :=
  vac_conj (vac_all v (vac_bin i v a b hv ha hb))
    (vac_all v (vac_bout i v a b hv ha hb))

private lemma fixed_alpha (v w p q : V)
    (h : CProv (wim (weq v w) (wim p q))) (hvq : Vac v q) (hwp : Vac w p) :
    CProv (wim (wal v p) (wal w q)) := by
  have h0' : CProv (wim (0 : V) (wim (weq v w) (wim p q))) :=
    cProv_mp (cProv_k _ 0) h
  exact cProv_mp (all_relational 0 p q v w h0' (vac_truth v) hvq
    (vac_truth w) (vac_all v hwp)) cProv_truth

theorem all_bin_alpha (v w a b : V) (hva : v ≠ a) (hvb : v ≠ b)
    (hwa : w ≠ a) (hwb : w ≠ b) :
    CProv (wim (wal v (Bin v a b)) (wal w (Bin w a b))) := by
  by_cases hwv : w = v
  · subst w; exact self_imp _
  · exact fixed_alpha v w _ _ (bin_congr v w a b)
      (vac_bin v w a b (Ne.symm hwv) hva hvb) (vac_bin w v a b hwv hwa hwb)

theorem all_bout_alpha (v w a b : V) (hva : v ≠ a) (hvb : v ≠ b)
    (hwa : w ≠ a) (hwb : w ≠ b) :
    CProv (wim (wal v (Bout v a b)) (wal w (Bout w a b))) := by
  by_cases hwv : w = v
  · subst w; exact self_imp _
  · exact fixed_alpha v w _ _ (bout_congr v w a b)
      (vac_bout v w a b (Ne.symm hwv) hva hvb) (vac_bout w v a b hwv hwa hwb)

theorem ev_alpha (v w a b : V) (hva : v ≠ a) (hvb : v ≠ b)
    (hwa : w ≠ a) (hwb : w ≠ b) : CProv (wim (Ev v a b) (Ev w a b)) := by
  apply ded1
  have hi : D [Ev v a b] (wal w (Bin w a b)) :=
    .mp (.ax (all_bin_alpha v w a b hva hvb hwa hwb)) (.mp (.ax (conj_left _ _)) h0)
  have ho : D [Ev v a b] (wal w (Bout w a b)) :=
    .mp (.ax (all_bout_alpha v w a b hva hvb hwa hwb)) (.mp (.ax (conj_right _ _)) h0)
  exact .mp (.mp (.ax (conj_rule _ _)) hi) ho

theorem aux_ne (a b : V) : aux a b ≠ a ∧ aux a b ≠ b := by
  constructor
  · exact ne_of_gt (lt_of_le_of_lt (show a ≤ a + b by simp) (lt_add_one _))
  · exact ne_of_gt (lt_of_le_of_lt (show b ≤ a + b by simp) (lt_add_one _))

theorem fresh3_ne (a b c : V) : fresh3 a b c ≠ a ∧ fresh3 a b c ≠ b ∧ fresh3 a b c ≠ c := by
  have ha : a ≤ a + b + c := by simp
  have hb : b ≤ a + b + c := le_trans (by simp : b ≤ a + b) (by simp)
  have hc : c ≤ a + b + c := by simp
  exact ⟨ne_of_gt (lt_of_le_of_lt ha (lt_add_one _)),
    ne_of_gt (lt_of_le_of_lt hb (lt_add_one _)),
    ne_of_gt (lt_of_le_of_lt hc (lt_add_one _))⟩

theorem eind_to (w a b : V) (ha : w ≠ a) (hb : w ≠ b) :
    CProv (wim (Eind a b) (Ev w a b)) :=
  ev_alpha _ _ _ _ (aux_ne a b).1 (aux_ne a b).2 ha hb

theorem eind_of (w a b : V) (ha : w ≠ a) (hb : w ≠ b) :
    CProv (wim (Ev w a b) (Eind a b)) :=
  ev_alpha _ _ _ _ ha hb (aux_ne a b).1 (aux_ne a b).2

private lemma fixed_spec (v c p q : V)
    (h : CProv (wim (weq v c) (wim p q))) (hvq : Vac v q) :
    CProv (wim (wal v p) q) := by
  have hs : CProv (wim p (wim (weq v c) q)) :=
    ded2 (.mp (.mp (.ax h) h0) h1)
  apply ded1
  have hi : D [wal v p] (wal v (wim (weq v c) q)) := .mp (.ax (all_mono v hs)) h0
  have he : D [wal v p] (ex v q) :=
    .mp (.mp (.ax (all_imp_ex v (weq v c) q)) hi) (.ax (ex_equality v c))
  exact .mp (.ax (ex_elim_of_vac hvq)) he

theorem bin_spec (v a b c : V) (hvc : v ≠ c) (hva : v ≠ a) (hvb : v ≠ b) :
    CProv (wim (wal v (Bin v a b)) (Bin c a b)) :=
  fixed_spec v c _ _ (bin_congr v c a b) (vac_bin v c a b hvc hva hvb)

theorem bout_spec (v a b c : V) (hvc : v ≠ c) (hva : v ≠ a) (hvb : v ≠ b) :
    CProv (wim (wal v (Bout v a b)) (Bout c a b)) :=
  fixed_spec v c _ _ (bout_congr v c a b) (vac_bout v c a b hvc hva hvb)

theorem Eind_el_r (a b c : V) : CProv (wim (Eind a b) (wim (wel c a) (wel c b))) := by
  obtain ⟨ha, hb, hc⟩ := fresh3_ne a b c
  exact compose (compose (compose (eind_to _ a b ha hb) (conj_left _ _))
    (bin_spec _ a b c hc ha hb)) (conj_left _ _)

theorem Eind_el_l (a b c : V) : CProv (wim (Eind c a) (wim (wel c b) (wel a b))) := by
  obtain ⟨hc, ha, hb⟩ := fresh3_ne c a b
  exact compose (compose (compose (eind_to _ c a hc ha) (conj_right _ _))
    (bout_spec _ c a b hb hc ha)) (conj_left _ _)

theorem biff_euclid (p q r : V) :
    CProv (wim (biff p q) (wim (biff p r) (biff q r))) := by
  apply ded2
  have pq : D [biff p r, biff p q] (wim p q) := .mp (.ax (conj_left _ _)) h1
  have qp : D [biff p r, biff p q] (wim q p) := .mp (.ax (conj_right _ _)) h1
  have pr : D [biff p r, biff p q] (wim p r) := .mp (.ax (conj_left _ _)) h0
  have rp : D [biff p r, biff p q] (wim r p) := .mp (.ax (conj_right _ _)) h0
  have qr : D [biff p r, biff p q] (wim q r) :=
    Kalmar.deduction cProv_classical (.mp pr.weaken (.mp qp.weaken h0))
  have rq : D [biff p r, biff p q] (wim r q) :=
    Kalmar.deduction cProv_classical (.mp pq.weaken (.mp rp.weaken h0))
  exact .mp (.mp (.ax (conj_rule _ _)) qr) rq

theorem all_mono2 (i : V) {a b c : V} (h : CProv (wim a (wim b c))) :
    CProv (wim (wal i a) (wim (wal i b) (wal i c))) :=
  compose (all_mono i h) (all_distribution i b c)

theorem ev_euclid (v a b c : V) :
    CProv (wim (Ev v a b) (wim (Ev v a c) (Ev v b c))) := by
  have hi := all_mono2 v (biff_euclid (wel v a) (wel v b) (wel v c))
  have ho := all_mono2 v (biff_euclid (wel a v) (wel b v) (wel c v))
  apply ded2
  have di : D [Ev v a c, Ev v a b] (wal v (Bin v b c)) :=
    .mp (.mp (.ax hi) (.mp (.ax (conj_left _ _)) h1)) (.mp (.ax (conj_left _ _)) h0)
  have do' : D [Ev v a c, Ev v a b] (wal v (Bout v b c)) :=
    .mp (.mp (.ax ho) (.mp (.ax (conj_right _ _)) h1)) (.mp (.ax (conj_right _ _)) h0)
  exact .mp (.mp (.ax (conj_rule _ _)) di) do'

theorem Eind_euclid (a b c : V) :
    CProv (wim (Eind c a) (wim (Eind c b) (Eind a b))) := by
  obtain ⟨ha, hb, hc⟩ := fresh3_ne a b c
  apply ded2
  have d1 : D [Eind c b, Eind c a] (Ev (fresh3 a b c) c a) :=
    .mp (.ax (eind_to _ c a hc ha)) h1
  have d2 : D [Eind c b, Eind c a] (Ev (fresh3 a b c) c b) :=
    .mp (.ax (eind_to _ c b hc hb)) h0
  exact .mp (.ax (eind_of _ a b ha hb)) (.mp (.mp (.ax (ev_euclid _ c a b)) d1) d2)

private lemma wel_fresh (a b : V) : wel a b ≠ a ∧ wel a b ≠ b := by
  have ha : a ≤ 4 * ArithmeticCantor.cantor a b := by
    simpa only [tagged, add_zero] using (tagged_components (0 : V) a b).1
  have hb : b ≤ 4 * ArithmeticCantor.cantor a b := by
    simpa only [tagged, add_zero] using (tagged_components (0 : V) a b).2
  exact ⟨ne_of_gt (lt_of_le_of_lt ha (lt_add_one _)),
    ne_of_gt (lt_of_le_of_lt hb (lt_add_one _))⟩

/-- Primitive equality implies indiscernibility, using only its actual
helper binder wel(a,b), followed by fixed relational alpha conversion. -/
theorem Eq_Eind (a b : V) : CProv (wim (weq a b) (Eind a b)) := by
  let w := wel a b
  have hi : CProv (wim (weq a b) (Bin w a b)) := by
    apply ded1
    exact .mp (.mp (.ax (conj_rule _ _)) (.mp (.ax (eq_mem_right a b w)) h0))
      (.mp (.ax (eq_mem_right b a w)) (.mp (.ax (eq_symm a b)) h0))
  have ho : CProv (wim (weq a b) (Bout w a b)) := by
    apply ded1
    exact .mp (.mp (.ax (conj_rule _ _)) (.mp (.ax (eq_mem_left a b w)) h0))
      (.mp (.ax (eq_mem_left b a w)) (.mp (.ax (eq_symm a b)) h0))
  apply ded1
  have hall : D [weq a b] (wal w (weq a b)) := .mp (.ax (cProv_helper a b)) h0
  have di : D [weq a b] (wal w (Bin w a b)) := .mp (.ax (all_mono w hi)) hall
  have do' : D [weq a b] (wal w (Bout w a b)) := .mp (.ax (all_mono w ho)) hall
  exact .mp (.ax (eind_of w a b (wel_fresh a b).1 (wel_fresh a b).2))
    (.mp (.mp (.ax (conj_rule _ _)) di) do')

theorem Eind_ex (a b : V) : CProv (ex a (Eind a b)) :=
  cProv_mp (ex_mono a (Eq_Eind a b)) (ex_equality a b)

/-- Both legal cases are covered, including c=0 and a=b. If c is the
fixed auxiliary binder, first rename it to a+b+c+1, then return under ∀c. -/
theorem Eind_vac (a b c : V) (ha : c ≠ a) (hb : c ≠ b) : Vac c (Eind a b) := by
  by_cases hc : c = aux a b
  · obtain ⟨hwa, hwb, hwc⟩ := fresh3_ne a b c
    exact compose (compose (eind_to _ a b hwa hwb)
      (vac_ev c _ a b (Ne.symm hwc) ha hb))
      (all_mono c (eind_of _ a b hwa hwb))
  · exact vac_ev c _ a b hc ha hb

end LeanProofs.ZFCinPA.ValidatorEind222
