import BusyBeaver.ZFC.ConstructibleReflect

/-!
The constructible class satisfies ZF.

Separation in `L` reflects the formula into a closed stage `L_β`
(`ConstructibleReflect.reflect`), where the separated set is definable, hence
constructible. Replacement collects the images by Replacement in the model,
bounds them in one stage and separates. Together with the easy axioms of
`Constructible`, the substructure on `L` is a model of `SetTheory.ZFax_s`.
-/

namespace SetTheory.BusyBeaver.ZFC.ConstructibleZF

open NamedZF NForm InternalOrd InternalRank TransRec ConstructibleDef Constructible
  ConstructibleReflect LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

section Sep

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP

/-- Finitely many constructible sets lie in one stage. -/
theorem inL_common (v : Nat → V) :
    ∀ m, (∀ k, k < m + 1 → InL H hP (v k)) →
      ∃ γ T, Ord mem γ ∧ IsL H hP γ T ∧ ∀ k, k < m + 1 → mem (v k) T := by
  intro m
  induction m with
  | zero =>
      intro hv
      obtain ⟨γ, T, hγ, hT, hx⟩ := hv 0 (by omega)
      exact ⟨γ, T, hγ, hT, fun k hk => by rwa [show k = 0 by omega]⟩
  | succ m ih =>
      intro hv
      obtain ⟨γ1, T1, ho1, hT1, h1⟩ := ih fun k hk => hv k (by omega)
      obtain ⟨γ2, T2, ho2, hT2, h2⟩ := hv (m + 1) (by omega)
      rcases trichotomy H hR γ1 ho1 γ2 ho2 with h | rfl | h
      · exact ⟨γ2, T2, ho2, hT2, fun k hk => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact isL_mono H hR hP ho2 h hT1 hT2 _ (h1 k hk)
          · exact h2⟩
      · exact ⟨γ1, T1, ho1, hT1, fun k hk => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact h1 k hk
          · rwa [isL_unique H hR hP ho1 hT2 hT1] at h2⟩
      · exact ⟨γ1, T1, ho1, hT1, fun k hk => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact h1 k hk
          · exact isL_mono H hR hP ho1 h hT2 hT1 _ h2⟩

omit hR hP in
/-- The set `{y ∈ T | (T, ∈) ⊨ φ[y, E]}` exists. -/
theorem satSet_exists {T R E : V} (hR' : MemRel H T R) (hE : IsEnvOn H T E) (hne : ∃ d, mem d T)
    (φ : Form) : ∃ S, ∀ y, mem y S ↔ mem y T ∧ RSat mem T (scons y (envVals H E)) φ := by
  have hst := setStructure_of_memRel H hR' hne
  obtain ⟨S, hS⟩ := sep_of H (fun y => SatIn H T R (formCode H φ) (econs H y E))
    (.ex 5 (.and (econsAtomF 5 0 4) (satInF 1 2 3 5)))
    (fun i => if i = 1 then T else if i = 2 then R else if i = 3 then formCode H φ else E)
    (fun y => by
      simp only [NSat, nsat_satInF H]
      refine ⟨fun ⟨e', he', hs⟩ => ?_, fun hs => ⟨econs H y E, ?_, ?_⟩⟩
      · rw [nsat_econsAtomF H _ _ _ _ (by simp (disch := omega) only [upd_other]; exact hE.1.1)]
          at he'
        simp (disch := omega) only [upd_same, upd_other] at he' hs
        simp only [show (2 : Nat) ≠ 1 by omega, show (3 : Nat) ≠ 1 by omega,
          show (3 : Nat) ≠ 2 by omega, show (4 : Nat) ≠ 1 by omega, show (4 : Nat) ≠ 2 by omega,
          show (4 : Nat) ≠ 3 by omega, if_false] at he' hs
        rw [he'] at hs; exact hs
      · rw [nsat_econsAtomF H _ _ _ _ (by simp (disch := omega) only [upd_other]; exact hE.1.1)]
        simp (disch := omega) only [upd_same, upd_other]
        simp
      · simp (disch := omega) only [upd_same, upd_other]
        simpa using hs) T
  refine ⟨S, fun y => ?_⟩
  rw [hS y]
  refine and_congr_right fun hy => ?_
  rw [satIn_formCode H hst hR' φ _ (econs_isEnvOn H hE hy)]
  exact rsat_congr T φ fun n => envVals_econs H hE y n

/-- **Separation in L.** -/
theorem inL_sep (φ : Form) (e : Nat → V) (he : ∀ n, InL H hP (e n)) {a : V} (ha : InL H hP a) :
    ∃ s, InL H hP s ∧ ∀ z, mem z s ↔ mem z a ∧ CSat mem (InL H hP) (scons z e) φ := by
  let m := bound φ
  let v : Nat → V := fun k => if k < m then e k else a
  have hv : ∀ k, k < m + 1 → InL H hP (v k) := fun k _ => by
    simp only [v]; split
    · exact he k
    · exact ha
  obtain ⟨α0, T0, hα0, hT0, hvT0⟩ := inL_common H hR hP v m hv
  obtain ⟨β, hαβ, hC⟩ := closed_exists H hR hP (qbodies φ) hα0
  obtain ⟨Tβ, hTβ⟩ := isL_exists H hR hP hC.1
  have hsub := isL_mono H hR hP hC.1 hαβ hT0 hTβ
  have haT : mem a Tβ := by simpa [v] using hsub _ (hvT0 m (by omega))
  obtain ⟨E, hE, hEv⟩ := mk_env H haT (m + 1) v fun k hk => hsub _ (hvT0 k hk)
  obtain ⟨R, hR'⟩ := memRel_exists H hP Tβ
  let φ' : Form := .fAnd (.fMem 0 (m + 1)) φ
  obtain ⟨S, hS⟩ := satSet_exists H hR' hE ⟨a, haT⟩ φ'
  have hTt := isL_trans H hR hP hC.1 hTβ
  have hEa : envVals H E m = a := by rw [hEv m (by omega)]; simp [v]
  have agree : ∀ z, CSat mem (InL H hP) (scons z (envVals H E)) φ ↔
      CSat mem (InL H hP) (scons z e) φ := fun z =>
    csat_ext_free _ φ _ _ fun n hn => by
      cases n with
      | zero => rfl
      | succ k =>
          have hk : k < m := by have := free_lt_bound φ _ hn; simp only [m]; omega
          simp only [scons]; rw [hEv k (by omega)]; simp [v, hk]
  have hall : ∀ z, mem z Tβ → ∀ n, mem (scons z (envVals H E) n) Tβ := fun z hz n => by
    cases n with
    | zero => exact hz
    | succ n => exact isEnvOn_apply H hE (natV_mem_omega H n)
  refine ⟨S, inL_of_definable H hR hP hC.1 hTβ (fun z hz => ((hS z).1 hz).1)
    (definable_env H hP hE φ' S hS), fun z => ?_⟩
  rw [hS z]
  simp only [φ', RSat, scons, hEa]
  constructor
  · rintro ⟨hz, hza, hφ⟩
    exact ⟨hza, (agree z).1 ((reflect H hR hP hC hTβ φ (fun _ h => h) _ (hall z hz)).2 hφ)⟩
  · rintro ⟨hza, hφ⟩
    have hz := hTt a haT z hza
    exact ⟨hz, hza, (reflect H hR hP hC hTβ φ (fun _ h => h) _ (hall z hz)).1 ((agree z).2 hφ)⟩

end Sep

/-! ## Renaming and the constructible substructure -/

theorem csat_rename (P : V → Prop) :
    ∀ (φ : Form) (r : Nat → Nat) (e : Nat → V),
      CSat mem P e (rename r φ) ↔ CSat mem P (fun n => e (r n)) φ
  | .fMem _ _, _, _ => Iff.rfl
  | .fEq _ _, _, _ => Iff.rfl
  | .fBot, _, _ => Iff.rfl
  | .fImp a b, r, e | .fAnd a b, r, e | .fOr a b, r, e => by
      simp only [rename, CSat, csat_rename P a r e, csat_rename P b r e]
  | .fAll a, r, e => by
      simp only [rename, CSat]
      refine forall_congr' fun d => imp_congr_right fun _ => ?_
      rw [csat_rename P a]
      exact Iff.of_eq (congrArg (fun e' => CSat mem P e' a) (funext fun n => up_env r d e n))
  | .fEx a, r, e => by
      simp only [rename, CSat]
      refine exists_congr fun d => and_congr_right fun _ => ?_
      rw [csat_rename P a]
      exact Iff.of_eq (congrArg (fun e' => CSat mem P e' a) (funext fun n => up_env r d e n))

theorem vals_scons (P : V → Prop) (x : {x // P x}) (e : Nat → {x // P x}) :
    (fun n => (scons x e n).1) = scons x.1 (fun n => (e n).1) :=
  funext fun n => by cases n <;> rfl

/-- Satisfaction in the substructure on a class is satisfaction relativized to it. -/
theorem sat_sub (P : V → Prop) :
    ∀ (φ : Form) (e : Nat → {x // P x}),
      Sat (fun a b : {x // P x} => mem a.1 b.1) e φ ↔ CSat mem P (fun n => (e n).1) φ
  | .fMem _ _, _ => Iff.rfl
  | .fEq _ _, e => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  | .fBot, _ => Iff.rfl
  | .fImp a b, e | .fAnd a b, e | .fOr a b, e => by
      simp only [Sat, CSat, sat_sub P a e, sat_sub P b e]
  | .fAll a, e => by
      have key d := (sat_sub P a (scons d e)).trans (by rw [vals_scons P d e])
      exact ⟨fun h d hd => (key ⟨d, hd⟩).1 (h ⟨d, hd⟩), fun h d => (key d).2 (h d.1 d.2)⟩
  | .fEx a, e => by
      have key d := (sat_sub P a (scons d e)).trans (by rw [vals_scons P d e])
      exact ⟨fun ⟨d, hd⟩ => ⟨d.1, d.2, (key d).1 hd⟩, fun ⟨d, hd, h⟩ => ⟨⟨d, hd⟩, (key _).2 h⟩⟩


/-! ## Replacement and the model -/

section Model

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP

omit hR hP in
theorem omega_trans : ∀ n, mem n (omegaV H) → ∀ y, mem y n → mem y (omegaV H) := by
  have key := omega_ind H (toForm id (.all 2 (.imp (.mem 2 0) (.mem 2 1)))) (fun _ => omegaV H)
  have hspec : ∀ n, Sat mem (scons n (fun _ => omegaV H))
      (toForm id (.all 2 (.imp (.mem 2 0) (.mem 2 1)))) ↔ ∀ y, mem y n → mem y (omegaV H) := by
    intro n
    rw [sat_toForm]
    simp only [NSat]
    simp (disch := omega) only [upd_same, upd_other]
    rfl
  intro n hn
  refine (hspec n).1 (key ((hspec _).2 fun y hy => absurd hy (vempty_spec H y))
    (fun m hm ih => (hspec _).2 fun y hy =>
      ((vsucc_spec H m y).1 hy).elim ((hspec m).1 ih y) fun e => e ▸ hm) n hn)

omit hR hP in
theorem ord_omega : Ord mem (omegaV H) :=
  ⟨fun n hn y hy => omega_trans H n hn y hy, fun n hn => nat_transitive H n hn⟩

theorem inL_ord {a : V} (ha : Ord mem a) : InL H hP a := by
  obtain ⟨S, hS⟩ := isL_exists H hR hP (ord_succ H ha)
  exact ⟨_, S, ord_succ H ha, hS, ord_mem_isL H hR hP ha hS⟩

/-- Every stage is constructible. -/
theorem inL_stage {b T : V} (hb : Ord mem b) (hT : IsL H hP b T) : InL H hP T := by
  obtain ⟨S, hS⟩ := isL_exists H hR hP (ord_succ H hb)
  exact ⟨_, S, ord_succ H hb, hS, isL_mem H hR hP (ord_succ H hb) (vsucc_self H b) hT hS⟩

omit H hR hP in
def rslots (m : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | k + 2 => if k < m then 100 + k else 100

omit H hR hP in
def swapRen : Nat → Nat
  | 0 => 1
  | 1 => 0
  | k + 2 => k + 3

/-- **Replacement in L.** -/
theorem inL_repl (psi : Form) (e : Nat → V) (he : ∀ n, InL H hP (e n))
    (hfun : ∀ x y1 y2, InL H hP x → InL H hP y1 → InL H hP y2 →
      CSat mem (InL H hP) (scons y1 (scons x e)) psi →
      CSat mem (InL H hP) (scons y2 (scons x e)) psi → y1 = y2)
    {a : V} (ha : InL H hP a) :
    ∃ r, InL H hP r ∧ ∀ y, InL H hP y →
      (mem y r ↔ ∃ x, mem x a ∧ CSat mem (InL H hP) (scons y (scons x e)) psi) := by
  let Rel : V → V → Prop := fun x y => InL H hP x ∧ InL H hP y ∧
    CSat mem (InL H hP) (scons y (scons x e)) psi
  obtain ⟨Img, hImg⟩ := repl_of H Rel
    (.and (inLF H hP 1) (.and (inLF H hP 0)
      (relT (inLF H hP) (rslots (bound psi)) (100 + bound psi + 1) psi)))
    (fun i => e (i - 100))
    (fun x y => by
      simp only [NSat, nsat_inLF H hP]
      simp (disch := omega) only [upd_same, upd_other]
      refine and_congr_right fun _ => and_congr_right fun _ => ?_
      rw [nsat_relT (InL H hP) (inLF H hP) (nsat_inLF H hP) psi _ _ _ fun i => by
        rcases i with _ | _ | k <;> simp only [rslots] <;> first | omega | (split <;> omega)]
      refine csat_ext_free _ psi _ _ fun n hn => ?_
      have hlt := free_lt_bound psi n hn
      rcases n with _ | _ | k
      · show upd (upd _ 1 x) 0 y 0 = y
        rw [upd_same]
      · show upd (upd _ 1 x) 0 y 1 = x
        rw [upd_other _ _ (by omega), upd_same]
      · have hk : k < bound psi := by omega
        simp only [rslots, hk, if_true, scons]
        rw [upd_other _ _ (by omega), upd_other _ _ (by omega)]
        simp)
    (fun x y1 y2 h1 h2 => hfun x y1 y2 h1.1 h1.2.1 h2.2.1 h1.2.2 h2.2.2) a
  obtain ⟨β, T, hβ, hT, hImgT⟩ := stage_bound H hR hP (A := Img) fun y hy =>
    ((hImg y).1 hy).elim fun _ h => h.2.2.1
  obtain ⟨s, hs, hsspec⟩ := inL_sep H hR hP (.fEx (.fAnd (.fMem 0 2) (rename swapRen psi)))
    (scons a e) (fun n => by cases n with | zero => exact ha | succ n => exact he n)
    (inL_stage H hR hP hβ hT)
  refine ⟨s, hs, fun y hy => ?_⟩
  rw [hsspec y]
  have hren : ∀ x, CSat mem (InL H hP) (scons x (scons y (scons a e))) (rename swapRen psi) ↔
      CSat mem (InL H hP) (scons y (scons x e)) psi := fun x => by
    rw [csat_rename]
    exact Iff.of_eq (congrArg (fun e' => CSat mem (InL H hP) e' psi) (funext fun n => by
      rcases n with _ | _ | k <;> rfl))
  simp only [CSat, scons, hren]
  constructor
  · rintro ⟨-, x, -, hxa, hx⟩; exact ⟨x, hxa, hx⟩
  · rintro ⟨x, hxa, hx⟩
    have hxL := inL_trans H hR hP ha hxa
    exact ⟨hImgT y ((hImg y).2 ⟨x, hxa, hxL, hy, hx⟩), x, hxL, hxa, hx⟩

end Model

/-- The membership relation of the constructible substructure. -/
def memL (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) :
    {x // InL H hP x} → {x // InL H hP x} → Prop := fun a b => mem a.1 b.1

section ModelAxioms

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP

/-- **The constructible substructure satisfies the ZF bundle.** -/
theorem L_zfAxioms : ZFAxioms (memL H hP) where
  ext a b h := Subtype.ext (H.ext a.1 b.1 fun x =>
    ⟨fun hx => (h ⟨x, inL_trans H hR hP a.2 hx⟩).1 hx,
     fun hx => (h ⟨x, inL_trans H hR hP b.2 hx⟩).2 hx⟩)
  sep phi e a := by
    obtain ⟨s, hs, hspec⟩ := inL_sep H hR hP phi (fun n => (e n).1) (fun n => (e n).2) a.2
    refine ⟨⟨s, hs⟩, fun x => ?_⟩
    show mem x.1 s ↔ mem x.1 a.1 ∧ _
    rw [hspec x.1]
    exact and_congr_right fun _ => ((sat_sub (mem := mem) (InL H hP) phi (scons x e)).trans
      (by rw [vals_scons (InL H hP) x e])).symm
  pair a b := by
    refine ⟨⟨_, inL_pair H hR hP a.2 b.2⟩, fun x => ?_⟩
    show mem x.1 (vpair H a.1 b.1) ↔ _
    rw [vpair_spec H a.1 b.1 x.1, Subtype.ext_iff, Subtype.ext_iff]
  union u := by
    refine ⟨⟨_, inL_union H hR hP u.2⟩, fun x => ?_⟩
    show mem x.1 (vunion H u.1) ↔ _
    rw [vunion_spec H u.1 x.1]
    exact ⟨fun ⟨v, hxv, hvu⟩ => ⟨⟨v, inL_trans H hR hP u.2 hvu⟩, hxv, hvu⟩,
      fun ⟨v, hxv, hvu⟩ => ⟨v.1, hxv, hvu⟩⟩
  inf := by
    have hω := inL_ord H hR hP (ord_omega H)
    have he0 := inL_ord H hR hP (ord_of_mem (ord_omega H) (vempty_in_omega H))
    refine ⟨⟨_, hω⟩, ⟨⟨_, he0⟩, vempty_in_omega H, fun z hz => vempty_spec H z.1 hz⟩, fun x hx => ?_⟩
    have hxo := ord_of_mem (ord_omega H) hx
    refine ⟨⟨_, inL_ord H hR hP (ord_succ H hxo)⟩, omega_succ H x.1 hx, fun t => ?_⟩
    show mem t.1 (vsucc H x.1) ↔ _
    rw [vsucc_spec H x.1 t.1, Subtype.ext_iff]
    exact Iff.rfl
  repl psi e hfun a := by
    have hrel : ∀ (x y : {x // InL H hP x}), relOf (memL H hP) psi e y x ↔
        CSat mem (InL H hP) (scons y.1 (scons x.1 (fun n => (e n).1))) psi := fun x y => by
      unfold relOf
      refine (sat_sub (mem := mem) (InL H hP) psi _).trans ?_
      exact Iff.of_eq (congrArg (fun e' => CSat mem (InL H hP) e' psi) (funext fun n => by
        rcases n with _ | _ | k <;> rfl))
    obtain ⟨r, hr, hspec⟩ := inL_repl H hR hP psi (fun n => (e n).1) (fun n => (e n).2)
      (fun x y1 y2 hx hy1 hy2 h1 h2 => congrArg Subtype.val
        (hfun ⟨x, hx⟩ ⟨y1, hy1⟩ ⟨y2, hy2⟩ ((hrel _ _).2 h1) ((hrel _ _).2 h2))) a.2
    refine ⟨⟨r, hr⟩, fun y => ?_⟩
    show mem y.1 r ↔ _
    rw [hspec y.1 y.2]
    exact ⟨fun ⟨x, hxa, hx⟩ => ⟨⟨x, inL_trans H hR hP a.2 hxa⟩, hxa, (hrel _ _).2 hx⟩,
      fun ⟨x, hxa, hx⟩ => ⟨x.1, hxa, (hrel _ _).1 hx⟩⟩

theorem L_power : ∀ a : {x // InL H hP x}, ∃ p : {x // InL H hP x}, ∀ x : {x // InL H hP x},
    memL H hP x p ↔ Sub (memL H hP) x a := by
  intro a
  obtain ⟨p, hp, hspec⟩ := inL_power H hR hP a.2
  refine ⟨⟨p, hp⟩, fun x => ?_⟩
  show mem x.1 p ↔ _
  rw [hspec x.1 x.2]
  exact ⟨fun h y hy => h y.1 hy, fun h y hy => h ⟨y, inL_trans H hR hP x.2 hy⟩ hy⟩

theorem L_regular : Regular (memL H hP) := by
  intro a ⟨x, hx⟩
  obtain ⟨m, hm, hmin⟩ := hR a.1 ⟨x.1, hx⟩
  exact ⟨⟨m, inL_trans H hR hP a.2 hm⟩, hm, fun ⟨z, hz1, hz2⟩ => hmin ⟨z.1, hz1, hz2⟩⟩

end ModelAxioms

/-- Any structure with the ZF bundle, Power and Regularity is a model of `ZFax_s`. -/
theorem zfax_of {W : Type u} {memW : W → W → Prop} (H : ZFAxioms memW)
    (hP : ∀ a, ∃ p, ∀ x, memW x p ↔ Sub memW x a) (hR : Regular memW) (v : Nat → W) :
    ∀ f, ZFax_s f → Sat memW v f := by
  intro f hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ | ⟨psi, rfl⟩
  · exact (closeN_valid (bound Ext_form) Ext_form).mpr (bridge_Ext.mpr H.ext) v
  · exact (closeN_valid (bound Reg_form) Reg_form).mpr (bridge_Reg.mpr hR) v
  · exact (closeN_valid (bound Pow_form) Pow_form).mpr (bridge_Pow.mpr hP) v
  · exact (closeN_valid (bound Pair_form) Pair_form).mpr (bridge_Pair.mpr H.pair) v
  · exact (closeN_valid (bound Union_form) Union_form).mpr (bridge_Union.mpr H.union) v
  · exact (closeN_valid (bound Inf_form) Inf_form).mpr (fun env => (bridge_Inf env).mpr H.inf) v
  · exact (closeN_valid (bound (Sep_form phi)) (Sep_form phi)).mpr
      (fun env => bridge_Sep.mpr H.sep phi env) v
  · exact (closeN_valid (bound (Repl_form psi)) (Repl_form psi)).mpr
      (fun env => (bridge_Repl psi env).mpr (H.repl psi env)) v

/-- **The constructible class of a model of ZF is a model of ZF.** -/
theorem L_models_ZF (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) (v : Nat → {x // InL H hP x}) :
    ∀ f, ZFax_s f → Sat (memL H hP) v f :=
  zfax_of (L_zfAxioms H hR hP) (L_power H hR hP) (L_regular H hR hP) v

end SetTheory.BusyBeaver.ZFC.ConstructibleZF
