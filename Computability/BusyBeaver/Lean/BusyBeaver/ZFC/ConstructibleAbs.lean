import BusyBeaver.ZFC.SatSupport

/-!
Absoluteness between a model of ZF and its constructible class.

`N = {x // InL x}` with `memL` is a model of the ZF bundle
(`ConstructibleZF.L_zfAxioms`). Basic set operations, internal `ω`, recorded
graph application, environment shift, truth bits and satisfaction-certificate
relations agree on constructible data. `satIn_iff` proves satisfaction agreement
for a constructible set structure and environment when the code is valid in
both the ambient and constructible models. `memRel_iff` compares the encoded
membership relation.

The extension below proves formula-code absoluteness, replaces an arbitrary
ambient environment by a constructible environment on its internally finite
support, and transports definability and `Def`. Hierarchy comparison then gives
`vEqL`: every constructible set is constructible in the sense of the constructible
model. The internal well-order and Choice arguments remain separate obligations.
-/

namespace SetTheory.BusyBeaver.ZFC.ConstructibleAbs

open NamedZF NForm InternalOrd InternalRank TransRec ConstructibleDef Constructible
  ConstructibleZF LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

/-! ## Inversion for formula codes (in any model of the ZF bundle) -/

section Inversion

/-- `c = ⟨t, x⟩` with `t` a numeral. -/
def tagF (c t x : Nat) : NForm :=
  .ex (c + x + 1) (.and (ConstructibleReflect.natF (c + x + 1) t) (kpairF c (c + x + 1) x))

theorem nsat_tagF (H : ZFAxioms mem) (ρ : Nat → V) (c t x : Nat) :
    NSat mem ρ (tagF c t x) ↔ ρ c = kpair H (natV H t) (ρ x) := by
  simp only [tagF, NSat, ConstructibleReflect.nsat_natF H, nsat_kpairF H]
  simp (disch := omega) only [upd_same, upd_other]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

/-- `c = ⟨t, ⟨a, b⟩⟩`. -/
def tag2F (c t a b : Nat) : NForm :=
  .ex (c + a + b + 1) (.and (kpairF (c + a + b + 1) a b) (tagF c t (c + a + b + 1)))

theorem nsat_tag2F (H : ZFAxioms mem) (ρ : Nat → V) (c t a b : Nat) :
    NSat mem ρ (tag2F c t a b) ↔ ρ c = kpair H (natV H t) (kpair H (ρ a) (ρ b)) := by
  simp only [tag2F, NSat, nsat_kpairF H, nsat_tagF H]
  simp (disch := omega) only [upd_same, upd_other]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

/-- The possible shapes of a formula code. -/
def CodeShape (H : ZFAxioms mem) (c : V) : Prop :=
  (∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧
    (c = kpair H (natV H 0) (kpair H i j) ∨ c = kpair H (natV H 1) (kpair H i j))) ∨
  c = kpair H (natV H 2) (vempty H) ∨
  (∃ a b, IsFormCodeSem H a ∧ IsFormCodeSem H b ∧
    (c = kpair H (natV H 3) (kpair H a b) ∨ c = kpair H (natV H 4) (kpair H a b) ∨
      c = kpair H (natV H 5) (kpair H a b))) ∨
  (∃ a, IsFormCodeSem H a ∧ (c = kpair H (natV H 6) a ∨ c = kpair H (natV H 7) a))

/-- The code property and its shape (name `0`). -/
def shapeF : NForm :=
  .and (ConstructibleDef.isCodeF 0)
  (.or (.ex 1 (.ex 2 (.and (SatSupport.inOmegaF 1) (.and (SatSupport.inOmegaF 2)
      (.or (tag2F 0 0 1 2) (tag2F 0 1 1 2))))))
  (.or (.ex 1 (.and (.all 2 (.imp (.mem 2 1) .bot)) (tagF 0 2 1)))
  (.or (.ex 1 (.ex 2 (.and (ConstructibleDef.isCodeF 1) (.and (ConstructibleDef.isCodeF 2)
      (.or (tag2F 0 3 1 2) (.or (tag2F 0 4 1 2) (tag2F 0 5 1 2)))))))
    (.ex 1 (.and (ConstructibleDef.isCodeF 1) (.or (tagF 0 6 1) (tagF 0 7 1)))))))

theorem nsat_shapeF (H : ZFAxioms mem) (ρ : Nat → V) :
    NSat mem ρ shapeF ↔ IsFormCodeSem H (ρ 0) ∧ CodeShape H (ρ 0) := by
  simp only [shapeF, NSat, ConstructibleDef.nsat_isCodeF H, SatSupport.nsat_inOmegaF H,
    nsat_tag2F H, nsat_tagF H]
  simp (disch := omega) only [upd_same, upd_other]
  refine and_congr_right fun _ => or_congr Iff.rfl (or_congr
    ⟨fun ⟨z, hz, h⟩ => ?_, fun h => ⟨vempty H, fun w hw => vempty_spec H w hw, h⟩⟩ Iff.rfl)
  rw [h, show z = vempty H from H.ext _ _ fun w =>
    ⟨fun hw => absurd hw (hz w), fun hw => absurd hw (vempty_spec H w)⟩]

/-- **Inversion**: every internal formula code is an atom, `⊥`, or a constructor
applied to internal codes. -/
theorem code_shape (H : ZFAxioms mem) : ∀ c, IsFormCodeSem H c → CodeShape H c :=
  fun c hc => (isFormCodeSem_ind' H (fun c => IsFormCodeSem H c ∧ CodeShape H c)
    (toForm id shapeF) (fun _ => vempty H)
    (fun y => by rw [sat_toForm, nsat_shapeF H]; rfl)
    (fun a b ha hb => ⟨isFormCodeSem_memAtom H ha hb, Or.inl ⟨a, b, ha, hb, Or.inl rfl⟩⟩)
    (fun a b ha hb => ⟨isFormCodeSem_eqAtom H ha hb, Or.inl ⟨a, b, ha, hb, Or.inr rfl⟩⟩)
    ⟨isFormCodeSem_bot H, Or.inr (Or.inl rfl)⟩
    (fun a b ha hb => ⟨isFormCodeSem_imp H ha.1 hb.1,
      Or.inr (Or.inr (Or.inl ⟨a, b, ha.1, hb.1, Or.inl rfl⟩))⟩)
    (fun a b ha hb => ⟨isFormCodeSem_and H ha.1 hb.1,
      Or.inr (Or.inr (Or.inl ⟨a, b, ha.1, hb.1, Or.inr (Or.inl rfl)⟩))⟩)
    (fun a b ha hb => ⟨isFormCodeSem_or H ha.1 hb.1,
      Or.inr (Or.inr (Or.inl ⟨a, b, ha.1, hb.1, Or.inr (Or.inr rfl)⟩))⟩)
    (fun a ha => ⟨isFormCodeSem_all H ha.1, Or.inr (Or.inr (Or.inr ⟨a, ha.1, Or.inl rfl⟩))⟩)
    (fun a ha => ⟨isFormCodeSem_ex H ha.1, Or.inr (Or.inr (Or.inr ⟨a, ha.1, Or.inr rfl⟩))⟩)
    c hc).2

end Inversion
section Ops

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP

/-- Bounded quantifiers agree because every member of a constructible set is constructible. -/
private theorem forall_memL_iff (A : {x // InL H hP x}) (P : V → Prop) :
    (∀ x : {x // InL H hP x}, memL H hP x A → P x.1) ↔ ∀ x, mem x A.1 → P x :=
  ⟨fun h x hx => h ⟨x, inL_trans H hR hP A.2 hx⟩ hx, fun h x hx => h x.1 hx⟩

private theorem exists_memL_iff (A : {x // InL H hP x}) (P : V → Prop) :
    (∃ x : {x // InL H hP x}, memL H hP x A ∧ P x.1) ↔ ∃ x, mem x A.1 ∧ P x :=
  ⟨fun ⟨x, hx, h⟩ => ⟨x.1, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨⟨x, inL_trans H hR hP A.2 hx⟩, hx, h⟩⟩

/-- Equality of a constructible set with an ambient set, by extensionality. -/
theorem val_eq {u : {x // InL H hP x}} {v : V} (hv : ∀ z, mem z v → InL H hP z)
    (h : ∀ z : {x // InL H hP x}, mem z.1 u.1 ↔ mem z.1 v) : u.1 = v :=
  H.ext _ _ fun z => ⟨fun hz => (h ⟨z, inL_trans H hR hP u.2 hz⟩).1 hz,
    fun hz => (h ⟨z, hv z hz⟩).2 hz⟩

theorem val_vpair (a b : {x // InL H hP x}) :
    (vpair (L_zfAxioms H hR hP) a b).1 = vpair H a.1 b.1 := by
  refine val_eq H hR hP (fun z hz => ?_) fun z => ?_
  · exact ((vpair_spec H _ _ z).1 hz).elim (· ▸ a.2) (· ▸ b.2)
  · rw [show mem z.1 (vpair (L_zfAxioms H hR hP) a b).1 ↔ _ from
      vpair_spec (L_zfAxioms H hR hP) a b z, vpair_spec H, Subtype.ext_iff, Subtype.ext_iff]

theorem val_vsingle (a : {x // InL H hP x}) :
    (vsingle (L_zfAxioms H hR hP) a).1 = vsingle H a.1 :=
  val_vpair H hR hP a a

theorem val_kpair (a b : {x // InL H hP x}) :
    (kpair (L_zfAxioms H hR hP) a b).1 = kpair H a.1 b.1 := by
  show (vpair (L_zfAxioms H hR hP) _ _).1 = vpair H _ _
  rw [val_vpair H hR hP, val_vsingle H hR hP, val_vpair H hR hP]

theorem val_vempty : (vempty (L_zfAxioms H hR hP)).1 = vempty H :=
  val_eq H hR hP (fun z hz => absurd hz (vempty_spec H z))
    fun z => iff_of_false (vempty_spec (L_zfAxioms H hR hP) z) (vempty_spec H _)

theorem val_vunion (a : {x // InL H hP x}) :
    (vunion (L_zfAxioms H hR hP) a).1 = vunion H a.1 := by
  refine val_eq H hR hP (fun z hz => ?_) fun z => ?_
  · obtain ⟨v, hzv, hva⟩ := (vunion_spec H _ z).1 hz
    exact inL_trans H hR hP (inL_trans H hR hP a.2 hva) hzv
  · rw [show mem z.1 (vunion (L_zfAxioms H hR hP) a).1 ↔ _ from
      vunion_spec (L_zfAxioms H hR hP) a z, vunion_spec H]
    simpa only [memL, and_comm] using exists_memL_iff H hR hP a (fun v => mem z.1 v)

theorem val_vcup (a b : {x // InL H hP x}) :
    (vcup (L_zfAxioms H hR hP) a b).1 = vcup H a.1 b.1 := by
  show (vunion (L_zfAxioms H hR hP) _).1 = vunion H _
  rw [val_vunion H hR hP, val_vpair H hR hP]

theorem val_vsucc (a : {x // InL H hP x}) :
    (vsucc (L_zfAxioms H hR hP) a).1 = vsucc H a.1 := by
  show (vcup (L_zfAxioms H hR hP) _ _).1 = vcup H _ _
  rw [val_vcup H hR hP, val_vsingle H hR hP]

theorem val_natV : ∀ k, (natV (L_zfAxioms H hR hP) k).1 = natV H k
  | 0 => val_vempty H hR hP
  | k + 1 => by rw [natV_succ, natV_succ, val_vsucc H hR hP, val_natV k]

theorem inductive_iff (c : {x // InL H hP x}) :
    inductiveV (L_zfAxioms H hR hP) c ↔ inductiveV H c.1 := by
  unfold inductiveV
  change (mem (vempty (L_zfAxioms H hR hP)).1 c.1 ∧
    ∀ y : {x // InL H hP x}, mem y.1 c.1 → mem (vsucc (L_zfAxioms H hR hP) y).1 c.1) ↔ _
  simp only [val_vempty H hR hP, val_vsucc H hR hP]
  exact and_congr Iff.rfl (forall_memL_iff H hR hP c fun y => mem (vsucc H y) c.1)

theorem inL_omega : InL H hP (omegaV H) := inL_ord H hR hP (ord_omega H)

theorem val_omegaV : (omegaV (L_zfAxioms H hR hP)).1 = omegaV H := by
  refine val_eq H hR hP (fun z hz => inL_trans H hR hP (inL_omega H hR hP) hz) fun z => ?_
  rw [show mem z.1 (omegaV (L_zfAxioms H hR hP)).1 ↔ _ from
    mem_omega_iff (L_zfAxioms H hR hP) z, mem_omega_iff H]
  exact ⟨fun h c hc => (mem_omega_iff H z.1).1 (h ⟨omegaV H, inL_omega H hR hP⟩
    ((inductive_iff H hR hP _).2 (omega_inductive H))) c hc,
    fun h c hc => h c.1 ((inductive_iff H hR hP c).1 hc)⟩

theorem mem_omegaN (n : {x // InL H hP x}) :
    mem n.1 (omegaV (L_zfAxioms H hR hP)).1 ↔ mem n.1 (omegaV H) := by
  rw [val_omegaV H hR hP]

/-- The components of a constructible pair are constructible. -/
theorem inL_kpair {a b : V} (h : InL H hP (kpair H a b)) : InL H hP a ∧ InL H hP b := by
  have hs : InL H hP (vsingle H a) := inL_trans H hR hP h ((kpair_mem H a b _).2 (Or.inl rfl))
  have hp : InL H hP (vpair H a b) := inL_trans H hR hP h ((kpair_mem H a b _).2 (Or.inr rfl))
  exact ⟨inL_trans H hR hP hs ((vsingle_spec H a a).2 rfl),
    inL_trans H hR hP hp ((vpair_spec H a b b).2 (Or.inr rfl))⟩

theorem inL_of_kpair_mem {a b F : V} (hF : InL H hP F) (h : mem (kpair H a b) F) :
    InL H hP a ∧ InL H hP b :=
  inL_kpair H hR hP (inL_trans H hR hP hF h)

theorem kpairN_mem (a b F : {x // InL H hP x}) :
    mem (kpair (L_zfAxioms H hR hP) a b).1 F.1 ↔ mem (kpair H a.1 b.1) F.1 := by
  rw [val_kpair H hR hP]

theorem kpairN_eq (a b c : {x // InL H hP x}) :
    c = kpair (L_zfAxioms H hR hP) a b ↔ c.1 = kpair H a.1 b.1 := by
  rw [Subtype.ext_iff, val_kpair H hR hP]

/-- Functionality of a graph agrees. -/
theorem functional_iff (F : {x // InL H hP x}) :
    (∀ x y y' : {x // InL H hP x}, memL H hP (kpair (L_zfAxioms H hR hP) x y) F →
      memL H hP (kpair (L_zfAxioms H hR hP) x y') F → y = y') ↔
    (∀ x y y', mem (kpair H x y) F.1 → mem (kpair H x y') F.1 → y = y') := by
  simp only [memL, val_kpair H hR hP, Subtype.ext_iff]
  refine ⟨fun h x y y' hy hy' => ?_, fun h x y y' => h x.1 y.1 y'.1⟩
  obtain ⟨hx, hyL⟩ := inL_of_kpair_mem H hR hP F.2 hy
  obtain ⟨-, hy'L⟩ := inL_of_kpair_mem H hR hP F.2 hy'
  exact h ⟨x, hx⟩ ⟨y, hyL⟩ ⟨y', hy'L⟩ hy hy'

theorem isFunctionOn_iff (F d : {x // InL H hP x}) :
    IsFunctionOn (L_zfAxioms H hR hP) F d ↔ IsFunctionOn H F.1 d.1 := by
  unfold IsFunctionOn
  rw [functional_iff H hR hP]
  simp only [memL, val_kpair H hR hP, Subtype.ext_iff]
  refine and_congr Iff.rfl (and_congr ⟨fun h x hx => ?_, fun h x hx => ?_⟩
    ⟨fun h p hp => ?_, fun h p hp => ?_⟩)
  · obtain ⟨y, hy⟩ := h ⟨x, inL_trans H hR hP d.2 hx⟩ hx
    exact ⟨y.1, hy⟩
  · obtain ⟨y, hy⟩ := h x.1 hx
    exact ⟨⟨y, (inL_of_kpair_mem H hR hP F.2 hy).2⟩, hy⟩
  · obtain ⟨x, y, hx, he⟩ := h ⟨p, inL_trans H hR hP F.2 hp⟩ hp
    exact ⟨x.1, y.1, hx, he⟩
  · obtain ⟨x, y, hx, he⟩ := h p.1 hp
    have hxy := inL_kpair H hR hP (he ▸ p.2)
    exact ⟨⟨x, hxy.1⟩, ⟨y, hxy.2⟩, hx, he⟩

theorem isEnvOn_iff (A E : {x // InL H hP x}) :
    IsEnvOn (L_zfAxioms H hR hP) A E ↔ IsEnvOn H A.1 E.1 := by
  unfold IsEnvOn
  rw [isFunctionOn_iff H hR hP]
  simp only [val_omegaV H hR hP, memL, val_kpair H hR hP]
  refine and_congr Iff.rfl ⟨fun h n y hy => ?_, fun h n y hy => h n.1 y.1 hy⟩
  obtain ⟨hn, hyL⟩ := inL_of_kpair_mem H hR hP E.2 hy
  exact h ⟨n, hn⟩ ⟨y, hyL⟩ hy

/-- Application agrees on a graph with a recorded value. -/
theorem val_applyV {F x : {x // InL H hP x}}
    (hfun : ∀ a b b', mem (kpair H a b) F.1 → mem (kpair H a b') F.1 → b = b')
    {y : V} (hy : mem (kpair H x.1 y) F.1) : (applyV (L_zfAxioms H hR hP) F x).1 = y := by
  rw [applyV_eq (L_zfAxioms H hR hP) ((functional_iff H hR hP F).2 hfun) (x := x)
    (y := ⟨y, (inL_of_kpair_mem H hR hP F.2 hy).2⟩) ((kpairN_mem H hR hP _ _ _).2 hy)]

theorem val_applyV_env {A E n : {x // InL H hP x}} (hE : IsEnvOn H A.1 E.1)
    (hn : mem n.1 (omegaV H)) : (applyV (L_zfAxioms H hR hP) E n).1 = applyV H E.1 n.1 :=
  val_applyV H hR hP hE.1.1 (applyV_mem H (hE.1.2.1 n.1 hn))

theorem inL_nat {n : V} (hn : mem n (omegaV H)) : InL H hP n :=
  inL_trans H hR hP (inL_omega H hR hP) hn

theorem inL_kpair_of {a b : V} (ha : InL H hP a) (hb : InL H hP b) : InL H hP (kpair H a b) :=
  inL_pair H hR hP (inL_pair H hR hP ha ha) (inL_pair H hR hP ha hb)

theorem val_econs {d E : {x // InL H hP x}}
    (hfun : ∀ a b b', mem (kpair H a b) E.1 → mem (kpair H a b') E.1 → b = b') :
    (econs (L_zfAxioms H hR hP) d E).1 = econs H d.1 E.1 := by
  have hfunN := (functional_iff H hR hP E).2 hfun
  refine val_eq H hR hP (fun z hz => ?_) fun z => ?_
  · rcases (econs_spec H hfun d.1 z).1 hz with rfl | ⟨n, hn, y, hy, rfl⟩
    · exact inL_kpair_of H hR hP (inL_nat H hR hP (vempty_in_omega H)) d.2
    · exact inL_kpair_of H hR hP (inL_ord H hR hP (ord_succ H (ord_of_mem (ord_omega H) hn)))
        (inL_of_kpair_mem H hR hP E.2 hy).2
  · rw [show mem z.1 (econs (L_zfAxioms H hR hP) d E).1 ↔ _ from
      econs_spec (L_zfAxioms H hR hP) hfunN d z, econs_spec H hfun d.1 z.1,
      kpairN_eq H hR hP, val_vempty H hR hP]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨n, hn, y, hy, he⟩
      refine ⟨n.1, (mem_omegaN H hR hP n).1 hn, y.1, (kpairN_mem H hR hP _ _ _).1 hy, ?_⟩
      rw [(kpairN_eq H hR hP _ _ _).1 he, val_vsucc H hR hP]
    · rintro ⟨n, hn, y, hy, he⟩
      have hnL := inL_of_kpair_mem H hR hP E.2 hy
      refine ⟨⟨n, hnL.1⟩, (mem_omegaN H hR hP _).2 hn, ⟨y, hnL.2⟩,
        (kpairN_mem H hR hP _ _ _).2 hy, ?_⟩
      rwa [kpairN_eq H hR hP, val_vsucc H hR hP]

theorem val_vbit (p : Prop) : (vbit (L_zfAxioms H hR hP) p).1 = vbit H p := by
  by_cases hp : p
  · rw [vbit_pos _ hp, vbit_pos _ hp, val_natV H hR hP]
  · rw [vbit_neg _ hp, vbit_neg _ hp, val_natV H hR hP]

theorem val_satTriple (c e b : {x // InL H hP x}) :
    (satTriple (L_zfAxioms H hR hP) c e b).1 = satTriple H c.1 e.1 b.1 := by
  show (kpair (L_zfAxioms H hR hP) _ _).1 = kpair H _ _
  rw [val_kpair H hR hP, val_kpair H hR hP]

theorem inL_satTriple {c e b : V} (h : InL H hP (satTriple H c e b)) :
    InL H hP c ∧ InL H hP e ∧ InL H hP b :=
  ⟨(inL_kpair H hR hP h).1, inL_kpair H hR hP (inL_kpair H hR hP h).2⟩

theorem codeEq_iff (t : Nat) (c x : {x // InL H hP x}) :
    c = kpair (L_zfAxioms H hR hP) (natV (L_zfAxioms H hR hP) t) x ↔
      c.1 = kpair H (natV H t) x.1 := by
  rw [Subtype.ext_iff, val_kpair H hR hP, val_natV H hR hP]

theorem codeEq2_iff (t : Nat) (c x y : {x // InL H hP x}) :
    c = kpair (L_zfAxioms H hR hP) (natV (L_zfAxioms H hR hP) t)
      (kpair (L_zfAxioms H hR hP) x y) ↔ c.1 = kpair H (natV H t) (kpair H x.1 y.1) := by
  rw [Subtype.ext_iff, val_kpair H hR hP, val_natV H hR hP, val_kpair H hR hP]

theorem natEq_iff (b : {x // InL H hP x}) (k : Nat) :
    b = natV (L_zfAxioms H hR hP) k ↔ b.1 = natV H k := by
  rw [Subtype.ext_iff, val_natV H hR hP]

theorem tripleMem_iff (c e b S : {x // InL H hP x}) :
    memL H hP (satTriple (L_zfAxioms H hR hP) c e b) S ↔ mem (satTriple H c.1 e.1 b.1) S.1 := by
  show mem (satTriple (L_zfAxioms H hR hP) c e b).1 S.1 ↔ _
  rw [val_satTriple H hR hP]

section Clauses

variable {A R S c e b : {x // InL H hP x}} (he : IsEnvOn H A.1 e.1)
include he

omit he in
theorem atom_clause (t : Nat) (QN : {x // InL H hP x} → {x // InL H hP x} → Prop)
    (Q : V → V → Prop) (hQ : ∀ i j : {x // InL H hP x}, mem i.1 (omegaV H) → mem j.1 (omegaV H) →
      (QN i j ↔ Q i.1 j.1)) :
    (∃ i j : {x // InL H hP x}, memL H hP i (omegaV (L_zfAxioms H hR hP)) ∧
      memL H hP j (omegaV (L_zfAxioms H hR hP)) ∧
      c = kpair (L_zfAxioms H hR hP) (natV (L_zfAxioms H hR hP) t)
        (kpair (L_zfAxioms H hR hP) i j) ∧ b = vbit (L_zfAxioms H hR hP) (QN i j)) ↔
    (∃ i j, mem i (omegaV H) ∧ mem j (omegaV H) ∧ c.1 = kpair H (natV H t) (kpair H i j) ∧
      b.1 = vbit H (Q i j)) := by
  simp only [memL, val_omegaV H hR hP, Subtype.ext_iff, val_kpair H hR hP,
    val_natV H hR hP, val_vbit H hR hP]
  refine ⟨fun ⟨i, j, hi, hj, hc, hb⟩ => ⟨i.1, j.1, hi, hj, hc, ?_⟩,
    fun ⟨i, j, hi, hj, hc, hb⟩ => ?_⟩
  · simpa only [propext (hQ i j hi hj)] using hb
  · let i' : {x // InL H hP x} := ⟨i, inL_nat H hR hP hi⟩
    let j' : {x // InL H hP x} := ⟨j, inL_nat H hR hP hj⟩
    exact ⟨i', j', hi, hj, hc, by simpa only [propext (hQ i' j' hi hj)] using hb⟩

omit he in
theorem bin_clause (t : Nat) (op : Prop → Prop → Prop) :
    (∃ c1 c2 b1 b2 : {x // InL H hP x},
      c = kpair (L_zfAxioms H hR hP) (natV (L_zfAxioms H hR hP) t)
        (kpair (L_zfAxioms H hR hP) c1 c2) ∧
      memL H hP (satTriple (L_zfAxioms H hR hP) c1 e b1) S ∧
      memL H hP (satTriple (L_zfAxioms H hR hP) c2 e b2) S ∧
      b = vbit (L_zfAxioms H hR hP) (op (b1 = natV (L_zfAxioms H hR hP) 1)
        (b2 = natV (L_zfAxioms H hR hP) 1))) ↔
    (∃ c1 c2 b1 b2, c.1 = kpair H (natV H t) (kpair H c1 c2) ∧
      mem (satTriple H c1 e.1 b1) S.1 ∧ mem (satTriple H c2 e.1 b2) S.1 ∧
      b.1 = vbit H (op (b1 = natV H 1) (b2 = natV H 1))) := by
  simp only [Subtype.ext_iff, val_kpair H hR hP, val_natV H hR hP,
    val_vbit H hR hP, memL, val_satTriple H hR hP]
  refine ⟨fun ⟨c1, c2, b1, b2, h⟩ => ⟨c1.1, c2.1, b1.1, b2.1, h⟩,
    fun ⟨c1, c2, b1, b2, h⟩ => ?_⟩
  have h1 := inL_satTriple H hR hP (inL_trans H hR hP S.2 h.2.1)
  have h2 := inL_satTriple H hR hP (inL_trans H hR hP S.2 h.2.2.1)
  exact ⟨⟨c1, h1.1⟩, ⟨c2, h2.1⟩, ⟨b1, h1.2.2⟩, ⟨b2, h2.2.2⟩, h⟩

theorem quant_clause (t u v : Nat) :
    (∃ c1 : {x // InL H hP x}, c = kpair (L_zfAxioms H hR hP) (natV (L_zfAxioms H hR hP) t) c1 ∧
      ((b = natV (L_zfAxioms H hR hP) u ∧ ∀ d : {x // InL H hP x}, memL H hP d A →
          memL H hP (satTriple (L_zfAxioms H hR hP) c1 (econs (L_zfAxioms H hR hP) d e)
            (natV (L_zfAxioms H hR hP) u)) S) ∨
       (b = natV (L_zfAxioms H hR hP) v ∧ ∃ d : {x // InL H hP x}, memL H hP d A ∧
          memL H hP (satTriple (L_zfAxioms H hR hP) c1 (econs (L_zfAxioms H hR hP) d e)
            (natV (L_zfAxioms H hR hP) v)) S))) ↔
    (∃ c1, c.1 = kpair H (natV H t) c1 ∧
      ((b.1 = natV H u ∧ ∀ d, mem d A.1 → mem (satTriple H c1 (econs H d e.1) (natV H u)) S.1) ∨
       (b.1 = natV H v ∧ ∃ d, mem d A.1 ∧
          mem (satTriple H c1 (econs H d e.1) (natV H v)) S.1))) := by
  have hT : ∀ (c1 d : {x // InL H hP x}) (k : Nat),
      memL H hP (satTriple (L_zfAxioms H hR hP) c1 (econs (L_zfAxioms H hR hP) d e)
        (natV (L_zfAxioms H hR hP) k)) S ↔
      mem (satTriple H c1.1 (econs H d.1 e.1) (natV H k)) S.1 := fun c1 d k => by
    show mem (satTriple (L_zfAxioms H hR hP) _ _ _).1 S.1 ↔ _
    rw [val_satTriple H hR hP, val_econs H hR hP he.1.1, val_natV H hR hP]
  have hc1 : ∀ c1 : V, c.1 = kpair H (natV H t) c1 → InL H hP c1 := fun c1 h =>
    (inL_kpair H hR hP (h ▸ c.2)).2
  simp only [codeEq_iff H hR hP, natEq_iff H hR hP, hT]
  have hall (c1 : {x // InL H hP x}) := forall_memL_iff H hR hP A
    (fun d => mem (satTriple H c1.1 (econs H d e.1) (natV H u)) S.1)
  have hex (c1 : {x // InL H hP x}) := exists_memL_iff H hR hP A
    (fun d => mem (satTriple H c1.1 (econs H d e.1) (natV H v)) S.1)
  simp only [hall, hex]
  exact ⟨fun ⟨c1, hc, h⟩ => ⟨c1.1, hc, h⟩, fun ⟨c1, hc, h⟩ => ⟨⟨c1, hc1 c1 hc⟩, hc, h⟩⟩

/-- **The certificate step relation is absolute** (at a genuine environment). -/
theorem justified_iff :
    Justified (L_zfAxioms H hR hP) A R S c e b ↔ Justified H A.1 R.1 S.1 c.1 e.1 b.1 := by
  have hval : ∀ i : {x // InL H hP x}, mem i.1 (omegaV H) →
      (applyV (L_zfAxioms H hR hP) e i).1 = applyV H e.1 i.1 := fun i hi =>
    val_applyV_env H hR hP he hi
  unfold Justified
  refine or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_
    (or_congr ?_ ?_))))))
  · exact atom_clause H hR hP 0 _ _ fun i j hi hj => by
      show mem (kpair (L_zfAxioms H hR hP) _ _).1 R.1 ↔ _
      rw [val_kpair H hR hP, hval i hi, hval j hj]
  · exact atom_clause H hR hP 1 _ _ fun i j hi hj => by
      rw [Subtype.ext_iff, hval i hi, hval j hj]
  · rw [codeEq_iff H hR hP, val_vempty H hR hP, natEq_iff H hR hP]
  · exact bin_clause H hR hP 3 fun p q => p → q
  · exact bin_clause H hR hP 4 And
  · exact bin_clause H hR hP 5 Or
  · exact quant_clause H hR hP he 6 1 0
  · exact quant_clause H hR hP he 7 0 1

end Clauses

theorem satClosed_iff (A R S : {x // InL H hP x}) :
    SatClosed (L_zfAxioms H hR hP) A R S ↔ SatClosed H A.1 R.1 S.1 := by
  refine ⟨fun h c e b hm => ?_, fun h c e b hm => ?_⟩
  · obtain ⟨hc, he, hb⟩ := inL_satTriple H hR hP (inL_trans H hR hP S.2 hm)
    obtain ⟨hE, hJ⟩ := h ⟨c, hc⟩ ⟨e, he⟩ ⟨b, hb⟩ ((tripleMem_iff H hR hP _ _ _ _).2 hm)
    have hE' := (isEnvOn_iff H hR hP A ⟨e, he⟩).1 hE
    exact ⟨hE', (justified_iff H hR hP hE').1 hJ⟩
  · obtain ⟨hE, hJ⟩ := h c.1 e.1 b.1 ((tripleMem_iff H hR hP _ _ _ _).1 hm)
    exact ⟨(isEnvOn_iff H hR hP A e).2 hE, (justified_iff H hR hP hE).2 hJ⟩

theorem certifies_iff (A R S c e b : {x // InL H hP x}) :
    Certifies (L_zfAxioms H hR hP) A R S c e b ↔ Certifies H A.1 R.1 S.1 c.1 e.1 b.1 :=
  ⟨fun h => ⟨(satClosed_iff H hR hP A R S).1 h.closed, (tripleMem_iff H hR hP _ _ _ _).1 h.holds⟩,
   fun h => ⟨(satClosed_iff H hR hP A R S).2 h.closed, (tripleMem_iff H hR hP _ _ _ _).2 h.holds⟩⟩

theorem isSetStructure_iff (A R : {x // InL H hP x}) :
    IsSetStructure (L_zfAxioms H hR hP) A R ↔ IsSetStructure H A.1 R.1 := by
  refine ⟨fun h => ⟨?_, fun p hp => ?_⟩, fun h => ⟨?_, fun p hp => ?_⟩⟩
  · obtain ⟨d, hd⟩ := h.nonempty; exact ⟨d.1, hd⟩
  · obtain ⟨x, y, hx, hy, he⟩ := h.pairs ⟨p, inL_trans H hR hP R.2 hp⟩ hp
    exact ⟨x.1, y.1, hx, hy, (kpairN_eq H hR hP _ _ _).1 he⟩
  · obtain ⟨d, hd⟩ := h.nonempty; exact ⟨⟨d, inL_trans H hR hP A.2 hd⟩, hd⟩
  · obtain ⟨x, y, hx, hy, he⟩ := h.pairs p.1 hp
    exact ⟨⟨x, inL_trans H hR hP A.2 hx⟩, ⟨y, inL_trans H hR hP A.2 hy⟩, hx, hy,
      (kpairN_eq H hR hP _ _ _).2 he⟩

/-- **Satisfaction is absolute** for codes of both models and genuine environments. -/
theorem satIn_iff {A R c e : {x // InL H hP x}} (hS : IsSetStructure H A.1 R.1)
    (hcN : IsFormCodeSem (L_zfAxioms H hR hP) c) (hcM : IsFormCodeSem H c.1)
    (he : IsEnvOn H A.1 e.1) :
    SatIn (L_zfAxioms H hR hP) A R c e ↔ SatIn H A.1 R.1 c.1 e.1 := by
  constructor
  · rintro ⟨S, hS'⟩
    have := (certifies_iff H hR hP A R S c e _).1 hS'
    rw [val_natV H hR hP] at this
    exact ⟨S.1, this⟩
  · intro h
    obtain ⟨S, hcert⟩ := exists_certifies (L_zfAxioms H hR hP)
      ((isSetStructure_iff H hR hP A R).2 hS) hcN ((isEnvOn_iff H hR hP A e).2 he)
    have hM := (certifies_iff H hR hP A R S c e _).1 hcert
    rw [val_vbit H hR hP] at hM
    have hb := certifies_bit H hcM hM
    rw [vbit_pos H h] at hb
    exact (vbit_eq_one H _).1 hb

theorem memRel_iff (X R : {x // InL H hP x}) :
    MemRel (L_zfAxioms H hR hP) X R ↔ MemRel H X.1 R.1 := by
  refine ⟨fun h p => ⟨fun hp => ?_, ?_⟩, fun h p => ?_⟩
  · obtain ⟨a, b, ha, hb, hab, he⟩ := (h ⟨p, inL_trans H hR hP R.2 hp⟩).1 hp
    exact ⟨a.1, b.1, ha, hb, hab, (kpairN_eq H hR hP _ _ _).1 he⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    have haL := inL_trans H hR hP X.2 ha
    have hbL := inL_trans H hR hP X.2 hb
    exact (h ⟨_, inL_kpair_of H hR hP haL hbL⟩).2
      ⟨⟨a, haL⟩, ⟨b, hbL⟩, ha, hb, hab, (kpairN_eq H hR hP _ _ _).2 rfl⟩
  · rw [show memL H hP p R ↔ mem p.1 R.1 from Iff.rfl, h p.1]
    exact ⟨fun ⟨a, b, ha, hb, hab, he⟩ => ⟨⟨a, inL_trans H hR hP X.2 ha⟩,
      ⟨b, inL_trans H hR hP X.2 hb⟩, ha, hb, hab, (kpairN_eq H hR hP _ _ _).2 he⟩,
      fun ⟨a, b, ha, hb, hab, he⟩ => ⟨a.1, b.1, ha, hb, hab, (kpairN_eq H hR hP _ _ _).1 he⟩⟩

/-! ### Formula codes -/

/-- A code of `N`, read in `M` through the relativization of its formula. -/
theorem codeN_iff (c : V) (h : InL H hP c) :
    IsFormCodeSem (L_zfAxioms H hR hP) ⟨c, h⟩ ↔
      ConstructibleReflect.CSat mem (InL H hP) (fun _ => c) (fIsFormCodeF 0) := by
  rw [← fIsFormCodeF_spec (L_zfAxioms H hR hP) (fun _ => ⟨c, h⟩) 0]
  exact sat_sub (InL H hP) (fIsFormCodeF 0) (fun _ => ⟨c, h⟩)

/-- "`x` is a constructible code of `N`", as a named formula of `M`. -/
noncomputable def codeNF (x : Nat) : NForm :=
  .and (inLF H hP x) (ConstructibleReflect.relT (inLF H hP) (fun _ => x) (x + 1) (fIsFormCodeF 0))

omit hR in
theorem nsat_codeNF_aux (ρ : Nat → V) (x : Nat) :
    NSat mem ρ (codeNF H hP x) ↔ InL H hP (ρ x) ∧
      ConstructibleReflect.CSat mem (InL H hP) (fun _ => ρ x) (fIsFormCodeF 0) := by
  simp only [codeNF, NSat, nsat_inLF]
  rw [ConstructibleReflect.nsat_relT (InL H hP) (inLF H hP) (fun ρ x => nsat_inLF H hP ρ x)
    _ _ _ _ fun _ => by omega]

theorem nsat_codeNF (ρ : Nat → V) (x : Nat) :
    NSat mem ρ (codeNF H hP x) ↔ ∃ h : InL H hP (ρ x), IsFormCodeSem (L_zfAxioms H hR hP) ⟨ρ x, h⟩ := by
  rw [nsat_codeNF_aux]
  exact ⟨fun ⟨h, hc⟩ => ⟨h, (codeN_iff H hR hP _ h).2 hc⟩,
    fun ⟨h, hc⟩ => ⟨h, (codeN_iff H hR hP _ h).1 hc⟩⟩

theorem codeN_congr {x y : {x // InL H hP x}} (hxy : x.1 = y.1)
    (h : IsFormCodeSem (L_zfAxioms H hR hP) y) : IsFormCodeSem (L_zfAxioms H hR hP) x :=
  (Subtype.ext hxy : x = y) ▸ h

theorem inL_natV (k : Nat) : InL H hP (natV H k) := inL_nat H hR hP (natV_mem_omega H k)

/-- **Codes of `M` are constructible codes of `N`.** -/
theorem code_up :
    ∀ c, IsFormCodeSem H c → ∃ h : InL H hP c, IsFormCodeSem (L_zfAxioms H hR hP) ⟨c, h⟩ := by
  have hk : ∀ (t : Nat) (a b : V), InL H hP a → InL H hP b →
      InL H hP (kpair H (natV H t) (kpair H a b)) := fun t a b ha hb =>
    inL_kpair_of H hR hP (inL_natV H hR hP t) (inL_kpair_of H hR hP ha hb)
  have hv2 : ∀ (t : Nat) (a b : {x // InL H hP x}),
      (kpair (L_zfAxioms H hR hP) (natV (L_zfAxioms H hR hP) t)
        (kpair (L_zfAxioms H hR hP) a b)).1 = kpair H (natV H t) (kpair H a.1 b.1) :=
    fun t a b => by rw [val_kpair H hR hP, val_natV H hR hP, val_kpair H hR hP]
  have hv1 : ∀ (t : Nat) (a : {x // InL H hP x}),
      (kpair (L_zfAxioms H hR hP) (natV (L_zfAxioms H hR hP) t) a).1 = kpair H (natV H t) a.1 :=
    fun t a => by rw [val_kpair H hR hP, val_natV H hR hP]
  have atom : ∀ (t : Nat) (a b : V), mem a (omegaV H) → mem b (omegaV H) →
      (∀ a b : {x // InL H hP x}, memL H hP a (omegaV (L_zfAxioms H hR hP)) →
        memL H hP b (omegaV (L_zfAxioms H hR hP)) →
        IsFormCodeSem (L_zfAxioms H hR hP) (kpair (L_zfAxioms H hR hP)
          (natV (L_zfAxioms H hR hP) t) (kpair (L_zfAxioms H hR hP) a b))) →
      ∃ h : InL H hP (kpair H (natV H t) (kpair H a b)),
        IsFormCodeSem (L_zfAxioms H hR hP) ⟨_, h⟩ := by
    intro t a b ha hb hN
    let a' : {x // InL H hP x} := ⟨a, inL_nat H hR hP ha⟩
    let b' : {x // InL H hP x} := ⟨b, inL_nat H hR hP hb⟩
    exact ⟨hk t a b a'.2 b'.2, codeN_congr H hR hP (hv2 t a' b').symm
      (hN a' b' ((mem_omegaN H hR hP a').2 ha) ((mem_omegaN H hR hP b').2 hb))⟩
  have bin : ∀ (t : Nat) (a b : V), (∃ h : InL H hP a, IsFormCodeSem (L_zfAxioms H hR hP) ⟨a, h⟩) →
      (∃ h : InL H hP b, IsFormCodeSem (L_zfAxioms H hR hP) ⟨b, h⟩) →
      (∀ a b : {x // InL H hP x}, IsFormCodeSem (L_zfAxioms H hR hP) a →
        IsFormCodeSem (L_zfAxioms H hR hP) b →
        IsFormCodeSem (L_zfAxioms H hR hP) (kpair (L_zfAxioms H hR hP)
          (natV (L_zfAxioms H hR hP) t) (kpair (L_zfAxioms H hR hP) a b))) →
      ∃ h : InL H hP (kpair H (natV H t) (kpair H a b)),
        IsFormCodeSem (L_zfAxioms H hR hP) ⟨_, h⟩ := by
    rintro t a b ⟨ha, hca⟩ ⟨hb, hcb⟩ hN
    exact ⟨hk t a b ha hb, codeN_congr H hR hP (hv2 t ⟨a, ha⟩ ⟨b, hb⟩).symm (hN _ _ hca hcb)⟩
  have un : ∀ (t : Nat) (a : V), (∃ h : InL H hP a, IsFormCodeSem (L_zfAxioms H hR hP) ⟨a, h⟩) →
      (∀ a : {x // InL H hP x}, IsFormCodeSem (L_zfAxioms H hR hP) a →
        IsFormCodeSem (L_zfAxioms H hR hP) (kpair (L_zfAxioms H hR hP)
          (natV (L_zfAxioms H hR hP) t) a)) →
      ∃ h : InL H hP (kpair H (natV H t) a), IsFormCodeSem (L_zfAxioms H hR hP) ⟨_, h⟩ := by
    rintro t a ⟨ha, hca⟩ hN
    exact ⟨inL_kpair_of H hR hP (inL_natV H hR hP t) ha,
      codeN_congr H hR hP (hv1 t ⟨a, ha⟩).symm (hN _ hca)⟩
  refine isFormCodeSem_ind' H _ (toForm id (codeNF H hP 0)) (fun _ => vempty H)
    (fun y => by rw [sat_toForm, nsat_codeNF H hR hP]; rfl)
    (fun a b ha hb => atom 0 a b ha hb fun a b ha hb => isFormCodeSem_memAtom _ ha hb)
    (fun a b ha hb => atom 1 a b ha hb fun a b ha hb => isFormCodeSem_eqAtom _ ha hb)
    ⟨inL_kpair_of H hR hP (inL_natV H hR hP 2) (inL_natV H hR hP 0),
      codeN_congr H hR hP (by rw [val_kpair H hR hP, val_natV H hR hP, val_vempty H hR hP])
        (isFormCodeSem_bot (L_zfAxioms H hR hP))⟩
    (fun a b ha hb => bin 3 a b ha hb fun a b => isFormCodeSem_imp _)
    (fun a b ha hb => bin 4 a b ha hb fun a b => isFormCodeSem_and _)
    (fun a b ha hb => bin 5 a b ha hb fun a b => isFormCodeSem_or _)
    (fun a ha => un 6 a ha fun a => isFormCodeSem_all _)
    (fun a ha => un 7 a ha fun a => isFormCodeSem_ex _)

/-- `y` lies in some `V_γ` with `γ ∈ α`. -/
def RankBelow (α y : V) : Prop := ∃ γ T, mem γ α ∧ IsV H γ T ∧ mem y T

theorem rankBelow_step {α z y : V} (hα : Ord mem α) (hz : RankBelow H α z) (hy : mem y z) :
    RankBelow H α y := by
  obtain ⟨γ, T, hγ, hT, hzT⟩ := hz
  obtain ⟨δ, U, hδ, hU, hyU⟩ := (isV_spec H hR hP (ord_of_mem hα hγ) hT z).1 hzT
  exact ⟨δ, U, hα.1 γ hγ δ hδ, hU, hyU y hy⟩

theorem rankBelow_of_mem {α S z y : V} (hα : Ord mem α) (hS : IsV H α S) (hz : mem z S)
    (hy : mem y z) : RankBelow H α y := by
  obtain ⟨γ, T, hγ, hT, hzT⟩ := (isV_spec H hR hP hα hS z).1 hz
  exact ⟨γ, T, hγ, hT, hzT y hy⟩

/-- **Constructible codes of `N` are codes of `M`**, by a least-rank counterexample
and inversion of codes inside `N`. -/
theorem code_down (c : {x // InL H hP x}) (hc : IsFormCodeSem (L_zfAxioms H hR hP) c) :
    IsFormCodeSem H c.1 := by
  refine Classical.byContradiction fun hnc => ?_
  let Q : V → Prop := fun α => ∃ S x, IsV H α S ∧ mem x S ∧
    (∃ h : InL H hP x, IsFormCodeSem (L_zfAxioms H hR hP) ⟨x, h⟩) ∧ ¬ IsFormCodeSem H x
  obtain ⟨α0, S0, hα0, hS0, hcS0⟩ := ZFRank.ranked H hR hP c.1
  obtain ⟨m, hm, hQm, hmin⟩ := least_ord H hR Q
    (.ex 1 (.ex 2 (.and (isVF 0 1) (.and (.mem 2 1) (.and (codeNF H hP 2)
      (.neg (ConstructibleDef.isCodeF 2)))))))
    (fun _ => vempty H)
    (fun α => by
      simp only [NSat, nsat_isVF H, nsat_codeNF H hR hP, ConstructibleDef.nsat_isCodeF H, nsat_neg]
      simp (disch := omega) only [upd_same, upd_other]
      exact Iff.rfl)
    hα0 ⟨S0, c.1, hS0, hcS0, ⟨c.2, hc⟩, hnc⟩
  obtain ⟨S, x, hS, hxS, ⟨hx, hcx⟩, hnx⟩ := hQm
  -- members of lower rank that are codes of `N` are codes of `M`
  have below : ∀ y : {x // InL H hP x}, RankBelow H m y.1 →
      IsFormCodeSem (L_zfAxioms H hR hP) y → IsFormCodeSem H y.1 := by
    intro y ⟨γ, T, hγ, hT, hyT⟩ hcy
    refine Classical.byContradiction fun hny => ?_
    rcases hmin γ (ord_of_mem hm hγ) ⟨T, y.1, hT, hyT, ⟨y.2, hcy⟩, hny⟩ with rfl | h
    · exact mem_irrefl H hR _ hγ
    · exact mem_irrefl H hR _ (hm.1 γ hγ m h)
  have r1 : ∀ (t : V) (p : V), x = kpair H t p → RankBelow H m p := fun t p he =>
    rankBelow_step H hR hP hm (rankBelow_of_mem H hR hP hm hS hxS
      (he ▸ (kpair_mem H t p _).2 (Or.inr rfl))) ((vpair_spec H t p p).2 (Or.inr rfl))
  have r2 : ∀ (t a b : V), x = kpair H t (kpair H a b) → RankBelow H m a ∧ RankBelow H m b :=
    fun t a b he => by
      have hp := r1 t _ he
      refine ⟨rankBelow_step H hR hP hm (rankBelow_step H hR hP hm hp
        ((kpair_mem H a b _).2 (Or.inl rfl))) ((vsingle_spec H a a).2 rfl), ?_⟩
      exact rankBelow_step H hR hP hm (rankBelow_step H hR hP hm hp
        ((kpair_mem H a b _).2 (Or.inr rfl))) ((vpair_spec H a b b).2 (Or.inr rfl))
  apply hnx
  rcases code_shape (L_zfAxioms H hR hP) ⟨x, hx⟩ hcx with
    ⟨i, j, hi, hj, h | h⟩ | h | ⟨a, b, ha, hb, h | h | h⟩ | ⟨a, ha, h | h⟩
  · rw [show x = _ from (codeEq2_iff H hR hP 0 _ i j).1 h]
    exact isFormCodeSem_memAtom H ((mem_omegaN H hR hP i).1 hi) ((mem_omegaN H hR hP j).1 hj)
  · rw [show x = _ from (codeEq2_iff H hR hP 1 _ i j).1 h]
    exact isFormCodeSem_eqAtom H ((mem_omegaN H hR hP i).1 hi) ((mem_omegaN H hR hP j).1 hj)
  · rw [show x = _ from (codeEq_iff H hR hP 2 _ _).1 h, val_vempty H hR hP]
    exact isFormCodeSem_bot H
  all_goals first
    | (have e : x = _ := (codeEq2_iff H hR hP _ _ a b).1 h
       obtain ⟨ra, rb⟩ := r2 _ _ _ e
       rw [e]
       first
         | exact isFormCodeSem_imp H (below a ra ha) (below b rb hb)
         | exact isFormCodeSem_and H (below a ra ha) (below b rb hb)
         | exact isFormCodeSem_or H (below a ra ha) (below b rb hb))
    | (have e : x = _ := (codeEq_iff H hR hP _ _ a).1 h
       have ra := r1 _ _ e
       rw [e]
       first
         | exact isFormCodeSem_all H (below a ra ha)
         | exact isFormCodeSem_ex H (below a ra ha))

/-! ### Constructible environments with prescribed finite parts -/

/-- `t` is the restriction of the graph `e` to the indices in `k`. -/
def IsRes (e k t : V) : Prop := ∀ p, mem p t ↔ mem p e ∧ ∃ i y, mem i k ∧ p = kpair H i y

omit hR hP in
theorem nsat_isRes (ρ : Nat → V) :
    NSat mem ρ (.all 3 ((NForm.mem 3 2).iff (.and (.mem 3 1) (.ex 4 (.ex 5
      (.and (.mem 4 0) (kpairF 3 4 5))))))) ↔ IsRes H (ρ 1) (ρ 0) (ρ 2) := by
  simp only [NSat, nsat_iff, nsat_kpairF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

/-- Finite restrictions of an environment with constructible values are constructible. -/
theorem res_inL {A e : V} (hA : InL H hP A) (he : IsEnvOn H A e) :
    ∀ k, mem k (omegaV H) → ∃ t, InL H hP t ∧ IsRes H e k t := by
  let φ : NForm := .ex 2 (.and (inLF H hP 2) (.all 3 ((NForm.mem 3 2).iff (.and (.mem 3 1)
    (.ex 4 (.ex 5 (.and (.mem 4 0) (kpairF 3 4 5))))))))
  have hφ : ∀ k, Sat mem (scons k (fun _ => e)) (toForm id φ) ↔ ∃ t, InL H hP t ∧ IsRes H e k t := by
    intro k
    rw [sat_toForm]
    simp only [φ, NSat, nsat_inLF]
    refine exists_congr fun t => and_congr_right fun _ => ?_
    have := nsat_isRes H (upd (fun i => scons k (fun _ => e) (id i)) 2 t)
    simp only [NSat, nsat_iff] at this ⊢
    rw [this]
    simp (disch := omega) only [upd_same, upd_other]
    rfl
  intro k hk
  refine (hφ k).1 (omega_ind H (toForm id φ) (fun _ => e) ((hφ _).2 ?_) (fun m hm ih => ?_) k hk)
  · refine ⟨vempty H, inL_nat H hR hP (vempty_in_omega H), fun p => ?_⟩
    exact iff_of_false (vempty_spec H p) fun ⟨_, i, _, hi, _⟩ => vempty_spec H i hi
  · obtain ⟨t, htL, ht⟩ := (hφ m).1 ih
    refine (hφ _).2 ⟨vcup H t (vsingle H (kpair H m (applyV H e m))), ?_, fun p => ?_⟩
    · have hk : InL H hP (kpair H m (applyV H e m)) :=
        inL_kpair_of H hR hP (inL_nat H hR hP hm) (inL_trans H hR hP hA (isEnvOn_apply H he hm))
      exact inL_union H hR hP (inL_pair H hR hP htL (inL_pair H hR hP hk hk))
    · rw [vcup_spec H t _ p, vsingle_spec H _ p, ht p]
      constructor
      · rintro (⟨hpe, i, y, hi, rfl⟩ | rfl)
        · exact ⟨hpe, i, y, (vsucc_spec H m i).2 (Or.inl hi), rfl⟩
        · exact ⟨applyV_mem H (he.1.2.1 m hm), m, _, vsucc_self H m, rfl⟩
      · rintro ⟨hpe, i, y, hi, rfl⟩
        rcases (vsucc_spec H m i).1 hi with hi | rfl
        · exact Or.inl ⟨hpe, i, y, hi, rfl⟩
        · exact Or.inr (by rw [applyV_eq H he.1.1 hpe])

omit H hR hP in
/-- Pairs of elements of `U` lie in `P(P(U))`, in any model of the bundle. -/
theorem kpair_mem_pp {W : Type u} {memW : W → W → Prop} (HW : ZFAxioms memW) {U P1 P2 a b : W}
    (h1 : ∀ x, memW x P1 ↔ Sub memW x U) (h2 : ∀ x, memW x P2 ↔ Sub memW x P1)
    (ha : memW a U) (hb : memW b U) : memW (kpair HW a b) P2 := by
  refine (h2 _).2 fun q hq => (h1 q).2 ?_
  rcases (kpair_mem HW a b q).1 hq with rfl | rfl
  · intro z hz; rwa [(vsingle_spec HW a z).1 hz]
  · intro z hz; rcases (vpair_spec HW a b z).1 hz with rfl | rfl <;> assumption

/-- **Constructible environments with a prescribed finite part.** -/
theorem env_in_L (X : {x // InL H hP x}) {e n : V} (he : IsEnvOn H X.1 e)
    (hn : mem n (omegaV H)) :
    ∃ e' : {x // InL H hP x}, IsEnvOn H X.1 e'.1 ∧ ∀ i, mem i n → applyV H e i = applyV H e'.1 i := by
  obtain ⟨t, htL, ht⟩ := res_inL H hR hP X.2 he n hn
  have hd0 : mem (applyV H e (vempty H)) X.1 := isEnvOn_apply H he (vempty_in_omega H)
  let HN := L_zfAxioms H hR hP
  let ωN : {x // InL H hP x} := ⟨omegaV H, inL_omega H hR hP⟩
  let tN : {x // InL H hP x} := ⟨t, htL⟩
  let nN : {x // InL H hP x} := ⟨n, inL_nat H hR hP hn⟩
  let dN : {x // InL H hP x} := ⟨_, inL_trans H hR hP X.2 hd0⟩
  obtain ⟨P1, hP1⟩ := L_power H hR hP (vcup HN ωN X)
  obtain ⟨P2, hP2⟩ := L_power H hR hP P1
  let Q : {x // InL H hP x} → Prop := fun p => ∃ i y : {x // InL H hP x}, memL H hP i ωN ∧
    memL H hP y X ∧ p = kpair HN i y ∧ ((memL H hP i nN ∧ memL H hP p tN) ∨
      (¬ memL H hP i nN ∧ y = dN))
  let ρ : Nat → {x // InL H hP x} := fun i =>
    if i = 1 then ωN else if i = 2 then X else if i = 3 then nN else if i = 4 then tN else dN
  obtain ⟨s, hs⟩ := sep_of HN Q
    (.ex 6 (.ex 7 (.and (.mem 6 1) (.and (.mem 7 2) (.and (kpairF 0 6 7)
      (.or (.and (.mem 6 3) (.mem 0 4)) (.and (.neg (.mem 6 3)) (.eq 7 5))))))))
    ρ (fun p => by
      simp only [NSat, nsat_kpairF HN, nsat_neg]
      simp (disch := omega) only [upd_same, upd_other]
      rfl) P2
  -- membership in `s`, read in `M`
  have hsM : ∀ p, mem p s.1 ↔ ∃ i y, mem i (omegaV H) ∧ mem y X.1 ∧ p = kpair H i y ∧
      ((mem i n ∧ mem p t) ∨ (¬ mem i n ∧ y = applyV H e (vempty H))) := by
    refine fun p => ⟨fun hp => ?_, ?_⟩
    · obtain ⟨-, i, y, hi, hy, he', hc⟩ := (hs ⟨p, inL_trans H hR hP s.2 hp⟩).1 hp
      exact ⟨i.1, y.1, hi, hy, (kpairN_eq H hR hP _ _ _).1 he',
        hc.imp (fun ⟨h1, h2⟩ => ⟨h1, h2⟩) fun ⟨h1, h2⟩ => ⟨h1, congrArg Subtype.val h2⟩⟩
    · rintro ⟨i, y, hi, hy, rfl, hc⟩
      have hiL := inL_nat H hR hP hi
      have hyL := inL_trans H hR hP X.2 hy
      let iN : {x // InL H hP x} := ⟨i, hiL⟩
      let yN : {x // InL H hP x} := ⟨y, hyL⟩
      have hU : ∀ z : {x // InL H hP x}, memL H hP z ωN ∨ memL H hP z X →
          memL H hP z (vcup HN ωN X) := fun z hz => (vcup_spec HN ωN X z).2 hz
      have hmem := kpair_mem_pp HN hP1 hP2 (hU iN (Or.inl hi)) (hU yN (Or.inr hy))
      have hpq : (kpair HN iN yN).1 = kpair H i y := val_kpair H hR hP iN yN
      have := (hs (kpair HN iN yN)).2 ⟨hmem, iN, yN, hi, hy, rfl, hc.imp
        (fun ⟨h1, h2⟩ => ⟨h1, show mem (kpair HN iN yN).1 t by rwa [hpq]⟩)
        fun ⟨h1, h2⟩ => ⟨h1, Subtype.ext h2⟩⟩
      exact hpq ▸ this
  have hte : ∀ p, mem p t → mem p e := fun p hp => ((ht p).1 hp).1
  have hfun : ∀ a b b', mem (kpair H a b) s.1 → mem (kpair H a b') s.1 → b = b' := by
    intro a b b' h1 h2
    obtain ⟨i, y, -, -, e1, c1⟩ := (hsM _).1 h1
    obtain ⟨i', y', -, -, e2, c2⟩ := (hsM _).1 h2
    obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e1
    obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e2
    rcases c1 with ⟨hi, ht1⟩ | ⟨hi, rfl⟩ <;> rcases c2 with ⟨hi', ht2⟩ | ⟨hi', rfl⟩
    · exact he.1.1 _ _ _ (hte _ ht1) (hte _ ht2)
    · exact absurd hi hi'
    · exact absurd hi' hi
    · rfl
  have hin : ∀ i, mem i (omegaV H) → mem i n → mem (kpair H i (applyV H e i)) s.1 :=
    fun i hi hin => (hsM _).2 ⟨i, _, hi, isEnvOn_apply H he hi, rfl,
      Or.inl ⟨hin, (ht _).2 ⟨applyV_mem H (he.1.2.1 i hi), i, _, hin, rfl⟩⟩⟩
  refine ⟨s, ⟨⟨hfun, fun i hi => ?_, fun p hp => ?_⟩, fun i y hy => ?_⟩, fun i hi => ?_⟩
  · by_cases hin' : mem i n
    · exact ⟨_, hin i hi hin'⟩
    · exact ⟨_, (hsM _).2 ⟨i, _, hi, hd0, rfl, Or.inr ⟨hin', rfl⟩⟩⟩
  · obtain ⟨i, y, hi, -, rfl, -⟩ := (hsM p).1 hp
    exact ⟨i, y, hi, rfl⟩
  · obtain ⟨i', y', -, hy', e1, -⟩ := (hsM _).1 hy
    rwa [(kpair_inj H _ _ _ _ e1).2]
  · exact (applyV_eq H hfun (hin i (ConstructibleZF.omega_trans H n hn i hi) hi)).symm

/-! ### Definability and `Def` -/

theorem def_down (X S : {x // InL H hP x}) (h : DefinableIn (L_zfAxioms H hR hP) X S) :
    DefinableIn H X.1 S.1 := by
  obtain ⟨R, c, e, hRel, hc, he, hspec⟩ := h
  have he' := (isEnvOn_iff H hR hP X e).1 he
  have hRel' := (memRel_iff H hR hP X R).1 hRel
  have hS := setStructure_of_memRel H hRel' ⟨_, isEnvOn_apply H he' (vempty_in_omega H)⟩
  have hcM := code_down H hR hP c hc
  have key : ∀ z : {x // InL H hP x}, mem z.1 X.1 →
      (SatIn (L_zfAxioms H hR hP) X R c (econs (L_zfAxioms H hR hP) z e) ↔
        SatIn H X.1 R.1 c.1 (econs H z.1 e.1)) := by
    intro z hz
    rw [satIn_iff H hR hP hS hc hcM (by rw [val_econs H hR hP he'.1.1]; exact econs_isEnvOn H he' hz),
      val_econs H hR hP he'.1.1]
  refine ⟨R.1, c.1, e.1, hRel', hcM, he', fun z => ⟨fun hz => ?_, fun ⟨hz, hsat⟩ => ?_⟩⟩
  · obtain ⟨hzX, hsat⟩ := (hspec ⟨z, inL_trans H hR hP S.2 hz⟩).1 hz
    exact ⟨hzX, (key ⟨z, _⟩ hzX).1 hsat⟩
  · exact (hspec ⟨z, inL_trans H hR hP X.2 hz⟩).2 ⟨hz, (key ⟨z, _⟩ hz).2 hsat⟩

/-- **Definable subsets of a constructible set are constructible and `N`-definable.** -/
theorem def_up (X : {x // InL H hP x}) {S : V} (hd : DefinableIn H X.1 S) :
    ∃ S' : {x // InL H hP x}, S'.1 = S ∧ DefinableIn (L_zfAxioms H hR hP) X S' := by
  obtain ⟨R, c, e, hRel, hc, he, hspec⟩ := hd
  have hne : ∃ d, mem d X.1 := ⟨_, isEnvOn_apply H he (vempty_in_omega H)⟩
  obtain ⟨RN, hRN⟩ := memRel_exists (L_zfAxioms H hR hP) (L_power H hR hP) X
  have hRN' := (memRel_iff H hR hP X RN).1 hRN
  have eR : RN.1 = R := H.ext _ _ fun p => by rw [hRN' p, hRel p]
  have hS := setStructure_of_memRel H hRel hne
  obtain ⟨n, hn, hsup⟩ := SatSupport.sat_support H hS c hc
  obtain ⟨hcL, hcN⟩ := code_up H hR hP c hc
  obtain ⟨e', he', hag⟩ := env_in_L H hR hP X he hn
  let cN : {x // InL H hP x} := ⟨c, hcL⟩
  have he'N := (isEnvOn_iff H hR hP X e').2 he'
  let ρ : Nat → {x // InL H hP x} := fun i =>
    if i = 1 then X else if i = 2 then RN else if i = 3 then e' else cN
  obtain ⟨S', hS'⟩ := sep_of (L_zfAxioms H hR hP)
    (fun y => SatIn (L_zfAxioms H hR hP) X RN cN (econs (L_zfAxioms H hR hP) y e'))
    (.ex 5 (.and (econsAtomF 5 0 3) (satInF 1 2 4 5))) ρ
    (fun y => by
      simp only [NSat, nsat_satInF (L_zfAxioms H hR hP)]
      simp (disch := omega) only [upd_same, upd_other]
      constructor
      · rintro ⟨E, hE, hsat⟩
        rw [nsat_econsAtomF (L_zfAxioms H hR hP) _ _ _ _ (by
          simp (disch := omega) only [upd_other]; exact he'N.1.1)] at hE
        simp (disch := omega) only [upd_same, upd_other] at hE
        rwa [hE] at hsat
      · intro hsat
        refine ⟨_, ?_, hsat⟩
        rw [nsat_econsAtomF (L_zfAxioms H hR hP) _ _ _ _ (by
          simp (disch := omega) only [upd_other]; exact he'N.1.1)]
        simp (disch := omega) only [upd_same, upd_other]
        rfl) X
  have hcode : IsFormCodeSem (L_zfAxioms H hR hP) cN := hcN
  have key : ∀ z : {x // InL H hP x}, mem z.1 X.1 →
      (SatIn (L_zfAxioms H hR hP) X RN cN (econs (L_zfAxioms H hR hP) z e') ↔
        SatIn H X.1 R c (econs H z.1 e)) := by
    intro z hz
    have hEe : IsEnvOn H X.1 (econs H z.1 e'.1) := econs_isEnvOn H he' hz
    rw [satIn_iff H hR hP (eR ▸ hS) hcode hc (by rw [val_econs H hR hP he'.1.1]; exact hEe),
      val_econs H hR hP he'.1.1, eR]
    exact hsup _ _ hEe (econs_isEnvOn H he hz) (SatSupport.agreeP_econs H hn he' he hz
      ((SatSupport.agreeP_iff H hn he' he).2 fun i hi => (hag i hi).symm))
  refine ⟨S', H.ext _ _ fun z => ⟨fun hz => ?_, fun hz => ?_⟩, ⟨RN, cN, e', hRN, hcode, he'N, hS'⟩⟩
  · obtain ⟨hzX, hsat⟩ := (hS' ⟨z, inL_trans H hR hP S'.2 hz⟩).1 hz
    exact (hspec z).2 ⟨hzX, (key _ hzX).1 hsat⟩
  · obtain ⟨hzX, hsat⟩ := (hspec z).1 hz
    exact (hS' ⟨z, inL_trans H hR hP X.2 hzX⟩).2 ⟨hzX, (key ⟨z, _⟩ hzX).2 hsat⟩

/-- **`Def` is absolute**: the `N`-version of `Gdef X` is `Gdef X`. -/
theorem gdef_eq (X : {x // InL H hP x}) :
    (Gdef (L_zfAxioms H hR hP) (L_power H hR hP) X).1 = Gdef H hP X.1 := by
  refine val_eq H hR hP (fun S hS => ?_) fun S => ?_
  · rcases ((gdef_spec H hP X.1 S).1 hS).2 with hemp | hdef
    · have : S = vempty H := H.ext _ _ fun z =>
        ⟨fun hz => absurd hz (hemp z), fun hz => absurd hz (vempty_spec H z)⟩
      rw [this]; exact inL_nat H hR hP (vempty_in_omega H)
    · obtain ⟨S', rfl, -⟩ := def_up H hR hP X hdef
      exact S'.2
  · rw [show mem S.1 (Gdef (L_zfAxioms H hR hP) (L_power H hR hP) X).1 ↔ _ from
      gdef_spec (L_zfAxioms H hR hP) (L_power H hR hP) X S, gdef_spec H hP]
    refine and_congr (forall_memL_iff H hR hP S (fun z => mem z X.1))
      (or_congr (forall_memL_iff H hR hP S (fun _ => False)) ⟨def_down H hR hP X S, fun h => ?_⟩)
    obtain ⟨S', hS', hdef⟩ := def_up H hR hP X h
    rwa [show S' = S from Subtype.ext hS'] at hdef

/-! ### The hierarchy, and `V = L` in `L` -/

theorem approx_down (f d : {x // InL H hP x})
    (h : TransRec.Approx (L_zfAxioms H hR hP) (Gdef (L_zfAxioms H hR hP) (L_power H hR hP)) f d) :
    TransRec.Approx H (Gdef H hP) f.1 d.1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun p hp => ?_, fun b hb => ?_, fun b S S' hS hS' => ?_, fun b S hbS z => ?_⟩
  · obtain ⟨b, S, hb, he⟩ := h1 ⟨p, inL_trans H hR hP f.2 hp⟩ hp
    exact ⟨b.1, S.1, hb, (kpairN_eq H hR hP _ _ _).1 he⟩
  · obtain ⟨S, hS⟩ := h2 ⟨b, inL_trans H hR hP d.2 hb⟩ hb
    exact ⟨S.1, (kpairN_mem H hR hP _ _ _).1 hS⟩
  · have hL := inL_of_kpair_mem H hR hP f.2 hS
    have hL' := inL_of_kpair_mem H hR hP f.2 hS'
    exact congrArg Subtype.val (h3 ⟨b, hL.1⟩ ⟨S, hL.2⟩ ⟨S', hL'.2⟩
      ((kpairN_mem H hR hP _ _ _).2 hS) ((kpairN_mem H hR hP _ _ _).2 hS'))
  · obtain ⟨hbL, hSL⟩ := inL_of_kpair_mem H hR hP f.2 hbS
    have h4' := h4 ⟨b, hbL⟩ ⟨S, hSL⟩ ((kpairN_mem H hR hP _ _ _).2 hbS)
    refine ⟨fun hz => ?_, fun ⟨c, T, hc, hcT, hzT⟩ => ?_⟩
    · obtain ⟨c, T, hc, hcT, hzT⟩ := (h4' ⟨z, inL_trans H hR hP hSL hz⟩).1 hz
      refine ⟨c.1, T.1, hc, (kpairN_mem H hR hP _ _ _).1 hcT, ?_⟩
      have : mem z (Gdef (L_zfAxioms H hR hP) (L_power H hR hP) T).1 := hzT
      rwa [gdef_eq H hR hP] at this
    · obtain ⟨hcL, hTL⟩ := inL_of_kpair_mem H hR hP f.2 hcT
      have hz' : mem z (Gdef (L_zfAxioms H hR hP) (L_power H hR hP) ⟨T, hTL⟩).1 := by
        rwa [gdef_eq H hR hP]
      have hzL := inL_trans H hR hP (Gdef (L_zfAxioms H hR hP) (L_power H hR hP) ⟨T, hTL⟩).2 hz'
      exact (h4' ⟨z, hzL⟩).2 ⟨⟨c, hcL⟩, ⟨T, hTL⟩, hc, (kpairN_mem H hR hP _ _ _).2 hcT, hz'⟩

theorem isL_down (a S : {x // InL H hP x})
    (h : IsL (L_zfAxioms H hR hP) (L_power H hR hP) a S) : IsL H hP a.1 S.1 := by
  obtain ⟨f, hf, haS⟩ := h
  refine ⟨f.1, ?_, (kpairN_mem H hR hP _ _ _).1 haS⟩
  have := approx_down H hR hP f _ hf
  rwa [val_vsucc H hR hP] at this

theorem ord_iff (a : {x // InL H hP x}) : Ord (memL H hP) a ↔ Ord mem a.1 := by
  have htr : ∀ t : {x // InL H hP x}, Trans (memL H hP) t ↔ Trans mem t.1 := fun t =>
    ⟨fun h x hx z hz => h ⟨x, inL_trans H hR hP t.2 hx⟩ hx
        ⟨z, inL_trans H hR hP (inL_trans H hR hP t.2 hx) hz⟩ hz,
     fun h x hx z hz => h x.1 hx z.1 hz⟩
  unfold InternalOrd.Ord
  rw [htr a]
  exact and_congr_right fun _ =>
    ⟨fun h x hx => (htr ⟨x, inL_trans H hR hP a.2 hx⟩).1 (h _ hx),
     fun h x hx => (htr x).2 (h x.1 hx)⟩

/-- **`V = L` holds in `L`**: every constructible set is constructible in the
sense of the constructible model. -/
theorem vEqL (x : {x // InL H hP x}) : InL (L_zfAxioms H hR hP) (L_power H hR hP) x := by
  obtain ⟨a, S, ha, hS, hxS⟩ := x.2
  let aN : {x // InL H hP x} := ⟨a, inL_ord H hR hP ha⟩
  have haN : Ord (memL H hP) aN := (ord_iff H hR hP aN).2 ha
  obtain ⟨S', hS'⟩ := isL_exists (L_zfAxioms H hR hP) (L_regular H hR hP) (L_power H hR hP) haN
  have e : S'.1 = S := isL_unique H hR hP ha (isL_down H hR hP aN S' hS') hS
  exact ⟨aN, S', haN, hS', show mem x.1 S'.1 by rwa [e]⟩

end Ops

end SetTheory.BusyBeaver.ZFC.ConstructibleAbs
