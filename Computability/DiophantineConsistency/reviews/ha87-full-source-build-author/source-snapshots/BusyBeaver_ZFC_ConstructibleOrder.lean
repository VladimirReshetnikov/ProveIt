import BusyBeaver.ZFC.TupleOrder
import BoundedZFCConsistency.Choice

/-!
The canonical well-order of the constructible hierarchy, and Choice under
`V = L`, inside any model of ZF.

A stage `W` of the recursion well-orders a set `F` (its field). The next
stage appends the new elements `Def(F) \ F`, each compared by its least
**key** `⟨c, ⟨n, t⟩⟩`: an internal formula code `c` (ordered by
`CodeOrder`), a length `n ∈ ω`, and a tuple `t` of parameters from `F`
(ordered by `TupleOrder.LexN`), such that `c` with any environment extending
`t` defines the element over `F`. Every element of `Def(F)` has a key by the
uniform finite support of satisfaction (`SatSupport`), and a key determines
its element. By `OrderRec` every stage is a well-order; its field is `L_a`.
In a model of `V = L` every set lies in some `L_a`, and least elements give a
selector for every family of pairwise disjoint nonempty sets
(`choice_of_VL`).
-/

namespace SetTheory.BusyBeaver.ZFC.ConstructibleOrder

open NamedZF NForm InternalOrd InternalRank TransRec ConstructibleDef Constructible
  InternalWO OrderRec TupleOrder LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

section Defs

variable (H : ZFAxioms mem)

/-- `c` with any environment extending the tuple `t` of length `n` defines `x` over `F`. -/
def Defines (F c n t x : V) : Prop :=
  ∀ R e, MemRel H F R → IsEnvOn H F e → SatSupport.AgreeP H n e t →
    ∀ y, mem y x ↔ mem y F ∧ SatIn H F R c (econs H y e)

/-- Keys: a code in the field of `CW`, then a natural, then a tuple. -/
def KeyP (W CW k : V) : Prop :=
  LexP H (Fld H CW) (fun _ => LexP H (fun n => mem n (omegaV H)) (IsTup H W)) k

/-- The order of keys. -/
def KeyR (W CW k k' : V) : Prop :=
  LexR H (Le H CW) (fun _ => LexR H (fun m n => mem m n ∨ m = n) (LexN H W)) k k'

/-- `k` is a key of `x`. -/
def IsKey (W F CW x k : V) : Prop :=
  KeyP H W CW k ∧ ∃ c n t, k = kpair H c (kpair H n t) ∧ IsFormCodeSem H c ∧ Defines H F c n t x

/-- The order of new elements: by least keys. -/
def NewLe (W F CW x y : V) : Prop :=
  ∃ k, IsKey H W F CW x k ∧ ∀ k', IsKey H W F CW y k' → KeyR H W CW k k'

/-! ### Named formulas -/

def definesF (f c n t x : Nat) : NForm :=
  let m := f + c + n + t + x + 1
  .all m (.all (m + 1) (.imp (memRelF m f) (.imp (envOnF (m + 1) f)
    (.imp (SatSupport.agreeF n (m + 1) t) (.all (m + 2) ((NForm.mem (m + 2) x).iff
      (.and (.mem (m + 2) f) (.ex (m + 3) (.and (econsAtomF (m + 3) (m + 2) (m + 1))
        (satInF f m c (m + 3)))))))))))

theorem nsat_definesF (ρ : Nat → V) (f c n t x : Nat) :
    NSat mem ρ (definesF f c n t x) ↔ Defines H (ρ f) (ρ c) (ρ n) (ρ t) (ρ x) := by
  simp only [definesF, NSat, nsat_iff, nsat_memRelF H, nsat_envOnF H, SatSupport.nsat_agreeF H,
    nsat_satInF H]
  simp (disch := omega) only [upd_same, upd_other]
  refine forall_congr' fun R => forall_congr' fun e => imp_congr_right fun _ =>
    imp_congr_right fun hE => imp_congr_right fun _ => forall_congr' fun y =>
      iff_congr Iff.rfl (and_congr_right fun _ => ?_)
  let m := f + c + n + t + x + 1
  have key : ∀ e', NSat mem (upd (upd (upd (upd ρ m R) (m + 1) e) (m + 2) y) (m + 3) e')
      (econsAtomF (m + 3) (m + 2) (m + 1)) ↔ e' = econs H y e := by
    intro e'
    rw [nsat_econsAtomF H _ _ _ _ (by simp (disch := omega) only [upd_same, upd_other]; exact hE.1.1)]
    simp (disch := omega) only [upd_same, upd_other]
  constructor
  · rintro ⟨e', he', hs⟩; rwa [(key e').1 he'] at hs
  · intro hs; exact ⟨_, (key _).2 rfl, hs⟩

def keyPF (w cw k : Nat) : NForm :=
  let m := w + cw + k + 1
  .ex m (.ex (m + 1) (.and (kpairF k m (m + 1)) (.and (pmemF cw m m)
    (.ex (m + 2) (.ex (m + 3) (.and (kpairF (m + 1) (m + 2) (m + 3))
      (.and (SatSupport.inOmegaF (m + 2)) (isTupF w (m + 2) (m + 3)))))))))

theorem nsat_keyPF (ρ : Nat → V) (w cw k : Nat) :
    NSat mem ρ (keyPF w cw k) ↔ KeyP H (ρ w) (ρ cw) (ρ k) := by
  simp only [keyPF, NSat, nsat_kpairF H, nsat_pmemF H, SatSupport.nsat_inOmegaF H, nsat_isTupF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

def keyRF (w cw k k' : Nat) : NForm :=
  let m := w + cw + k + k' + 1
  .ex m (.ex (m + 1) (.ex (m + 2) (.ex (m + 3) (.and (kpairF k m (m + 1))
    (.and (kpairF k' (m + 2) (m + 3)) (.or (.and (pmemF cw m (m + 2)) (.neg (.eq m (m + 2))))
      (.and (.eq m (m + 2)) (.ex (m + 4) (.ex (m + 5) (.ex (m + 6) (.ex (m + 7)
        (.and (kpairF (m + 1) (m + 4) (m + 5)) (.and (kpairF (m + 3) (m + 6) (m + 7))
          (.or (.and (.or (.mem (m + 4) (m + 6)) (.eq (m + 4) (m + 6))) (.neg (.eq (m + 4) (m + 6))))
            (.and (.eq (m + 4) (m + 6)) (lexNF w (m + 4) (m + 5) (m + 7)))))))))))))))))

theorem nsat_keyRF (ρ : Nat → V) (w cw k k' : Nat) :
    NSat mem ρ (keyRF w cw k k') ↔ KeyR H (ρ w) (ρ cw) (ρ k) (ρ k') := by
  simp only [keyRF, NSat, nsat_neg, nsat_kpairF H, nsat_pmemF H, nsat_lexNF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

def isKeyF (w f cw x k : Nat) : NForm :=
  let m := w + f + cw + x + k + 1
  .and (keyPF w cw k) (.ex m (.ex (m + 1) (.ex (m + 2) (.and (.ex (m + 3) (.and
    (kpairF (m + 3) (m + 1) (m + 2)) (kpairF k m (m + 3)))) (.and (isCodeF m)
      (definesF f m (m + 1) (m + 2) x))))))

theorem nsat_isKeyF (ρ : Nat → V) (w f cw x k : Nat) :
    NSat mem ρ (isKeyF w f cw x k) ↔ IsKey H (ρ w) (ρ f) (ρ cw) (ρ x) (ρ k) := by
  simp only [isKeyF, NSat, nsat_keyPF H, nsat_kpairF H, nsat_isCodeF H, nsat_definesF H]
  simp (disch := omega) only [upd_same, upd_other]
  refine and_congr_right fun _ => exists_congr fun c => exists_congr fun n =>
    exists_congr fun t => and_congr_left fun _ => ?_
  constructor
  · rintro ⟨m, rfl, h⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

def newLeF (w f cw x y : Nat) : NForm :=
  let m := w + f + cw + x + y + 1
  .ex m (.and (isKeyF w f cw x m) (.all (m + 1) (.imp (isKeyF w f cw y (m + 1))
    (keyRF w cw m (m + 1)))))

theorem nsat_newLeF (ρ : Nat → V) (w f cw x y : Nat) :
    NSat mem ρ (newLeF w f cw x y) ↔ NewLe H (ρ w) (ρ f) (ρ cw) (ρ x) (ρ y) := by
  simp only [newLeF, NSat, nsat_isKeyF H, nsat_keyRF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

end Defs

section Keys

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include hR hP

omit hR hP in
theorem keyP_iff (W CW c n t : V) :
    KeyP H W CW (kpair H c (kpair H n t)) ↔ Fld H CW c ∧ mem n (omegaV H) ∧ IsTup H W n t := by
  constructor
  · rintro ⟨a, b, e, ha, n', t', e', hn, ht⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e
    obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e'
    exact ⟨ha, hn, ht⟩
  · rintro ⟨hc, hn, ht⟩
    exact ⟨c, _, rfl, hc, n, t, rfl, hn, ht⟩

omit hP in
/-- Keys are well-ordered. -/
theorem key_wo {W CW : V} (hW : IsWOS H W) (hCWo : IsWOS H CW) :
    IsWO mem (KeyR H W CW) (KeyP H W CW) :=
  wo_lex H hCWo.wo fun _ _ => wo_lex H (wo_nat H hR) fun _ hn => wo_lexN H hR hW hn

omit hR in
/-- An environment extending a tuple. -/
theorem env_of_tup {W F d0 n t : V} (hF : ∀ z, mem z F ↔ Fld H W z) (hd0 : mem d0 F)
    (ht : IsTup H W n t) :
    ∃ e, IsEnvOn H F e ∧ SatSupport.AgreeP H n e t := by
  obtain ⟨C, hC⟩ := prod_exists H hP (omegaV H) F
  obtain ⟨e, he⟩ := sep_of H (fun p => ∃ i y, p = kpair H i y ∧
      ((mem i n ∧ mem p t) ∨ (¬ mem i n ∧ y = d0)))
    (.ex 4 (.ex 5 (.and (kpairF 0 4 5) (.or (.and (.mem 4 1) (.mem 0 2))
      (.and (.neg (.mem 4 1)) (.eq 5 3))))))
    (fun i => if i = 1 then n else if i = 2 then t else d0) (fun p => by
      simp only [NSat, nsat_neg, nsat_kpairF H]
      simp (disch := omega) only [upd_same, upd_other]
      rfl) C
  have hval : ∀ i y, mem (kpair H i y) e → (mem i n ∧ mem (kpair H i y) t) ∨ (¬ mem i n ∧ y = d0) :=
    fun i y h => by
      obtain ⟨-, i', y', e', hc⟩ := (he _).1 h
      obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e'
      exact hc
  have hin : ∀ i y, mem i (omegaV H) → mem y F → ((mem i n ∧ mem (kpair H i y) t) ∨
      (¬ mem i n ∧ y = d0)) → mem (kpair H i y) e := fun i y hi hy hc =>
    (he _).2 ⟨(hC _).2 ⟨i, y, hi, hy, rfl⟩, i, y, rfl, hc⟩
  refine ⟨e, ⟨⟨fun i y y' h h' => ?_, fun i hi => ?_, fun p hp => ?_⟩, fun i y h => ?_⟩,
    fun i u u' hi hu hu' => ?_⟩
  · rcases hval i y h with ⟨hi, h1⟩ | ⟨hi, rfl⟩ <;> rcases hval i y' h' with ⟨hi', h2⟩ | ⟨hi', rfl⟩
    · exact ht.1.1 i y y' h1 h2
    · exact absurd hi hi'
    · exact absurd hi' hi
    · rfl
  · by_cases hin' : mem i n
    · obtain ⟨u, hu⟩ := ht.1.2.1 i hin'
      exact ⟨u, hin i u hi ((hF u).2 (ht.2 i u hu)) (Or.inl ⟨hin', hu⟩)⟩
    · exact ⟨d0, hin i d0 hi hd0 (Or.inr ⟨hin', rfl⟩)⟩
  · obtain ⟨hpC, -⟩ := (he p).1 hp
    obtain ⟨i, y, hi, -, rfl⟩ := (hC p).1 hpC
    exact ⟨i, y, hi, rfl⟩
  · obtain ⟨hpC, -⟩ := (he _).1 h
    obtain ⟨i', y', -, hy', e'⟩ := (hC _).1 hpC
    rwa [(kpair_inj H _ _ _ _ e').2]
  · rcases hval i u hu with ⟨-, h1⟩ | ⟨h, -⟩
    · exact ht.1.1 i u u' h1 hu'
    · exact absurd hi h

omit hR in
/-- A key determines its element. -/
theorem key_unique {W F CW x y k : V} (hF : ∀ z, mem z F ↔ Fld H W z) (hne : ∃ d, mem d F)
    (hx : IsKey H W F CW x k) (hy : IsKey H W F CW y k) : x = y := by
  obtain ⟨hkP, c, n, t, rfl, -, hdx⟩ := hx
  obtain ⟨-, c', n', t', e', -, hdy⟩ := hy
  obtain ⟨rfl, e''⟩ := kpair_inj H _ _ _ _ e'
  obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e''
  obtain ⟨-, hn, ht⟩ := (keyP_iff H W CW c n t).1 hkP
  obtain ⟨d0, hd0⟩ := hne
  obtain ⟨e, he, hag⟩ := env_of_tup H hP hF hd0 ht
  obtain ⟨R, hRel⟩ := memRel_exists H hP F
  exact H.ext _ _ fun z => by rw [hdx R e hRel he hag z, hdy R e hRel he hag z]

omit hR hP in
theorem isTup_empty (W : V) : IsTup H W (vempty H) (vempty H) :=
  ⟨⟨fun _ _ _ h => absurd h (vempty_spec H _), fun i hi => absurd hi (vempty_spec H i),
    fun p hp => absurd hp (vempty_spec H p)⟩, fun _ _ h => absurd h (vempty_spec H _)⟩

/-- **Every element of `Def(F)` has a key** (finite support of satisfaction). -/
theorem key_exists {W F CW x : V} (hF : ∀ z, mem z F ↔ Fld H W z)
    (hCW : CodeOrder.IsCodeOrder H hP CW) (hx : mem x (Gdef H hP F)) :
    ∃ k, IsKey H W F CW x k := by
  have hcm := CodeOrder.code_mem H hR hP hCW
  obtain ⟨hsub, hx⟩ := (gdef_spec H hP F x).1 hx
  have hbot : ∀ (R e y : V), ¬ SatIn H F R (kpair H (natV H 2) (vempty H)) (econs H y e) :=
    fun R e y => satIn_bot H
  rcases hx with hemp | ⟨R, c, e, hRel, hc, he, hspec⟩
  · refine ⟨kpair H (kpair H (natV H 2) (vempty H)) (kpair H (vempty H) (vempty H)),
      (keyP_iff H W CW _ _ _).2 ⟨hcm _ (isFormCodeSem_bot H), vempty_in_omega H,
        isTup_empty H W⟩, _, _, _, rfl, isFormCodeSem_bot H, fun R e _ _ _ y => ?_⟩
    exact iff_of_false (hemp y) fun ⟨_, h⟩ => hbot R e y h
  · have hne : ∃ d, mem d F := ⟨_, isEnvOn_apply H he (vempty_in_omega H)⟩
    have hS := setStructure_of_memRel H hRel hne
    obtain ⟨n, hn, hsup⟩ := SatSupport.sat_support H hS c hc
    obtain ⟨t, ht⟩ := TupleOrder.res_exists H e n
    have hnω := ConstructibleZF.omega_trans H n hn
    have htup : IsTup H W n t := by
      refine ⟨⟨fun i y y' h h' => he.1.1 i y y' ((ht _).1 h).1 ((ht _).1 h').1, fun i hi => ?_,
        fun p hp => ?_⟩, fun i y h => (hF y).1 (he.2 i y ((ht _).1 h).1)⟩
      · obtain ⟨y, hy⟩ := he.1.2.1 i (hnω i hi)
        exact ⟨y, (ht _).2 ⟨hy, i, y, hi, rfl⟩⟩
      · obtain ⟨-, i, y, hi, rfl⟩ := (ht p).1 hp
        exact ⟨i, y, hi, rfl⟩
    refine ⟨kpair H c (kpair H n t), (keyP_iff H W CW c n t).2 ⟨hcm c hc, hn, htup⟩, c, n, t, rfl,
      hc, fun R' e' hR' he' hag y => ?_⟩
    have eR : R' = R := H.ext _ _ fun p => by rw [hR' p, hRel p]
    subst eR
    rw [hspec y]
    refine and_congr_right fun hy => ?_
    have hag' : SatSupport.AgreeP H n e' e := fun i a b hi ha hb =>
      hag i a b hi ha ((ht _).2 ⟨hb, i, b, hi, rfl⟩)
    exact (hsup _ _ (econs_isEnvOn H he' hy) (econs_isEnvOn H he hy)
      (SatSupport.agreeP_econs H hn he' he hy hag')).symm

omit hR in
/-- The keys of the elements of a set form a set. -/
theorem key_set {W F CW : V} (hF : ∀ z, mem z F ↔ Fld H W z) (Z : V) :
    ∃ KS, ∀ k, mem k KS ↔ ∃ y, mem y Z ∧ IsKey H W F CW y k := by
  obtain ⟨CF, hCF⟩ := CodeOrder.fld_exists H CW
  obtain ⟨T1, hT1⟩ := prod_exists H hP (omegaV H) F
  obtain ⟨PT, hPT⟩ := hP T1
  obtain ⟨B1, hB1⟩ := prod_exists H hP (omegaV H) PT
  obtain ⟨B, hB⟩ := prod_exists H hP CF B1
  obtain ⟨KS, hKS⟩ := sep_of H (fun k => ∃ y, mem y Z ∧ IsKey H W F CW y k)
    (.ex 5 (.and (.mem 5 1) (isKeyF 2 3 4 5 0)))
    (fun i => if i = 1 then Z else if i = 2 then W else if i = 3 then F else CW) (fun k => by
      simp only [NSat, nsat_isKeyF H]
      simp (disch := omega) only [upd_same, upd_other]
      rfl) B
  refine ⟨KS, fun k => ?_⟩
  rw [hKS k]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨y, -, hkP, c, n, t, rfl, -, -⟩ := h
  obtain ⟨hc, hn, ht⟩ := (keyP_iff H W CW c n t).1 hkP
  refine (hB _).2 ⟨c, _, (hCF c).2 hc, (hB1 _).2 ⟨n, t, hn, (hPT t).2 fun p hp => ?_, rfl⟩, rfl⟩
  obtain ⟨i, y, hi, rfl⟩ := ht.1.2.2 p hp
  exact (hT1 _).2 ⟨i, y, ConstructibleZF.omega_trans H n hn i hi, (hF y).2 (ht.2 i y hp), rfl⟩

/-- **The new elements are well-ordered by their least keys.** -/
theorem new_wo {W F CW : V} (hW : IsWOS H W) (hF : ∀ z, mem z F ↔ Fld H W z)
    (hCW : CodeOrder.IsCodeOrder H hP CW) (hCWo : IsWOS H CW) :
    IsWO mem (NewLe H W F CW) (fun y => mem y (Gdef H hP F) ∧ ¬ mem y F) := by
  refine wo_pull H (key_wo H hR hW hCWo) (fun y hy => key_exists H hR hP hF hCW hy.1)
    (fun y k _ hk => hk.1) (fun y y' k hy hy' hk hk' => ?_) (fun Z _ => key_set H hP hF Z)
  by_cases hne : ∃ d, mem d F
  · exact key_unique H hP hF hne hk hk'
  · have hsub : ∀ z, mem z (Gdef H hP F) → ∀ w, ¬ mem w z := fun z hz w hw =>
      hne ⟨w, ((gdef_spec H hP F z).1 hz).1 w hw⟩
    exact H.ext _ _ fun w => iff_of_false (hsub y hy.1 w) (hsub y' hy'.1 w)

end Keys

/-! ## The step operation -/

section Step

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)

/-- The field of `W`, as a set. -/
noncomputable def fldSet (W : V) : V := (CodeOrder.fld_exists H W).choose

theorem fldSet_spec (W x : V) : mem x (fldSet H W) ↔ Fld H W x :=
  (CodeOrder.fld_exists H W).choose_spec x

/-- The canonical code order. -/
noncomputable def codeOrd : V := (CodeOrder.code_order H hR hP).choose

theorem codeOrd_spec : CodeOrder.IsCodeOrder H hP (codeOrd H hR hP) ∧
    IsWOS H (codeOrd H hR hP) :=
  ⟨(CodeOrder.code_order H hR hP).choose_spec.1, (CodeOrder.code_order H hR hP).choose_spec.2.1⟩

/-- `b` is new for `W`. -/
def NewP (W b : V) : Prop := mem b (Gdef H hP (fldSet H W)) ∧ ¬ mem b (fldSet H W)

/-- Membership in the next stage. -/
def InGL (W p : V) : Prop :=
  mem p W ∨ (∃ a b, p = kpair H a b ∧ Fld H W a ∧ NewP H hP W b) ∨
    (∃ a b, p = kpair H a b ∧ NewP H hP W a ∧ NewP H hP W b ∧
      NewLe H W (fldSet H W) (codeOrd H hR hP) a b)

theorem setNew_exists (W : V) : ∃ N, ∀ b, mem b N ↔ NewP H hP W b :=
  sep_of H (fun b => ¬ mem b (fldSet H W)) (.neg (.mem 0 1))
    (fun _ => fldSet H W) (fun b => by
      simp only [NSat, nsat_neg]
      simp (disch := omega) only [upd_same, upd_other]) (Gdef H hP (fldSet H W))

theorem setOrd_exists (W : V) : ∃ O, ∀ p, mem p O ↔ ∃ a b, p = kpair H a b ∧
    NewP H hP W a ∧ NewP H hP W b ∧ NewLe H W (fldSet H W) (codeOrd H hR hP) a b := by
  obtain ⟨N, hN⟩ := setNew_exists H hP W
  obtain ⟨NN, hNN⟩ := prod_exists H hP N N
  obtain ⟨O, hO⟩ := sep_of H (fun p => ∃ a b, p = kpair H a b ∧ NewP H hP W a ∧ NewP H hP W b ∧
      NewLe H W (fldSet H W) (codeOrd H hR hP) a b)
    (.ex 4 (.ex 5 (.and (kpairF 0 4 5) (.and (.mem 4 1) (.and (.mem 5 1) (newLeF 2 3 6 4 5))))))
    (fun i => if i = 1 then N else if i = 2 then W else if i = 3 then fldSet H W
      else codeOrd H hR hP) (fun p => by
      simp only [NSat, nsat_kpairF H, nsat_newLeF H]
      simp (disch := omega) only [upd_same, upd_other]
      refine exists_congr fun a => exists_congr fun b => and_congr_right fun _ => ?_
      exact and_congr (hN a) (and_congr (hN b) Iff.rfl)) NN
  refine ⟨O, fun p => ?_⟩
  rw [hO p]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨a, b, rfl, ha, hb, -⟩ := h
  exact (hNN _).2 ⟨a, b, (hN a).2 ha, (hN b).2 hb, rfl⟩

noncomputable def setNew (W : V) : V := (setNew_exists H hP W).choose
noncomputable def setOrd (W : V) : V := (setOrd_exists H hR hP W).choose

theorem setNew_spec (W b : V) : mem b (setNew H hP W) ↔ NewP H hP W b :=
  (setNew_exists H hP W).choose_spec b

theorem setOrd_spec (W p : V) : mem p (setOrd H hR hP W) ↔ ∃ a b, p = kpair H a b ∧
    NewP H hP W a ∧ NewP H hP W b ∧ NewLe H W (fldSet H W) (codeOrd H hR hP) a b :=
  (setOrd_exists H hR hP W).choose_spec p

theorem setGL_exists (W : V) : ∃ G, ∀ p, mem p G ↔ InGL H hR hP W p := by
  obtain ⟨A, hA⟩ := prod_exists H hP (fldSet H W) (setNew H hP W)
  refine ⟨vcup H (vcup H W A) (setOrd H hR hP W), fun p => ?_⟩
  rw [vcup_spec H _ _ p, vcup_spec H _ _ p, hA p, setOrd_spec H hR hP]
  unfold InGL
  constructor
  · rintro ((h | ⟨a, b, ha, hb, rfl⟩) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨a, b, rfl, (fldSet_spec H W a).1 ha, (setNew_spec H hP W b).1 hb⟩)
    · exact Or.inr (Or.inr h)
  · rintro (h | ⟨a, b, rfl, ha, hb⟩ | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨a, b, (fldSet_spec H W a).2 ha, (setNew_spec H hP W b).2 hb, rfl⟩)
    · exact Or.inr h

noncomputable def stepL (W : V) : V := (setGL_exists H hR hP W).choose

theorem stepL_spec (W p : V) : mem p (stepL H hR hP W) ↔ InGL H hR hP W p :=
  (setGL_exists H hR hP W).choose_spec p

theorem le_setOrd (W x y : V) : Le H (setOrd H hR hP W) x y ↔
    NewP H hP W x ∧ NewP H hP W y ∧ NewLe H W (fldSet H W) (codeOrd H hR hP) x y := by
  unfold Le
  rw [setOrd_spec H hR hP]
  refine ⟨fun ⟨a, b, e, h⟩ => ?_, fun h => ⟨x, y, rfl, h⟩⟩
  obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e
  exact h

/-- The step appends the new elements, ordered by least keys. -/
theorem appendOpL : AppendOp H (stepL H hR hP) (setNew H hP) (setOrd H hR hP) := by
  refine ⟨fun W _ x y => ?_, fun W _ y hy hy' => ?_, fun W hW => ?_, fun W _ x y h => ?_⟩
  · unfold Le
    rw [stepL_spec H hR hP, setNew_spec H hP]
    unfold InGL
    rw [show mem (kpair H x y) (setOrd H hR hP W) ↔ _ from le_setOrd H hR hP W x y]
    constructor
    · rintro (h | ⟨a, b, e, ha, hb⟩ | ⟨a, b, e, h⟩)
      · exact Or.inl h
      · obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e
        exact Or.inr (Or.inl ⟨ha, hb⟩)
      · obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e
        exact Or.inr (Or.inr h)
    · rintro (h | ⟨ha, hb⟩ | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨x, y, rfl, ha, hb⟩)
      · exact Or.inr (Or.inr ⟨x, y, rfl, h⟩)
  · exact ((setNew_spec H hP W y).1 hy).2 ((fldSet_spec H W y).2 hy')
  · have hnew := new_wo H hR hP hW (fun z => fldSet_spec H W z) (codeOrd_spec H hR hP).1
      (codeOrd_spec H hR hP).2
    refine (hnew.mono fun y hy => (setNew_spec H hP W y).1 hy).congr fun x y hx hy => ?_
    rw [le_setOrd]
    exact ⟨fun h => ⟨(setNew_spec H hP W x).1 hx, (setNew_spec H hP W y).1 hy, h⟩,
      fun h => h.2.2⟩
  · obtain ⟨hx, hy, -⟩ := (le_setOrd H hR hP W x y).1 h
    exact ⟨(setNew_spec H hP W x).2 hx, (setNew_spec H hP W y).2 hy⟩

/-! ### The step as a named formula -/

/-- `f` is the field of `x`. -/
def fldSetF (f x : Nat) : NForm :=
  .all (f + x + 1) ((NForm.mem (f + x + 1) f).iff (pmemF x (f + x + 1) (f + x + 1)))

theorem nsat_fldSetF (ρ : Nat → V) (f x : Nat) :
    NSat mem ρ (fldSetF f x) ↔ ρ f = fldSet H (ρ x) := by
  simp only [fldSetF, NSat, nsat_iff, nsat_pmemF H]
  simp (disch := omega) only [upd_same, upd_other]
  exact ⟨fun h => H.ext _ _ fun z => (h z).trans (fldSet_spec H _ z).symm,
    fun h z => by rw [h, fldSet_spec H]; rfl⟩

/-- `b` is new for `x` (field `f`). -/
def newF (x f b : Nat) : NForm :=
  .and (.ex (x + f + b + 1) (.and (gdefF (x + f + b + 1) f) (.mem b (x + f + b + 1)))) (.neg (.mem b f))

theorem nsat_newF (ρ : Nat → V) (x f b : Nat) (hf : ρ f = fldSet H (ρ x)) :
    NSat mem ρ (newF x f b) ↔ NewP H hP (ρ x) (ρ b) := by
  have hg : ∀ ρ' y x, NSat mem ρ' (gdefF y x) ↔ ρ' y = Gdef H hP (ρ' x) := (defOp H hP).spec
  simp only [newF, NSat, nsat_neg, hg]
  simp (disch := omega) only [upd_same, upd_other]
  rw [hf]
  constructor
  · rintro ⟨⟨D, rfl, h⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩; exact ⟨⟨_, rfl, h⟩, h'⟩

/-- `p ∈ stepL x`. -/
noncomputable def inGLF (x p : Nat) : NForm :=
  let m := x + p + 1
  .ex m (.ex (m + 1) (.and (fldSetF m x) (.and (CodeOrder.codeOrderF H hP (m + 1))
    (.or (.mem p x) (.or (.ex (m + 2) (.ex (m + 3) (.and (kpairF p (m + 2) (m + 3))
      (.and (pmemF x (m + 2) (m + 2)) (newF x m (m + 3))))))
      (.ex (m + 2) (.ex (m + 3) (.and (kpairF p (m + 2) (m + 3)) (.and (newF x m (m + 2))
        (.and (newF x m (m + 3)) (newLeF x m (m + 1) (m + 2) (m + 3))))))))))))

set_option linter.unusedSimpArgs false in
theorem nsat_inGLF (ρ : Nat → V) (x p : Nat) :
    NSat mem ρ (inGLF H hP x p) ↔ InGL H hR hP (ρ x) (ρ p) := by
  simp only [inGLF, NSat]
  constructor
  · rintro ⟨f, cw, hf, hcw, h⟩
    rw [nsat_fldSetF H] at hf
    rw [CodeOrder.nsat_codeOrderF H hP] at hcw
    simp (disch := omega) only [upd_same, upd_other] at hf hcw
    have ecw := CodeOrder.codeOrder_unique H hR hP hcw (codeOrd_spec H hR hP).1
    subst ecw; subst hf
    simp only [NSat, nsat_kpairF H, nsat_pmemF H, nsat_newLeF H] at h
    simp (disch := omega) only [upd_same, upd_other] at h
    unfold InGL
    rcases h with h | ⟨a, b, e, ha, hb⟩ | ⟨a, b, e, ha, hb, hl⟩
    · exact Or.inl h
    · rw [nsat_newF H hP _ _ _ _ (by simp (disch := omega) only [upd_same, upd_other])] at hb
      simp (disch := omega) only [upd_same, upd_other] at hb
      exact Or.inr (Or.inl ⟨a, b, e, ha, hb⟩)
    · rw [nsat_newF H hP _ _ _ _ (by simp (disch := omega) only [upd_same, upd_other])] at ha hb
      simp (disch := omega) only [upd_same, upd_other] at ha hb
      exact Or.inr (Or.inr ⟨a, b, e, ha, hb, hl⟩)
  · intro h
    refine ⟨fldSet H (ρ x), codeOrd H hR hP, ?_, ?_, ?_⟩
    · rw [nsat_fldSetF H]; simp (disch := omega) only [upd_same, upd_other]
    · rw [CodeOrder.nsat_codeOrderF H hP]
      simp (disch := omega) only [upd_same, upd_other]
      exact (codeOrd_spec H hR hP).1
    · simp only [NSat, nsat_kpairF H, nsat_pmemF H, nsat_newLeF H]
      simp (disch := omega) only [upd_same, upd_other]
      have hnew : ∀ (ρ' : Nat → V) (b : Nat), ρ' x = ρ x → ρ' (x + p + 1) = fldSet H (ρ x) →
          (NSat mem ρ' (newF x (x + p + 1) b) ↔ NewP H hP (ρ x) (ρ' b)) := by
        intro ρ' b h1 h2
        rw [nsat_newF H hP _ _ _ _ (by rw [h1, h2]), h1]
      rcases h with h | ⟨a, b, e, ha, hb⟩ | ⟨a, b, e, ha, hb, hl⟩
      · exact Or.inl h
      · refine Or.inr (Or.inl ⟨a, b, e, ha, ?_⟩)
        rw [hnew _ _ (by simp (disch := omega) only [upd_same, upd_other])
          (by simp (disch := omega) only [upd_same, upd_other])]
        simp (disch := omega) only [upd_same, upd_other]; exact hb
      · refine Or.inr (Or.inr ⟨a, b, e, ?_, ?_, hl⟩)
        · rw [hnew _ _ (by simp (disch := omega) only [upd_same, upd_other])
            (by simp (disch := omega) only [upd_same, upd_other])]
          simp (disch := omega) only [upd_same, upd_other]; exact ha
        · rw [hnew _ _ (by simp (disch := omega) only [upd_same, upd_other])
            (by simp (disch := omega) only [upd_same, upd_other])]
          simp (disch := omega) only [upd_same, upd_other]; exact hb

/-- The step is a definable operation. -/
noncomputable def stepLOp : DefOp mem (stepL H hR hP) where
  gF := fun y x => .all (y + x + 1) ((NForm.mem (y + x + 1) y).iff (inGLF H hP x (y + x + 1)))
  spec := fun ρ y x => by
    simp only [NSat, nsat_iff, nsat_inGLF H hR hP]
    simp (disch := omega) only [upd_same, upd_other]
    constructor
    · intro h; exact H.ext _ _ fun p => by rw [h p, stepL_spec H hR hP]
    · intro h p; rw [h, stepL_spec H hR hP]

end Step

/-! ## The canonical well-order and Choice -/

section Choice

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)

/-- **Every stage of the canonical order is a well-order.** -/
theorem lord_wos {a W : V} (ha : Ord mem a) (h : IsStage H (stepL H hR hP) a W) : IsWOS H W :=
  (stage_wos H hR (stepLOp H hR hP) (appendOpL H hR hP) a ha W h).1

/-- **The field of the stage `a` of the canonical order is `L_a`.** -/
theorem lord_fld : ∀ a, Ord mem a → ∀ W S, IsStage H (stepL H hR hP) a W → IsL H hP a S →
    ∀ x, Fld H W x ↔ mem x S := by
  refine ord_induction H hR _ (.all 1 (.all 2 (.imp (isStageF (stepLOp H hR hP) 0 1)
    (.imp (isStageF (defOp H hP) 0 2) (.all 3 ((pmemF 1 3 3).iff (.mem 3 2)))))))
    (fun _ => vempty H) (fun a => by
      simp only [NSat, nsat_iff, nsat_isStageF H, nsat_pmemF H]
      simp (disch := omega) only [upd_same, upd_other]
      rfl) ?_
  intro a ha IH W S hW hS x
  rw [show Fld H W x ↔ _ from stage_spec H hR (stepLOp H hR hP) ha hW (kpair H x x),
    isL_spec H hR hP ha hS x]
  constructor
  · rintro ⟨c, Wc, hc, hWc, hx⟩
    have hco := ord_of_mem ha hc
    obtain ⟨T, hT⟩ := isL_exists H hR hP hco
    have hWco := lord_wos H hR hP hco hWc
    have hfl := IH c hc Wc T hWc hT
    refine ⟨c, T, hc, hT, ?_⟩
    rcases (fld_step H (appendOpL H hR hP) hWco x).1 hx with hx | hx
    · exact mem_gdef_of_mem H hP (isL_trans H hR hP hco hT) ((hfl x).1 hx)
    · have hfs : fldSet H Wc = T := H.ext _ _ fun z => by rw [fldSet_spec H, hfl z]
      have := ((setNew_spec H hP Wc x).1 hx).1
      rwa [hfs] at this
  · rintro ⟨c, T, hc, hT, hx⟩
    have hco := ord_of_mem ha hc
    obtain ⟨Wc, hWc⟩ := stage_exists' H hR (stepLOp H hR hP) hco
    have hWco := lord_wos H hR hP hco hWc
    have hfl := IH c hc Wc T hWc hT
    have hfs : fldSet H Wc = T := H.ext _ _ fun z => by rw [fldSet_spec H, hfl z]
    refine ⟨c, Wc, hc, hWc, (fld_step H (appendOpL H hR hP) hWco x).2 ?_⟩
    by_cases hxT : mem x T
    · exact Or.inl ((hfl x).2 hxT)
    · exact Or.inr ((setNew_spec H hP Wc x).2 ⟨by rwa [hfs], by rwa [hfs]⟩)

include hR in
/-- **Choice under `V = L`.** In a model of ZF in which every set is
constructible, every family of pairwise disjoint nonempty sets has a
selector: the least elements in the canonical order. -/
theorem choice_of_VL (hVL : ∀ x, InL H hP x) : ChoiceSem mem := by
  intro x hne hdis
  obtain ⟨b, T, hb, hT, hsub⟩ := stage_bound H hR hP (A := vunion H x) (fun z _ => hVL z)
  obtain ⟨W, hW⟩ := stage_exists' H hR (stepLOp H hR hP) hb
  have hWo := lord_wos H hR hP hb hW
  have hfl := lord_fld H hR hP b hb W T hW hT
  have hyF : ∀ y, mem y x → ∀ z, mem z y → Fld H W z := fun y hy z hz =>
    (hfl z).2 (hsub z ((vunion_spec H x z).2 ⟨y, hz, hy⟩))
  obtain ⟨c, hc⟩ := sep_of H (fun z => ∃ y, mem y x ∧ mem z y ∧ ∀ w, mem w y → Le H W z w)
    (.ex 3 (.and (.mem 3 1) (.and (.mem 0 3) (.all 4 (.imp (.mem 4 3) (pmemF 2 0 4))))))
    (fun i => if i = 1 then x else W) (fun z => by
      simp only [NSat, nsat_pmemF H]
      simp (disch := omega) only [upd_same, upd_other]
      rfl) (vunion H x)
  refine ⟨c, fun y hy => ?_⟩
  obtain ⟨m, hm, hmin⟩ := hWo.least y (hne y hy) (hyF y hy)
  refine ⟨m, hm, (hc m).2 ⟨(vunion_spec H x m).2 ⟨y, hm, hy⟩, y, hy, hm, hmin⟩, fun w hw hwc => ?_⟩
  obtain ⟨-, y', hy', hwy', hwmin⟩ := (hc w).1 hwc
  have e : y = y' := Classical.byContradiction fun hne' => hdis y y' hy hy' hne' ⟨w, hw, hwy'⟩
  subst e
  exact hWo.antisymm w m (hwmin m hm) (hmin w hw)

end Choice

end SetTheory.BusyBeaver.ZFC.ConstructibleOrder
