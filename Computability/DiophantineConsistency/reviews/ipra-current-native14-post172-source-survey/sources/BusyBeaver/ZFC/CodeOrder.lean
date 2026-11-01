import BusyBeaver.ZFC.OrderRec

/-!
A definable well-order of the internal formula codes.

Formula codes are Kuratowski pairs built from internal naturals, so they lie
in the pair closure of `ω`. That closure is well-ordered by an `OrderRec`
recursion along `ω`: stage `1` is `ω` under `∈`, and each later stage appends
the new pairs of elements of the current field, ordered lexicographically.
The stage at `ω` (`IsCodeOrder`) is a well-order whose field contains every
internal code, standard or not (`code_order`). It is definable without
parameters (`codeOrderF`), which is what the constructible well-order needs.
-/

namespace SetTheory.BusyBeaver.ZFC.CodeOrder

open NamedZF NForm InternalOrd InternalRank TransRec InternalWO OrderRec
  LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

section Defs

variable (H : ZFAxioms mem)

/-- The field of `W` is empty. -/
def EmptyFld (W : V) : Prop := ∀ x, ¬ Fld H W x

/-- `a` is new for `W`: an internal natural if `W` has empty field, otherwise
a pair of field elements outside the field. -/
def InN (W a : V) : Prop :=
  (EmptyFld H W ∧ mem a (omegaV H)) ∨
  (¬ EmptyFld H W ∧ ¬ Fld H W a ∧ ∃ u v, Fld H W u ∧ Fld H W v ∧ a = kpair H u v)

/-- The order of the new elements. -/
def InO (W p : V) : Prop :=
  ∃ a b, p = kpair H a b ∧ InN H W a ∧ InN H W b ∧
    ((EmptyFld H W ∧ (mem a b ∨ a = b)) ∨
      (¬ EmptyFld H W ∧ LexR H (Le H W) (fun _ => Le H W) a b))

/-- Membership in the next stage. -/
def InG (W p : V) : Prop :=
  (∃ a b, p = kpair H a b ∧ (Fld H W a ∨ InN H W a) ∧ (Fld H W b ∨ InN H W b)) ∧
  (mem p W ∨ (∃ a b, p = kpair H a b ∧ Fld H W a ∧ InN H W b) ∨ InO H W p)

def emptyF (w : Nat) : NForm := .all (w + 1) (.neg (pmemF w (w + 1) (w + 1)))

theorem nsat_emptyF (ρ : Nat → V) (w : Nat) : NSat mem ρ (emptyF w) ↔ EmptyFld H (ρ w) := by
  simp only [emptyF, NSat, nsat_neg, nsat_pmemF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

def inNF (w a : Nat) : NForm :=
  let n := w + a + 1
  .or (.and (emptyF w) (SatSupport.inOmegaF a))
    (.and (.neg (emptyF w)) (.and (.neg (pmemF w a a)) (.ex n (.ex (n + 1)
      (.and (pmemF w n n) (.and (pmemF w (n + 1) (n + 1)) (kpairF a n (n + 1))))))))

theorem nsat_inNF (ρ : Nat → V) (w a : Nat) : NSat mem ρ (inNF w a) ↔ InN H (ρ w) (ρ a) := by
  simp only [inNF, NSat, nsat_neg, nsat_emptyF H, SatSupport.nsat_inOmegaF H, nsat_pmemF H,
    nsat_kpairF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

def lexF (w a b : Nat) : NForm :=
  let n := w + a + b + 1
  .ex n (.ex (n + 1) (.ex (n + 2) (.ex (n + 3) (.and (kpairF a n (n + 1))
    (.and (kpairF b (n + 2) (n + 3)) (.or (.and (pmemF w n (n + 2)) (.neg (.eq n (n + 2))))
      (.and (.eq n (n + 2)) (pmemF w (n + 1) (n + 3)))))))))

theorem nsat_lexF (ρ : Nat → V) (w a b : Nat) :
    NSat mem ρ (lexF w a b) ↔ LexR H (Le H (ρ w)) (fun _ => Le H (ρ w)) (ρ a) (ρ b) := by
  simp only [lexF, NSat, nsat_neg, nsat_pmemF H, nsat_kpairF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

def inOF (w p : Nat) : NForm :=
  let n := w + p + 1
  .ex n (.ex (n + 1) (.and (kpairF p n (n + 1)) (.and (inNF w n) (.and (inNF w (n + 1))
    (.or (.and (emptyF w) (.or (.mem n (n + 1)) (.eq n (n + 1))))
      (.and (.neg (emptyF w)) (lexF w n (n + 1))))))))

theorem nsat_inOF (ρ : Nat → V) (w p : Nat) : NSat mem ρ (inOF w p) ↔ InO H (ρ w) (ρ p) := by
  simp only [inOF, NSat, nsat_neg, nsat_kpairF H, nsat_inNF H, nsat_emptyF H, nsat_lexF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

def inGF (w p : Nat) : NForm :=
  let n := w + p + 1
  .and (.ex n (.ex (n + 1) (.and (kpairF p n (n + 1)) (.and (.or (pmemF w n n) (inNF w n))
      (.or (pmemF w (n + 1) (n + 1)) (inNF w (n + 1)))))))
    (.or (.mem p w) (.or (.ex n (.ex (n + 1) (.and (kpairF p n (n + 1))
      (.and (pmemF w n n) (inNF w (n + 1)))))) (inOF w p)))

theorem nsat_inGF (ρ : Nat → V) (w p : Nat) : NSat mem ρ (inGF w p) ↔ InG H (ρ w) (ρ p) := by
  simp only [inGF, NSat, nsat_pmemF H, nsat_kpairF H, nsat_inNF H, nsat_inOF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

end Defs

section Sets

variable (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include hP

omit hP in
theorem fld_exists (W : V) : ∃ F, ∀ x, mem x F ↔ Fld H W x := by
  obtain ⟨F, hF⟩ := sep_of H (fun x => Fld H W x) (pmemF 1 0 0) (fun _ => W)
    (fun x => by
      simp only [nsat_pmemF H]
      simp (disch := omega) only [upd_same, upd_other]
      rfl) (vunion H (vunion H W))
  exact ⟨F, fun x => by rw [hF x]; exact ⟨fun h => h.2, fun h => ⟨(comp_mem_uu H h).1, h⟩⟩⟩

/-- A set containing every field element and every new element. -/
theorem cand_exists (W : V) : ∃ E, ∀ a, (Fld H W a ∨ InN H W a) → mem a E := by
  obtain ⟨F, hF⟩ := fld_exists H W
  obtain ⟨FF, hFF⟩ := prod_exists H hP F F
  refine ⟨vcup H (vcup H F (omegaV H)) FF, fun a ha => ?_⟩
  rw [vcup_spec H _ _ a, vcup_spec H _ _ a]
  rcases ha with ha | ⟨⟨-, ha⟩ | ⟨-, -, u, v, hu, hv, rfl⟩⟩
  · exact Or.inl (Or.inl ((hF a).2 ha))
  · exact Or.inl (Or.inr ha)
  · exact Or.inr ((hFF _).2 ⟨u, v, (hF u).2 hu, (hF v).2 hv, rfl⟩)

theorem setN_exists (W : V) : ∃ N, ∀ a, mem a N ↔ InN H W a := by
  obtain ⟨E, hE⟩ := cand_exists H hP W
  obtain ⟨N, hN⟩ := sep_of H (fun a => InN H W a) (inNF 1 0) (fun _ => W)
    (fun a => by
      rw [nsat_inNF H]
      simp (disch := omega) only [upd_same, upd_other]) E
  exact ⟨N, fun a => by rw [hN a]; exact ⟨fun h => h.2, fun h => ⟨hE a (Or.inr h), h⟩⟩⟩

theorem setO_exists (W : V) : ∃ O, ∀ p, mem p O ↔ InO H W p := by
  obtain ⟨N, hN⟩ := setN_exists H hP W
  obtain ⟨NN, hNN⟩ := prod_exists H hP N N
  obtain ⟨O, hO⟩ := sep_of H (fun p => InO H W p) (inOF 1 0) (fun _ => W)
    (fun p => by
      rw [nsat_inOF H]
      simp (disch := omega) only [upd_same, upd_other]) NN
  refine ⟨O, fun p => ?_⟩
  rw [hO p]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨a, b, rfl, ha, hb, -⟩ := h
  exact (hNN _).2 ⟨a, b, (hN a).2 ha, (hN b).2 hb, rfl⟩

theorem setG_exists (W : V) : ∃ G, ∀ p, mem p G ↔ InG H W p := by
  obtain ⟨E, hE⟩ := cand_exists H hP W
  obtain ⟨EE, hEE⟩ := prod_exists H hP E E
  obtain ⟨G, hG⟩ := sep_of H (fun p => InG H W p) (inGF 1 0) (fun _ => W)
    (fun p => by
      rw [nsat_inGF H]
      simp (disch := omega) only [upd_same, upd_other]) EE
  refine ⟨G, fun p => ?_⟩
  rw [hG p]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨⟨a, b, rfl, ha, hb⟩, -⟩ := h
  exact (hEE _).2 ⟨a, b, hE a ha, hE b hb, rfl⟩

noncomputable def setN (W : V) : V := (setN_exists H hP W).choose
noncomputable def setO (W : V) : V := (setO_exists H hP W).choose
noncomputable def stepG (W : V) : V := (setG_exists H hP W).choose

theorem setN_spec (W a : V) : mem a (setN H hP W) ↔ InN H W a := (setN_exists H hP W).choose_spec a
theorem setO_spec (W p : V) : mem p (setO H hP W) ↔ InO H W p := (setO_exists H hP W).choose_spec p
theorem stepG_spec (W p : V) : mem p (stepG H hP W) ↔ InG H W p :=
  (setG_exists H hP W).choose_spec p

/-- The step is a definable operation. -/
noncomputable def stepOp : DefOp mem (stepG H hP) where
  gF := fun y x => .all (y + x + 1) ((NForm.mem (y + x + 1) y).iff (inGF x (y + x + 1)))
  spec := fun ρ y x => by
    simp only [NSat, nsat_iff, nsat_inGF H]
    simp (disch := omega) only [upd_same, upd_other]
    constructor
    · intro h; exact H.ext _ _ fun p => by rw [h p, stepG_spec H hP]
    · intro h p; rw [h, stepG_spec H hP]

theorem le_setO (W x y : V) : Le H (setO H hP W) x y ↔
    InN H W x ∧ InN H W y ∧ ((EmptyFld H W ∧ (mem x y ∨ x = y)) ∨
      (¬ EmptyFld H W ∧ LexR H (Le H W) (fun _ => Le H W) x y)) := by
  unfold Le
  rw [setO_spec H hP]
  refine ⟨fun ⟨a, b, e, h⟩ => ?_, fun h => ⟨x, y, rfl, h⟩⟩
  obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e
  exact h

variable (hR : Regular mem)
include hR

/-- The step appends the new elements. -/
theorem appendOp : AppendOp H (stepG H hP) (setN H hP) (setO H hP) := by
  refine ⟨fun W hW x y => ?_, fun W _ y hy hy' => ?_, fun W hW => ?_, fun W _ x y h => ?_⟩
  · have hO : InO H W (kpair H x y) ↔ Le H (setO H hP W) x y := by
      unfold Le; rw [setO_spec H hP]
    have key : InG H W (kpair H x y) ↔
        Le H W x y ∨ (Fld H W x ∧ InN H W y) ∨ InO H W (kpair H x y) := by
      unfold InG
      constructor
      · rintro ⟨-, h | ⟨a, b, e, ha, hb⟩ | h⟩
        · exact Or.inl h
        · obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e
          exact Or.inr (Or.inl ⟨ha, hb⟩)
        · exact Or.inr (Or.inr h)
      · intro h
        refine ⟨⟨x, y, rfl, ?_⟩, ?_⟩
        · rcases h with h | ⟨hx, hy⟩ | ⟨a, b, e, ha, hb, -⟩
          · exact ⟨Or.inl (hW.fld x y h).1, Or.inl (hW.fld x y h).2⟩
          · exact ⟨Or.inl hx, Or.inr hy⟩
          · obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e
            exact ⟨Or.inr ha, Or.inr hb⟩
        · rcases h with h | ⟨hx, hy⟩ | h
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨x, y, rfl, hx, hy⟩)
          · exact Or.inr (Or.inr h)
    have := key.trans (or_congr Iff.rfl (or_congr Iff.rfl hO))
    unfold Le at this ⊢
    rwa [stepG_spec H hP, setN_spec H hP]
  · rcases (setN_spec H hP W y).1 hy with ⟨he, -⟩ | ⟨-, hn, -⟩
    · exact he y hy'
    · exact hn hy'
  · by_cases he : EmptyFld H W
    · have hnat := wo_nat H hR
      refine (hnat.mono fun y hy => ?_).congr fun x y hx hy => ?_
      · exact (((setN_spec H hP W y).1 hy).resolve_right fun h => h.1 he).2
      · rw [le_setO]
        constructor
        · intro h; exact ⟨(setN_spec H hP W x).1 hx, (setN_spec H hP W y).1 hy, Or.inl ⟨he, h⟩⟩
        · rintro ⟨-, -, ⟨-, h⟩ | ⟨h, -⟩⟩
          · exact h
          · exact absurd he h
    · have hlex := wo_lex H hW.wo (P2 := fun _ => Fld H W) (r2 := fun _ => Le H W)
        fun _ _ => hW.wo
      refine (hlex.mono fun y hy => ?_).congr fun x y hx hy => ?_
      · rcases (setN_spec H hP W y).1 hy with ⟨h, -⟩ | ⟨-, -, u, v, hu, hv, rfl⟩
        · exact absurd h he
        · exact ⟨u, v, rfl, hu, hv⟩
      · rw [le_setO]
        constructor
        · intro h
          exact ⟨(setN_spec H hP W x).1 hx, (setN_spec H hP W y).1 hy, Or.inr ⟨he, h⟩⟩
        · rintro ⟨-, -, ⟨h, -⟩ | ⟨-, h⟩⟩
          · exact absurd h he
          · exact h
  · obtain ⟨hx, hy, -⟩ := (le_setO H hP W x y).1 h
    exact ⟨(setN_spec H hP W x).2 hx, (setN_spec H hP W y).2 hy⟩

end Sets

section Order

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)

/-- `CW` is the code order: the stage at `ω` of the pair-closure recursion. -/
def IsCodeOrder (CW : V) : Prop := IsStage H (stepG H hP) (omegaV H) CW

/-- `x` lies in the field of the stage `k`. -/
def FldS (k x : V) : Prop := ∃ W, IsStage H (stepG H hP) k W ∧ Fld H W x

omit hP in
theorem natOrd {k : V} (hk : mem k (omegaV H)) : Ord mem k :=
  ord_of_mem (ConstructibleZF.ord_omega H) hk

include hR

theorem stage_isWOS {k W : V} (hk : Ord mem k) (h : IsStage H (stepG H hP) k W) : IsWOS H W :=
  (stage_wos H hR (stepOp H hP) (appendOp H hP hR) k hk W h).1

theorem stage_empty {W : V} (h : IsStage H (stepG H hP) (vempty H) W) : EmptyFld H W :=
  fun x hx => by
    obtain ⟨c, T, hc, -, -⟩ :=
      (stage_spec H hR (stepOp H hP) (natOrd H (vempty_in_omega H)) h _).1 hx
    exact vempty_spec H c hc

theorem fldS_mono {k k' x : V} (hk' : Ord mem k') (hkk : mem k k' ∨ k = k')
    (h : FldS H hP k x) : FldS H hP k' x := by
  obtain ⟨W, hW, hx⟩ := h
  rcases hkk with hkk | rfl
  · obtain ⟨W', hW'⟩ := stage_exists' H hR (stepOp H hP) hk'
    exact ⟨W', hW', stage_mono H hR (stepOp H hP) hk' hkk hW hW' _ hx⟩
  · exact ⟨W, hW, hx⟩

theorem fldS_succ {k W x : V} (hk : Ord mem k) (hW : IsStage H (stepG H hP) k W)
    (hx : Fld H (stepG H hP W) x) : FldS H hP (vsucc H k) x := by
  obtain ⟨W', hW'⟩ := stage_exists' H hR (stepOp H hP) (ord_succ H hk)
  exact ⟨W', hW', (stage_spec H hR (stepOp H hP) (ord_succ H hk) hW' _).2
    ⟨k, W, vsucc_self H k, hW, hx⟩⟩

theorem fldS_stage {k W x : V} (hk : Ord mem k) (hW : IsStage H (stepG H hP) k W)
    (h : FldS H hP k x) : Fld H W x := by
  obtain ⟨W', hW', hx⟩ := h
  rwa [stage_unique H hR hk hW hW']

theorem omega_fldS_one {n : V} (hn : mem n (omegaV H)) : FldS H hP (vsucc H (vempty H)) n := by
  have h0 := natOrd H (vempty_in_omega H)
  obtain ⟨W0, hW0⟩ := stage_exists' H hR (stepOp H hP) h0
  refine fldS_succ H hR hP h0 hW0 ?_
  rw [fld_step H (appendOp H hP hR) (stage_isWOS H hR hP h0 hW0), setN_spec H hP]
  exact Or.inr (Or.inl ⟨stage_empty H hR hP hW0, hn⟩)

theorem omega_fldS {k n : V} (hk : mem k (omegaV H)) (h0 : mem (vempty H) k)
    (hn : mem n (omegaV H)) : FldS H hP k n :=
  fldS_mono H hR hP (natOrd H hk) (succ_le_of_lt H k hk _ h0) (omega_fldS_one H hR hP hn)

theorem pair_fldS {k u v : V} (hk : mem k (omegaV H)) (h0 : mem (vempty H) k)
    (hu : FldS H hP k u) (hv : FldS H hP k v) : FldS H hP (vsucc H k) (kpair H u v) := by
  have hko := natOrd H hk
  obtain ⟨W, hW⟩ := stage_exists' H hR (stepOp H hP) hko
  have hWo := stage_isWOS H hR hP hko hW
  refine fldS_succ H hR hP hko hW ?_
  rw [fld_step H (appendOp H hP hR) hWo, setN_spec H hP]
  have hu' := fldS_stage H hR hP hko hW hu
  have hv' := fldS_stage H hR hP hko hW hv
  by_cases hp : Fld H W (kpair H u v)
  · exact Or.inl hp
  · refine Or.inr (Or.inr ⟨fun he => he (vempty H) ?_, hp, u, v, hu', hv', rfl⟩)
    exact fldS_stage H hR hP hko hW (omega_fldS H hR hP hk h0 (vempty_in_omega H))

theorem cw_of_fldS {CW k x : V} (hCW : IsCodeOrder H hP CW) (hk : mem k (omegaV H))
    (h : FldS H hP k x) : Fld H CW x := by
  obtain ⟨W, hW, hx⟩ := h
  exact stage_mono H hR (stepOp H hP) (ConstructibleZF.ord_omega H) hk hW hCW _ hx

theorem fldS_of_cw {CW x : V} (hCW : IsCodeOrder H hP CW) (hx : Fld H CW x) :
    ∃ k, mem k (omegaV H) ∧ FldS H hP (vsucc H k) x := by
  obtain ⟨c, T, hc, hT, hxT⟩ :=
    (stage_spec H hR (stepOp H hP) (ConstructibleZF.ord_omega H) hCW _).1 hx
  exact ⟨c, hc, fldS_succ H hR hP (natOrd H hc) hT hxT⟩

/-- Two field elements of the code order lie in a common stage `k ≥ 1`. -/
theorem common_stage {CW a b : V} (hCW : IsCodeOrder H hP CW) (ha : Fld H CW a)
    (hb : Fld H CW b) : ∃ m, mem m (omegaV H) ∧ mem (vempty H) m ∧
      FldS H hP m a ∧ FldS H hP m b := by
  obtain ⟨k, hk, hka⟩ := fldS_of_cw H hR hP hCW ha
  obtain ⟨k', hk', hkb⟩ := fldS_of_cw H hR hP hCW hb
  obtain ⟨m, hm, h1, h2⟩ := SatSupport.nat_upper H (omega_succ H k hk) (omega_succ H k' hk')
  have h0 : mem (vempty H) (vsucc H k) := (vsucc_spec H k _).2 (vempty_le_nat H k hk)
  refine ⟨m, hm, ?_, fldS_mono H hR hP (natOrd H hm) h1 hka, fldS_mono H hR hP (natOrd H hm) h2 hkb⟩
  rcases h1 with h1 | rfl
  · exact nat_transitive H m hm _ h1 _ h0
  · exact h0

theorem tag_cw {CW : V} (hCW : IsCodeOrder H hP CW) (t : Nat) {x : V}
    (hx : ∃ m, mem m (omegaV H) ∧ mem (vempty H) m ∧ FldS H hP m x) :
    Fld H CW (kpair H (natV H t) x) := by
  obtain ⟨m, hm, h0, hx⟩ := hx
  have hm1 := omega_succ H m hm
  have h01 : mem (vempty H) (vsucc H m) := (vsucc_spec H m _).2 (Or.inl h0)
  exact cw_of_fldS H hR hP hCW (omega_succ H _ hm1) (pair_fldS H hR hP hm1 h01
    (omega_fldS H hR hP hm1 h01 (natV_mem_omega H t))
    (fldS_mono H hR hP (natOrd H hm1) (Or.inl (vsucc_self H m)) hx))

/-- **Every internal formula code lies in the field of the code order.** -/
theorem code_mem {CW : V} (hCW : IsCodeOrder H hP CW) :
    ∀ c, IsFormCodeSem H c → Fld H CW c := by
  have h1ω := omega_succ H _ (vempty_in_omega H)
  have hbin : ∀ (t : Nat) a b, Fld H CW a → Fld H CW b →
      Fld H CW (kpair H (natV H t) (kpair H a b)) := by
    intro t a b ha hb
    obtain ⟨m, hm, h0, hma, hmb⟩ := common_stage H hR hP hCW ha hb
    exact tag_cw H hR hP hCW t ⟨_, omega_succ H m hm, (vsucc_spec H m _).2 (Or.inl h0),
      pair_fldS H hR hP hm h0 hma hmb⟩
  have hun : ∀ (t : Nat) a, Fld H CW a → Fld H CW (kpair H (natV H t) a) := by
    intro t a ha
    obtain ⟨m, hm, h0, hma, -⟩ := common_stage H hR hP hCW ha ha
    exact tag_cw H hR hP hCW t ⟨m, hm, h0, hma⟩
  have hω : ∀ n, mem n (omegaV H) → Fld H CW n := fun n hn =>
    cw_of_fldS H hR hP hCW h1ω (omega_fldS_one H hR hP hn)
  refine isFormCodeSem_ind' H _ (toForm id (pmemF 1 0 0)) (fun _ => CW)
    (fun y => by
      rw [sat_toForm, nsat_pmemF H]
      rfl)
    (fun a b ha hb => hbin 0 a b (hω a ha) (hω b hb))
    (fun a b ha hb => hbin 1 a b (hω a ha) (hω b hb))
    (hun 2 _ (hω _ (vempty_in_omega H)))
    (fun a b ha hb => hbin 3 a b ha hb) (fun a b ha hb => hbin 4 a b ha hb)
    (fun a b ha hb => hbin 5 a b ha hb) (fun a ha => hun 6 a ha) (fun a ha => hun 7 a ha)

/-- **The code order exists**, is unique, is a well-order, and contains every code. -/
theorem code_order : ∃ CW, IsCodeOrder H hP CW ∧ IsWOS H CW ∧
    ∀ c, IsFormCodeSem H c → Fld H CW c := by
  obtain ⟨CW, hCW⟩ := stage_exists' H hR (stepOp H hP) (ConstructibleZF.ord_omega H)
  exact ⟨CW, hCW, stage_isWOS H hR hP (ConstructibleZF.ord_omega H) hCW, code_mem H hR hP hCW⟩

theorem codeOrder_unique {CW CW' : V} (h : IsCodeOrder H hP CW) (h' : IsCodeOrder H hP CW') :
    CW = CW' :=
  stage_unique H hR (ConstructibleZF.ord_omega H) h h'

end Order

/-- `o = ω`. -/
def omegaEqF (o : Nat) : NForm :=
  .all (o + 1) ((NForm.mem (o + 1) o).iff (SatSupport.inOmegaF (o + 1)))

theorem nsat_omegaEqF (H : ZFAxioms mem) (ρ : Nat → V) (o : Nat) :
    NSat mem ρ (omegaEqF o) ↔ ρ o = omegaV H := by
  simp only [omegaEqF, NSat, nsat_iff, SatSupport.nsat_inOmegaF H]
  simp (disch := omega) only [upd_same, upd_other]
  exact ⟨fun h => H.ext _ _ h, fun h z => by rw [h]⟩

/-- The named formula for "`w` is the code order". -/
noncomputable def codeOrderF (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
    (w : Nat) : NForm :=
  .ex (w + 1) (.and (omegaEqF (w + 1)) (isStageF (stepOp H hP) (w + 1) w))

theorem nsat_codeOrderF (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
    (ρ : Nat → V) (w : Nat) : NSat mem ρ (codeOrderF H hP w) ↔ IsCodeOrder H hP (ρ w) := by
  simp only [codeOrderF, NSat, nsat_omegaEqF H, nsat_isStageF H]
  simp (disch := omega) only [upd_same, upd_other]
  constructor
  · rintro ⟨o, rfl, h⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

end SetTheory.BusyBeaver.ZFC.CodeOrder
