import BusyBeaver.ZFC.SatSupport

/-!
Absoluteness between a model of ZF and its constructible class.

`N = {x // InL x}` with `memL` is a model of the ZF bundle
(`ConstructibleZF.L_zfAxioms`). Every internal notion of the satisfaction
machinery computed in `N` agrees with the same notion computed in the
ambient model `M` on constructible arguments: the basic set operations,
`ω`, application, the environment shift, the truth bits, the certificate
step relation, certificates themselves and hence `SatIn`, formula codes,
definability (using the uniform finite support of `SatSupport` to replace a
non-constructible environment), `Def`, and finally the constructible
hierarchy. Consequently **`N` satisfies `V = L`**: every element of `N` is
constructible in the sense of `N` (`vEqL`).
-/

namespace SetTheory.BusyBeaver.ZFC.ConstructibleAbs

open NamedZF NForm InternalOrd InternalRank TransRec ConstructibleDef Constructible
  ConstructibleZF LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

section Ops

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP

/-- Equality of a constructible set with an ambient set, by extensionality. -/
theorem val_eq {u : {x // InL H hP x}} {v : V} (hv : ∀ z, mem z v → InL H hP z)
    (h : ∀ z : {x // InL H hP x}, mem z.1 u.1 ↔ mem z.1 v) : u.1 = v :=
  H.ext _ _ fun z => ⟨fun hz => (h ⟨z, inL_trans H hR hP u.2 hz⟩).1 hz,
    fun hz => (h ⟨z, hv z hz⟩).2 hz⟩

theorem val_vpair (a b : {x // InL H hP x}) :
    (vpair (L_zfAxioms H hR hP) a b).1 = vpair H a.1 b.1 := by
  refine val_eq H hR hP (fun z hz => ?_) fun z => ?_
  · rcases (vpair_spec H _ _ z).1 hz with rfl | rfl
    · exact a.2
    · exact b.2
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
    constructor
    · rintro ⟨v, h1, h2⟩; exact ⟨v.1, h1, h2⟩
    · rintro ⟨v, h1, h2⟩; exact ⟨⟨v, inL_trans H hR hP a.2 h2⟩, h1, h2⟩

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
  refine and_congr ?_ ?_
  · show mem (vempty (L_zfAxioms H hR hP)).1 c.1 ↔ _
    rw [val_vempty H hR hP]
  · constructor
    · intro h y hy
      have : mem (vsucc (L_zfAxioms H hR hP) ⟨y, inL_trans H hR hP c.2 hy⟩).1 c.1 :=
        h ⟨y, inL_trans H hR hP c.2 hy⟩ hy
      rwa [val_vsucc H hR hP] at this
    · intro h y hy
      show mem (vsucc (L_zfAxioms H hR hP) y).1 c.1
      rw [val_vsucc H hR hP]; exact h y.1 hy

theorem inL_omega : InL H hP (omegaV H) := inL_ord H hR hP (ord_omega H)

theorem val_omegaV : (omegaV (L_zfAxioms H hR hP)).1 = omegaV H := by
  refine val_eq H hR hP (fun z hz => inL_trans H hR hP (inL_omega H hR hP) hz) fun z => ?_
  rw [show mem z.1 (omegaV (L_zfAxioms H hR hP)).1 ↔ _ from
    mem_omega_iff (L_zfAxioms H hR hP) z, mem_omega_iff H]
  constructor
  · intro h c hc
    have := h ⟨omegaV H, inL_omega H hR hP⟩ ((inductive_iff H hR hP _).2 (omega_inductive H))
    exact (mem_omega_iff H z.1).1 this c hc
  · intro h c hc
    exact h c.1 ((inductive_iff H hR hP c).1 hc)

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
  constructor
  · intro h x y y' hy hy'
    obtain ⟨hx, hyL⟩ := inL_of_kpair_mem H hR hP F.2 hy
    obtain ⟨-, hy'L⟩ := inL_of_kpair_mem H hR hP F.2 hy'
    have := h ⟨x, hx⟩ ⟨y, hyL⟩ ⟨y', hy'L⟩ ((kpairN_mem H hR hP _ _ _).2 hy)
      ((kpairN_mem H hR hP _ _ _).2 hy')
    exact congrArg Subtype.val this
  · intro h x y y' hy hy'
    exact Subtype.ext (h x.1 y.1 y'.1 ((kpairN_mem H hR hP _ _ _).1 hy)
      ((kpairN_mem H hR hP _ _ _).1 hy'))

theorem isFunctionOn_iff (F d : {x // InL H hP x}) :
    IsFunctionOn (L_zfAxioms H hR hP) F d ↔ IsFunctionOn H F.1 d.1 := by
  unfold IsFunctionOn
  refine and_congr (functional_iff H hR hP F) (and_congr ?_ ?_)
  · constructor
    · intro h x hx
      obtain ⟨y, hy⟩ := h ⟨x, inL_trans H hR hP d.2 hx⟩ hx
      exact ⟨y.1, (kpairN_mem H hR hP _ _ _).1 hy⟩
    · intro h x hx
      obtain ⟨y, hy⟩ := h x.1 hx
      exact ⟨⟨y, (inL_of_kpair_mem H hR hP F.2 hy).2⟩, (kpairN_mem H hR hP _ _ _).2 hy⟩
  · constructor
    · intro h p hp
      obtain ⟨x, y, hx, he⟩ := h ⟨p, inL_trans H hR hP F.2 hp⟩ hp
      exact ⟨x.1, y.1, hx, (kpairN_eq H hR hP _ _ _).1 he⟩
    · intro h p hp
      obtain ⟨x, y, hx, he⟩ := h p.1 hp
      have hxy := inL_kpair H hR hP (he ▸ p.2)
      exact ⟨⟨x, hxy.1⟩, ⟨y, hxy.2⟩, hx, (kpairN_eq H hR hP _ _ _).2 he⟩

theorem isEnvOn_iff (A E : {x // InL H hP x}) :
    IsEnvOn (L_zfAxioms H hR hP) A E ↔ IsEnvOn H A.1 E.1 := by
  unfold IsEnvOn
  rw [isFunctionOn_iff H hR hP]
  refine and_congr ?_ ?_
  · exact Iff.of_eq (congrArg (IsFunctionOn H E.1) (val_omegaV H hR hP))
  · constructor
    · intro h n y hy
      obtain ⟨hn, hyL⟩ := inL_of_kpair_mem H hR hP E.2 hy
      exact h ⟨n, hn⟩ ⟨y, hyL⟩ ((kpairN_mem H hR hP _ _ _).2 hy)
    · intro h n y hy
      exact h n.1 y.1 ((kpairN_mem H hR hP _ _ _).1 hy)

/-- Application agrees on a graph with a recorded value. -/
theorem val_applyV {F x : {x // InL H hP x}}
    (hfun : ∀ a b b', mem (kpair H a b) F.1 → mem (kpair H a b') F.1 → b = b')
    {y : V} (hy : mem (kpair H x.1 y) F.1) : (applyV (L_zfAxioms H hR hP) F x).1 = y := by
  have hyL := (inL_of_kpair_mem H hR hP F.2 hy).2
  have := applyV_eq (L_zfAxioms H hR hP) ((functional_iff H hR hP F).2 hfun)
    (x := x) (y := ⟨y, hyL⟩) ((kpairN_mem H hR hP _ _ _).2 hy)
  rw [this]

theorem val_applyV_env {A E n : {x // InL H hP x}} (hE : IsEnvOn H A.1 E.1)
    (hn : mem n.1 (omegaV H)) : (applyV (L_zfAxioms H hR hP) E n).1 = applyV H E.1 n.1 :=
  val_applyV H hR hP hE.1.1 (applyV_mem H (hE.1.2.1 n.1 hn))

theorem val_econs {d E : {x // InL H hP x}}
    (hfun : ∀ a b b', mem (kpair H a b) E.1 → mem (kpair H a b') E.1 → b = b') :
    (econs (L_zfAxioms H hR hP) d E).1 = econs H d.1 E.1 := by
  have hfunN := (functional_iff H hR hP E).2 hfun
  refine val_eq H hR hP (fun z hz => ?_) fun z => ?_
  · rcases (econs_spec H hfun d.1 z).1 hz with rfl | ⟨n, hn, y, hy, rfl⟩
    · exact inL_pair H hR hP (inL_pair H hR hP (inL_ord H hR hP (ord_of_mem (ord_omega H)
        (vempty_in_omega H))) (inL_ord H hR hP (ord_of_mem (ord_omega H) (vempty_in_omega H))))
        (inL_pair H hR hP (inL_ord H hR hP (ord_of_mem (ord_omega H) (vempty_in_omega H))) d.2)
    · have hnL := (inL_of_kpair_mem H hR hP E.2 hy)
      have hs : InL H hP (vsucc H n) :=
        inL_ord H hR hP (ord_succ H (ord_of_mem (ord_omega H) hn))
      exact inL_pair H hR hP (inL_pair H hR hP hs hs) (inL_pair H hR hP hs hnL.2)
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
      rw [kpairN_eq H hR hP, val_vsucc H hR hP]; exact he

theorem val_vbit (p : Prop) : (vbit (L_zfAxioms H hR hP) p).1 = vbit H p := by
  by_cases hp : p
  · rw [vbit_pos _ hp, vbit_pos _ hp, val_natV H hR hP]
  · rw [vbit_neg _ hp, vbit_neg _ hp, val_natV H hR hP]

theorem val_satTriple (c e b : {x // InL H hP x}) :
    (satTriple (L_zfAxioms H hR hP) c e b).1 = satTriple H c.1 e.1 b.1 := by
  show (kpair (L_zfAxioms H hR hP) _ _).1 = kpair H _ _
  rw [val_kpair H hR hP, val_kpair H hR hP]

theorem inL_satTriple {c e b : V} (h : InL H hP (satTriple H c e b)) :
    InL H hP c ∧ InL H hP e ∧ InL H hP b := by
  obtain ⟨hc, h2⟩ := inL_kpair H hR hP h
  obtain ⟨he, hb⟩ := inL_kpair H hR hP h2
  exact ⟨hc, he, hb⟩

theorem inL_nat {n : V} (hn : mem n (omegaV H)) : InL H hP n :=
  inL_trans H hR hP (inL_omega H hR hP) hn

theorem inL_kpair_of {a b : V} (ha : InL H hP a) (hb : InL H hP b) : InL H hP (kpair H a b) :=
  inL_pair H hR hP (inL_pair H hR hP ha ha) (inL_pair H hR hP ha hb)

theorem codeEq_iff (t : Nat) (c x : {x // InL H hP x}) :
    c = kpair (L_zfAxioms H hR hP) (natV (L_zfAxioms H hR hP) t) x ↔
      c.1 = kpair H (natV H t) x.1 := by
  rw [Subtype.ext_iff, val_kpair H hR hP, val_natV H hR hP]

theorem codeEq2_iff (t : Nat) (c x y : {x // InL H hP x}) :
    c = kpair (L_zfAxioms H hR hP) (natV (L_zfAxioms H hR hP) t)
      (kpair (L_zfAxioms H hR hP) x y) ↔ c.1 = kpair H (natV H t) (kpair H x.1 y.1) := by
  rw [Subtype.ext_iff, val_kpair H hR hP, val_natV H hR hP, val_kpair H hR hP]

theorem bitEq_iff (b : {x // InL H hP x}) (p q : Prop) (hpq : p ↔ q) :
    b = vbit (L_zfAxioms H hR hP) p ↔ b.1 = vbit H q := by
  rw [Subtype.ext_iff, val_vbit H hR hP, vbit_congr H hpq]

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
  constructor
  · rintro ⟨i, j, hi, hj, hc, hb⟩
    have hi' := (mem_omegaN H hR hP i).1 hi
    have hj' := (mem_omegaN H hR hP j).1 hj
    exact ⟨i.1, j.1, hi', hj', (codeEq2_iff H hR hP t c i j).1 hc,
      (bitEq_iff H hR hP b _ _ (hQ i j hi' hj')).1 hb⟩
  · rintro ⟨i, j, hi, hj, hc, hb⟩
    let i' : {x // InL H hP x} := ⟨i, inL_nat H hR hP hi⟩
    let j' : {x // InL H hP x} := ⟨j, inL_nat H hR hP hj⟩
    exact ⟨i', j', (mem_omegaN H hR hP i').2 hi, (mem_omegaN H hR hP j').2 hj,
      (codeEq2_iff H hR hP t c i' j').2 hc, (bitEq_iff H hR hP b _ _ (hQ i' j' hi hj)).2 hb⟩

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
  constructor
  · rintro ⟨c1, c2, b1, b2, hc, h1, h2, hb⟩
    refine ⟨c1.1, c2.1, b1.1, b2.1, (codeEq2_iff H hR hP t c c1 c2).1 hc,
      (tripleMem_iff H hR hP _ _ _ _).1 h1, (tripleMem_iff H hR hP _ _ _ _).1 h2,
      (bitEq_iff H hR hP b _ _ ?_).1 hb⟩
    rw [natEq_iff H hR hP, natEq_iff H hR hP]
  · rintro ⟨c1, c2, b1, b2, hc, h1, h2, hb⟩
    have t1 := inL_satTriple H hR hP (inL_trans H hR hP S.2 h1)
    have t2 := inL_satTriple H hR hP (inL_trans H hR hP S.2 h2)
    let c1' : {x // InL H hP x} := ⟨c1, t1.1⟩
    let c2' : {x // InL H hP x} := ⟨c2, t2.1⟩
    let b1' : {x // InL H hP x} := ⟨b1, t1.2.2⟩
    let b2' : {x // InL H hP x} := ⟨b2, t2.2.2⟩
    refine ⟨c1', c2', b1', b2', (codeEq2_iff H hR hP t c c1' c2').2 hc,
      (tripleMem_iff H hR hP c1' e b1' S).2 h1, (tripleMem_iff H hR hP c2' e b2' S).2 h2,
      (bitEq_iff H hR hP b _ _ ?_).2 hb⟩
    rw [natEq_iff H hR hP, natEq_iff H hR hP]

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
  constructor
  · rintro ⟨c1, hc, h⟩
    refine ⟨c1.1, (codeEq_iff H hR hP t c c1).1 hc, ?_⟩
    rcases h with ⟨hb, hall⟩ | ⟨hb, d, hd, hdS⟩
    · exact Or.inl ⟨(natEq_iff H hR hP b u).1 hb, fun d hd =>
        (hT c1 ⟨d, inL_trans H hR hP A.2 hd⟩ u).1 (hall ⟨d, inL_trans H hR hP A.2 hd⟩ hd)⟩
    · exact Or.inr ⟨(natEq_iff H hR hP b v).1 hb, d.1, hd, (hT c1 d v).1 hdS⟩
  · rintro ⟨c1, hc, h⟩
    let c1' : {x // InL H hP x} := ⟨c1, hc1 c1 hc⟩
    refine ⟨c1', (codeEq_iff H hR hP t c c1').2 hc, ?_⟩
    rcases h with ⟨hb, hall⟩ | ⟨hb, d, hd, hdS⟩
    · exact Or.inl ⟨(natEq_iff H hR hP b u).2 hb, fun d hd => (hT c1' d u).2 (hall d.1 hd)⟩
    · exact Or.inr ⟨(natEq_iff H hR hP b v).2 hb, ⟨d, inL_trans H hR hP A.2 hd⟩, hd,
        (hT c1' ⟨d, inL_trans H hR hP A.2 hd⟩ v).2 hdS⟩

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
  constructor
  · intro h c e b hm
    obtain ⟨hc, he, hb⟩ := inL_satTriple H hR hP (inL_trans H hR hP S.2 hm)
    obtain ⟨hE, hJ⟩ := h ⟨c, hc⟩ ⟨e, he⟩ ⟨b, hb⟩ ((tripleMem_iff H hR hP _ _ _ _).2 hm)
    have hE' := (isEnvOn_iff H hR hP A ⟨e, he⟩).1 hE
    exact ⟨hE', (justified_iff H hR hP hE').1 hJ⟩
  · intro h c e b hm
    obtain ⟨hE, hJ⟩ := h c.1 e.1 b.1 ((tripleMem_iff H hR hP _ _ _ _).1 hm)
    exact ⟨(isEnvOn_iff H hR hP A e).2 hE, (justified_iff H hR hP hE).2 hJ⟩

theorem certifies_iff (A R S c e b : {x // InL H hP x}) :
    Certifies (L_zfAxioms H hR hP) A R S c e b ↔ Certifies H A.1 R.1 S.1 c.1 e.1 b.1 :=
  ⟨fun h => ⟨(satClosed_iff H hR hP A R S).1 h.closed, (tripleMem_iff H hR hP _ _ _ _).1 h.holds⟩,
   fun h => ⟨(satClosed_iff H hR hP A R S).2 h.closed, (tripleMem_iff H hR hP _ _ _ _).2 h.holds⟩⟩

theorem isSetStructure_iff (A R : {x // InL H hP x}) :
    IsSetStructure (L_zfAxioms H hR hP) A R ↔ IsSetStructure H A.1 R.1 := by
  constructor
  · intro h
    refine ⟨?_, fun p hp => ?_⟩
    · obtain ⟨d, hd⟩ := h.nonempty; exact ⟨d.1, hd⟩
    · obtain ⟨x, y, hx, hy, he⟩ := h.pairs ⟨p, inL_trans H hR hP R.2 hp⟩ hp
      exact ⟨x.1, y.1, hx, hy, (kpairN_eq H hR hP _ _ _).1 he⟩
  · intro h
    refine ⟨?_, fun p hp => ?_⟩
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
  constructor
  · intro h p
    constructor
    · intro hp
      obtain ⟨a, b, ha, hb, hab, he⟩ := (h ⟨p, inL_trans H hR hP R.2 hp⟩).1 hp
      exact ⟨a.1, b.1, ha, hb, hab, (kpairN_eq H hR hP _ _ _).1 he⟩
    · rintro ⟨a, b, ha, hb, hab, rfl⟩
      have haL := inL_trans H hR hP X.2 ha
      have hbL := inL_trans H hR hP X.2 hb
      exact (h ⟨_, inL_kpair_of H hR hP haL hbL⟩).2
        ⟨⟨a, haL⟩, ⟨b, hbL⟩, ha, hb, hab, (kpairN_eq H hR hP _ _ _).2 rfl⟩
  · intro h p
    rw [show memL H hP p R ↔ mem p.1 R.1 from Iff.rfl, h p.1]
    constructor
    · rintro ⟨a, b, ha, hb, hab, he⟩
      exact ⟨⟨a, inL_trans H hR hP X.2 ha⟩, ⟨b, inL_trans H hR hP X.2 hb⟩, ha, hb, hab,
        (kpairN_eq H hR hP _ _ _).2 he⟩
    · rintro ⟨a, b, ha, hb, hab, he⟩
      exact ⟨a.1, b.1, ha, hb, hab, (kpairN_eq H hR hP _ _ _).1 he⟩

end Ops

end SetTheory.BusyBeaver.ZFC.ConstructibleAbs
