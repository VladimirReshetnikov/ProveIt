import BusyBeaver.ZFC.ConstructibleAbs

/-!
Internal well-orders of classes, inside a model of ZF.

`IsWO r P` says that the relation `r` is a (reflexive) well-order of the
class `P`: a total order on `P` under which every nonempty *set* of members
of `P` has an `r`-least element. Neither `r` nor `P` has to be a set; the
constructions below only ever separate sets by simple named formulas that do
not mention `r`.

The kit: the internal naturals (`wo_nat`), restriction, the
lexicographic order of pairs with a well-ordered fibre over each first
component (`wo_lex`), an order pulled back along least keys (`wo_pull`), and
the ordered sum of two disjoint well-ordered classes (`wo_append`). With them
a canonical well-order of the constructible hierarchy can be assembled
in a later module; that construction is not supplied here.
-/

namespace SetTheory.BusyBeaver.ZFC.InternalWO

open NamedZF NForm InternalOrd InternalRank LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- `r` well-orders the class `P`. -/
structure IsWO (mem : V → V → Prop) (r : V → V → Prop) (P : V → Prop) : Prop where
  refl : ∀ x, P x → r x x
  antisymm : ∀ x y, P x → P y → r x y → r y x → x = y
  trans : ∀ x y z, P x → P y → P z → r x y → r y z → r x z
  total : ∀ x y, P x → P y → r x y ∨ r y x
  least : ∀ Z, (∃ z, mem z Z) → (∀ z, mem z Z → P z) → ∃ m, mem m Z ∧ ∀ z, mem z Z → r m z

theorem IsWO.mono {r : V → V → Prop} {P Q : V → Prop} (h : IsWO mem r P)
    (hQ : ∀ x, Q x → P x) : IsWO mem r Q :=
  ⟨fun x hx => h.refl x (hQ x hx), fun x y hx hy => h.antisymm x y (hQ x hx) (hQ y hy),
    fun x y z hx hy hz => h.trans x y z (hQ x hx) (hQ y hy) (hQ z hz),
    fun x y hx hy => h.total x y (hQ x hx) (hQ y hy),
    fun Z hne hZ => h.least Z hne fun z hz => hQ z (hZ z hz)⟩

theorem IsWO.congr {r r' : V → V → Prop} {P : V → Prop} (h : IsWO mem r P)
    (hr : ∀ x y, P x → P y → (r x y ↔ r' x y)) : IsWO mem r' P :=
  ⟨fun x hx => (hr x x hx hx).1 (h.refl x hx),
    fun x y hx hy h1 h2 => h.antisymm x y hx hy ((hr x y hx hy).2 h1) ((hr y x hy hx).2 h2),
    fun x y z hx hy hz h1 h2 => (hr x z hx hz).1
      (h.trans x y z hx hy hz ((hr x y hx hy).2 h1) ((hr y z hy hz).2 h2)),
    fun x y hx hy => (h.total x y hx hy).imp (hr x y hx hy).1 (hr y x hy hx).1,
    fun Z hne hZ => (h.least Z hne hZ).imp fun m ⟨hm, hmin⟩ =>
      ⟨hm, fun z hz => (hr m z (hZ m hm) (hZ z hz)).1 (hmin z hz)⟩⟩

/-- The least element is unique. -/
theorem IsWO.least_unique {r : V → V → Prop} {P : V → Prop} (h : IsWO mem r P) {Z m m' : V}
    (hZ : ∀ z, mem z Z → P z) (hm : mem m Z) (hmin : ∀ z, mem z Z → r m z)
    (hm' : mem m' Z) (hmin' : ∀ z, mem z Z → r m' z) : m = m' :=
  h.antisymm m m' (hZ m hm) (hZ m' hm') (hmin m' hm') (hmin' m hm)

section Kit

variable (H : ZFAxioms mem)

/-- **The internal naturals are well-ordered by `∈`-or-equal.** -/
theorem wo_nat (hR : Regular mem) :
    IsWO mem (fun m n => mem m n ∨ m = n) (fun n => mem n (omegaV H)) := by
  refine ⟨fun x _ => Or.inr rfl, fun x y hx hy h1 h2 => ?_, fun x y z hx hy hz h1 h2 => ?_,
    fun x y hx hy => ?_, fun Z hne hZ => ?_⟩
  · rcases h1 with h1 | rfl
    · rcases h2 with h2 | rfl
      · exact absurd (nat_transitive H x hx y h2 x h1) (mem_irrefl H hR x)
      · rfl
    · rfl
  · rcases h1 with h1 | rfl
    · rcases h2 with h2 | rfl
      · exact Or.inl (nat_transitive H z hz y h2 x h1)
      · exact Or.inl h1
    · exact h2
  · exact (nat_linear H x hx y hy).elim (fun h => Or.inl (Or.inl h)) (Or.imp Or.inr Or.inl)
  · obtain ⟨m, hm, hmin⟩ := hR Z hne
    exact ⟨m, hm, fun z hz => (nat_linear H m (hZ m hm) z (hZ z hz)).elim Or.inl fun h =>
      h.elim Or.inr fun h => absurd ⟨z, h, hz⟩ hmin⟩

/-- The members of members of members of `Z` (pair components live there). -/
theorem comp_mem_uu {Z a b : V} (h : mem (kpair H a b) Z) :
    mem a (vunion H (vunion H Z)) ∧ mem b (vunion H (vunion H Z)) := by
  have hs : mem (vsingle H a) (vunion H Z) :=
    (vunion_spec H Z _).2 ⟨_, (kpair_mem H a b _).2 (Or.inl rfl), h⟩
  have hp : mem (vpair H a b) (vunion H Z) :=
    (vunion_spec H Z _).2 ⟨_, (kpair_mem H a b _).2 (Or.inr rfl), h⟩
  exact ⟨(vunion_spec H _ a).2 ⟨_, (vsingle_spec H a a).2 rfl, hs⟩,
    (vunion_spec H _ b).2 ⟨_, (vpair_spec H a b b).2 (Or.inr rfl), hp⟩⟩

/-- The first components of the pairs in `Z`. -/
theorem firsts_exists (Z : V) : ∃ A, ∀ a, mem a A ↔ ∃ b, mem (kpair H a b) Z := by
  obtain ⟨A, hA⟩ := sep_of H (fun a => ∃ b, mem (kpair H a b) Z) (.ex 2 (pmemF 1 0 2))
    (fun _ => Z) (fun a => by
      simp only [NSat, nsat_pmemF H]
      simp (disch := omega) only [upd_same, upd_other]) (vunion H (vunion H Z))
  exact ⟨A, fun a => (hA a).trans ⟨fun h => h.2, fun ⟨b, hb⟩ => ⟨(comp_mem_uu H hb).1, b, hb⟩⟩⟩

/-- The second components of the pairs in `Z` with first component `a`. -/
theorem fibre_exists (Z a : V) : ∃ B, ∀ b, mem b B ↔ mem (kpair H a b) Z := by
  obtain ⟨B, hB⟩ := sep_of H (fun b => mem (kpair H a b) Z) (pmemF 1 2 0)
    (fun i => if i = 1 then Z else a) (fun b => by
      simp only [nsat_pmemF H]
      simp (disch := omega) only [upd_same, upd_other]
      rfl) (vunion H (vunion H Z))
  exact ⟨B, fun b => (hB b).trans ⟨fun h => h.2, fun h => ⟨(comp_mem_uu H h).2, h⟩⟩⟩

/-- Pairs whose first component lies in `P1` and second in the fibre `P2 a`. -/
def LexP (P1 : V → Prop) (P2 : V → V → Prop) (p : V) : Prop :=
  ∃ a b, p = kpair H a b ∧ P1 a ∧ P2 a b

/-- The lexicographic order of pairs. -/
def LexR (r1 : V → V → Prop) (r2 : V → V → V → Prop) (p q : V) : Prop :=
  ∃ a b a' b', p = kpair H a b ∧ q = kpair H a' b' ∧ ((r1 a a' ∧ a ≠ a') ∨ (a = a' ∧ r2 a b b'))

theorem lexR_iff {r1 : V → V → Prop} {r2 : V → V → V → Prop} (a b a' b' : V) :
    LexR H r1 r2 (kpair H a b) (kpair H a' b') ↔ ((r1 a a' ∧ a ≠ a') ∨ (a = a' ∧ r2 a b b')) := by
  refine ⟨fun ⟨x, y, x', y', e1, e2, h⟩ => ?_, fun h => ⟨a, b, a', b', rfl, rfl, h⟩⟩
  obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e1
  obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e2
  exact h

/-- **Lexicographic order.** A well-ordered class of first components, with a
well-ordered fibre over each, gives a well-ordered class of pairs. -/
theorem wo_lex {P1 : V → Prop} {r1 : V → V → Prop} (h1 : IsWO mem r1 P1)
    {P2 : V → V → Prop} {r2 : V → V → V → Prop} (h2 : ∀ a, P1 a → IsWO mem (r2 a) (P2 a)) :
    IsWO mem (LexR H r1 r2) (LexP H P1 P2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, b, rfl, ha, hb⟩
    exact (lexR_iff H a b a b).2 (Or.inr ⟨rfl, (h2 a ha).refl b hb⟩)
  · rintro _ _ ⟨a, b, rfl, ha, hb⟩ ⟨a', b', rfl, ha', hb'⟩ hxy hyx
    rw [lexR_iff] at hxy hyx
    rcases hxy with ⟨h, hne⟩ | ⟨rfl, h⟩ <;> rcases hyx with ⟨h', hne'⟩ | ⟨e, h'⟩
    · exact absurd (h1.antisymm a a' ha ha' h h') hne
    · exact absurd e.symm hne
    · exact absurd rfl hne'
    · rw [(h2 a ha).antisymm b b' hb hb' h h']
  · rintro _ _ _ ⟨a, b, rfl, ha, hb⟩ ⟨a', b', rfl, ha', hb'⟩ ⟨a'', b'', rfl, ha'', hb''⟩ hxy hyz
    rw [lexR_iff] at hxy hyz ⊢
    rcases hxy with ⟨h, hne⟩ | ⟨rfl, h⟩ <;> rcases hyz with ⟨h', hne'⟩ | ⟨rfl, h'⟩
    · refine Or.inl ⟨h1.trans a a' a'' ha ha' ha'' h h', fun e => ?_⟩
      subst e
      exact hne (h1.antisymm a a' ha ha' h h')
    · exact Or.inl ⟨h, hne⟩
    · exact Or.inl ⟨h', hne'⟩
    · exact Or.inr ⟨rfl, (h2 a ha).trans b b' b'' hb hb' hb'' h h'⟩
  · rintro _ _ ⟨a, b, rfl, ha, hb⟩ ⟨a', b', rfl, ha', hb'⟩
    rw [lexR_iff, lexR_iff]
    by_cases e : a = a'
    · subst e
      exact ((h2 a ha).total b b' hb hb').imp (fun h => Or.inr ⟨rfl, h⟩) fun h => Or.inr ⟨rfl, h⟩
    · exact (h1.total a a' ha ha').imp (fun h => Or.inl ⟨h, e⟩)
        fun h => Or.inl ⟨h, fun e' => e e'.symm⟩
  · intro Z ⟨z0, hz0⟩ hZ
    obtain ⟨A, hA⟩ := firsts_exists H Z
    have hAP : ∀ a, mem a A → P1 a := fun a ha => by
      obtain ⟨b, hb⟩ := (hA a).1 ha
      obtain ⟨x, y, e, hx, -⟩ := hZ _ hb
      rwa [(kpair_inj H _ _ _ _ e).1]
    obtain ⟨x0, y0, e0, -, -⟩ := hZ z0 hz0
    obtain ⟨a, ha, hamin⟩ := h1.least A ⟨x0, (hA x0).2 ⟨y0, e0 ▸ hz0⟩⟩ hAP
    obtain ⟨B, hB⟩ := fibre_exists H Z a
    have hBP : ∀ b, mem b B → P2 a b := fun b hb => by
      obtain ⟨x, y, e, -, hy⟩ := hZ _ ((hB b).1 hb)
      obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ e
      exact hy
    obtain ⟨b1, hb1⟩ := (hA a).1 ha
    obtain ⟨b, hb, hbmin⟩ := (h2 a (hAP a ha)).least B ⟨b1, (hB b1).2 hb1⟩ hBP
    refine ⟨kpair H a b, (hB b).1 hb, fun z hz => ?_⟩
    obtain ⟨a', b', rfl, -, -⟩ := hZ z hz
    rw [lexR_iff]
    by_cases e : a = a'
    · subst e
      exact Or.inr ⟨rfl, hbmin b' ((hB b').2 hz)⟩
    · exact Or.inl ⟨hamin a' ((hA a').2 ⟨b', hz⟩), e⟩

include H in
/-- **Least-key pullback.** If every member of `PY` has keys, keys determine
their member, keys are well-ordered, and the keys of a set of members form a
set, then comparing least keys well-orders `PY`. -/
theorem wo_pull {PY PK : V → Prop} {Key : V → V → Prop} {rk : V → V → Prop}
    (hK : IsWO mem rk PK) (hex : ∀ y, PY y → ∃ k, Key y k)
    (hkK : ∀ y k, PY y → Key y k → PK k)
    (huniq : ∀ y y' k, PY y → PY y' → Key y k → Key y' k → y = y')
    (hset : ∀ Z, (∀ z, mem z Z → PY z) → ∃ KS, ∀ k, mem k KS ↔ ∃ y, mem y Z ∧ Key y k) :
    IsWO mem (fun y y' => ∃ k, Key y k ∧ ∀ k', Key y' k' → rk k k') PY := by
  have hlk : ∀ y, PY y → ∃ k, Key y k ∧ ∀ k', Key y k' → rk k k' := by
    intro y hy
    obtain ⟨KS, hKS⟩ := hset (vsingle H y) fun z hz => by rw [(vsingle_spec H y z).1 hz]; exact hy
    have hKS' : ∀ k, mem k KS ↔ Key y k := fun k => by
      rw [hKS k]
      exact ⟨fun ⟨y', hy', h⟩ => by rwa [(vsingle_spec H y y').1 hy'] at h,
        fun h => ⟨y, (vsingle_spec H y y).2 rfl, h⟩⟩
    obtain ⟨k0, hk0⟩ := hex y hy
    obtain ⟨m, hm, hmin⟩ := hK.least KS ⟨k0, (hKS' k0).2 hk0⟩
      fun k hk => hkK y k hy ((hKS' k).1 hk)
    exact ⟨m, (hKS' m).1 hm, fun k' hk' => hmin k' ((hKS' k').2 hk')⟩
  refine ⟨fun y hy => hlk y hy, ?_, ?_, ?_, ?_⟩
  · rintro y y' hy hy' ⟨k, hk, hk'⟩ ⟨k', hk2, hk2'⟩
    obtain rfl := hK.antisymm k k' (hkK y k hy hk) (hkK y' k' hy' hk2) (hk' k' hk2) (hk2' k hk)
    exact huniq y y' _ hy hy' hk hk2
  · rintro y y' y'' hy hy' hy'' ⟨k, hk, hk'⟩ ⟨k', hk2, hk2'⟩
    exact ⟨k, hk, fun k'' hk'' => hK.trans k k' k'' (hkK y k hy hk) (hkK y' k' hy' hk2)
      (hkK y'' k'' hy'' hk'') (hk' k' hk2) (hk2' k'' hk'')⟩
  · intro y y' hy hy'
    obtain ⟨k, hk, hkmin⟩ := hlk y hy
    obtain ⟨k', hk2, hk2min⟩ := hlk y' hy'
    rcases hK.total k k' (hkK y k hy hk) (hkK y' k' hy' hk2) with h | h
    · exact Or.inl ⟨k, hk, fun k'' hk'' => hK.trans k k' k'' (hkK y k hy hk) (hkK y' k' hy' hk2)
        (hkK y' k'' hy' hk'') h (hk2min k'' hk'')⟩
    · exact Or.inr ⟨k', hk2, fun k'' hk'' => hK.trans k' k k'' (hkK y' k' hy' hk2) (hkK y k hy hk)
        (hkK y k'' hy hk'') h (hkmin k'' hk'')⟩
  · intro Z ⟨z0, hz0⟩ hZ
    obtain ⟨KS, hKS⟩ := hset Z hZ
    obtain ⟨k0, hk0⟩ := hex z0 (hZ z0 hz0)
    obtain ⟨m, hm, hmin⟩ := hK.least KS ⟨k0, (hKS k0).2 ⟨z0, hz0, hk0⟩⟩ fun k hk =>
      let ⟨y, hy, hky⟩ := (hKS k).1 hk; hkK y k (hZ y hy) hky
    obtain ⟨y, hy, hmy⟩ := (hKS m).1 hm
    exact ⟨y, hy, fun z hz => ⟨m, hmy, fun k' hk' => hmin k' ((hKS k').2 ⟨z, hz, hk'⟩)⟩⟩

/-- **Ordered sum** of two disjoint well-ordered classes, the first separable. -/
theorem wo_append {PA PB : V → Prop} {rA rB : V → V → Prop} (hA : IsWO mem rA PA)
    (hB : IsWO mem rB PB) (hdis : ∀ x, PA x → PB x → False)
    (hsep : ∀ Z, ∃ Z', ∀ z, mem z Z' ↔ mem z Z ∧ PA z) :
    IsWO mem (fun x y => (PA x ∧ PA y ∧ rA x y) ∨ (PA x ∧ PB y) ∨ (PB x ∧ PB y ∧ rB x y))
      (fun x => PA x ∨ PB x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro x (hx | hx)
    · exact Or.inl ⟨hx, hx, hA.refl x hx⟩
    · exact Or.inr (Or.inr ⟨hx, hx, hB.refl x hx⟩)
  · intro x y _ _ h1 h2
    rcases h1 with ⟨hx, hy, h1⟩ | ⟨hx, hy⟩ | ⟨hx, hy, h1⟩ <;>
      rcases h2 with ⟨hy', hx', h2⟩ | ⟨hy', hx'⟩ | ⟨hy', hx', h2⟩
    all_goals first
      | exact hA.antisymm x y hx hy h1 h2
      | exact hB.antisymm x y hx hy h1 h2
      | exact absurd hx (fun h => hdis x h ‹PB x›)
      | exact absurd hy (fun h => hdis y h ‹PB y›)
      | exact (hdis x ‹PA x› ‹PB x›).elim
      | exact (hdis y ‹PA y› ‹PB y›).elim
  · intro x y z _ _ _ h1 h2
    rcases h1 with ⟨hx, hy, h1⟩ | ⟨hx, hy⟩ | ⟨hx, hy, h1⟩ <;>
      rcases h2 with ⟨hy', hz, h2⟩ | ⟨hy', hz⟩ | ⟨hy', hz, h2⟩
    all_goals first
      | exact Or.inr (Or.inl ⟨hx, hz⟩)
      | exact (hdis y hy' hy).elim
      | exact Or.inl ⟨hx, hz, hA.trans x y z hx hy hz h1 h2⟩
      | exact Or.inr (Or.inr ⟨hx, hz, hB.trans x y z hx hy hz h1 h2⟩)
  · rintro x y (hx | hx) (hy | hy)
    · exact (hA.total x y hx hy).imp (fun h => Or.inl ⟨hx, hy, h⟩) (fun h => Or.inl ⟨hy, hx, h⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨hx, hy⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hy, hx⟩))
    · exact (hB.total x y hx hy).imp (fun h => Or.inr (Or.inr ⟨hx, hy, h⟩))
        (fun h => Or.inr (Or.inr ⟨hy, hx, h⟩))
  · intro Z ⟨z0, hz0⟩ hZ
    obtain ⟨Z', hZ'⟩ := hsep Z
    by_cases hne : ∃ z, mem z Z'
    · obtain ⟨m, hm, hmin⟩ := hA.least Z' hne fun z hz => ((hZ' z).1 hz).2
      obtain ⟨hmZ, hmA⟩ := (hZ' m).1 hm
      refine ⟨m, hmZ, fun z hz => ?_⟩
      by_cases hzA : PA z
      · exact Or.inl ⟨hmA, hzA, hmin z ((hZ' z).2 ⟨hz, hzA⟩)⟩
      · exact Or.inr (Or.inl ⟨hmA, (hZ z hz).resolve_left hzA⟩)
    · have hB' : ∀ z, mem z Z → PB z := fun z hz =>
        (hZ z hz).resolve_left fun hzA => hne ⟨z, (hZ' z).2 ⟨hz, hzA⟩⟩
      obtain ⟨m, hm, hmin⟩ := hB.least Z ⟨z0, hz0⟩ hB'
      exact ⟨m, hm, fun z hz => Or.inr (Or.inr ⟨hB' m hm, hB' z hz, hmin z hz⟩)⟩

/-- The set of pairs `A ⊗ B`. -/
theorem prod_exists (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) (A B : V) :
    ∃ C, ∀ p, mem p C ↔ ∃ a b, mem a A ∧ mem b B ∧ p = kpair H a b := by
  obtain ⟨P1, hP1⟩ := hP (vcup H A B)
  obtain ⟨P2, hP2⟩ := hP P1
  obtain ⟨C, hC⟩ := sep_of H (fun p => ∃ a b, mem a A ∧ mem b B ∧ p = kpair H a b)
    (.ex 3 (.ex 4 (.and (.mem 3 1) (.and (.mem 4 2) (kpairF 0 3 4)))))
    (fun i => if i = 1 then A else B) (fun p => by
      simp only [NSat, nsat_kpairF H]
      simp (disch := omega) only [upd_same, upd_other]
      rfl) P2
  refine ⟨C, fun p => ⟨fun h => ((hC p).1 h).2, fun h => (hC p).2 ⟨?_, h⟩⟩⟩
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  exact ConstructibleAbs.kpair_mem_pp H hP1 hP2 ((vcup_spec H A B a).2 (Or.inl ha))
    ((vcup_spec H A B b).2 (Or.inr hb))

end Kit

end SetTheory.BusyBeaver.ZFC.InternalWO
