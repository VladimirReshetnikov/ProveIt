import BusyBeaver.ZFC.CodeOrder

/-!
The lexicographic order of finite tuples, inside a model of ZF.

A tuple of length `n ∈ ω` over the field of a well-order `W` is an internal
function on `n` with values in that field (`IsTup`). Two tuples of the same
length are compared at their first difference (`LexN`). For every internal
`n`, nonstandard included, `LexN W n` well-orders the tuples of length `n`
(`wo_lexN`): totality, antisymmetry and transitivity come from the least
index of difference, and least elements by internal induction on `n`,
restricting a set of tuples of length `n + 1` to its length-`n` prefixes.
-/

namespace SetTheory.BusyBeaver.ZFC.TupleOrder

open NamedZF NForm InternalOrd InternalRank TransRec InternalWO OrderRec
  LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

section Defs

variable (H : ZFAxioms mem)

/-- `t` is a tuple of length `n` over the field of `W`. -/
def IsTup (W n t : V) : Prop :=
  IsFunctionOn H t n ∧ ∀ i y, mem (kpair H i y) t → Fld H W y

/-- Same-length lexicographic order, at the first difference. -/
def LexN (W n t t' : V) : Prop :=
  t = t' ∨ ∃ k u u', mem k n ∧ SatSupport.AgreeP H k t t' ∧ mem (kpair H k u) t ∧
    mem (kpair H k u') t' ∧ u ≠ u' ∧ Le H W u u'

def isTupF (w n t : Nat) : NForm :=
  let m := w + n + t + 1
  .and (.atom (fFunOnF 0 1) (ConstructibleDef.argsOf [t, n]))
    (.all m (.all (m + 1) (.imp (pmemF t m (m + 1)) (pmemF w (m + 1) (m + 1)))))

theorem nsat_isTupF (ρ : Nat → V) (w n t : Nat) :
    NSat mem ρ (isTupF w n t) ↔ IsTup H (ρ w) (ρ n) (ρ t) := by
  simp only [isTupF, NSat, nsat_pmemF H]
  rw [fFunOnF_spec H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

def lexNF (w n t t' : Nat) : NForm :=
  let m := w + n + t + t' + 1
  .or (.eq t t') (.ex m (.ex (m + 1) (.ex (m + 2) (.and (.mem m n) (.and (SatSupport.agreeF m t t')
    (.and (pmemF t m (m + 1)) (.and (pmemF t' m (m + 2)) (.and (.neg (.eq (m + 1) (m + 2)))
      (pmemF w (m + 1) (m + 2))))))))))

theorem nsat_lexNF (ρ : Nat → V) (w n t t' : Nat) :
    NSat mem ρ (lexNF w n t t') ↔ LexN H (ρ w) (ρ n) (ρ t) (ρ t') := by
  simp only [lexNF, NSat, nsat_neg, nsat_pmemF H, SatSupport.nsat_agreeF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

end Defs

section Tuples

variable (H : ZFAxioms mem) (hR : Regular mem) {W : V}

/-- Tuples that agree everywhere are equal. -/
theorem tup_ext {n t t' : V} (ht : IsTup H W n t) (ht' : IsTup H W n t')
    (h : SatSupport.AgreeP H n t t') : t = t' := by
  refine H.ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨i, u, hi, rfl⟩ := ht.1.2.2 p hp
    obtain ⟨u', hu'⟩ := ht'.1.2.1 i hi
    rwa [h i u u' hi hp hu']
  · obtain ⟨i, u, hi, rfl⟩ := ht'.1.2.2 p hp
    obtain ⟨u', hu'⟩ := ht.1.2.1 i hi
    rwa [← h i u' u hi hu' hp]

include hR

/-- Distinct tuples have a first difference. -/
theorem first_diff {n t t' : V} (hn : mem n (omegaV H)) (ht : IsTup H W n t)
    (ht' : IsTup H W n t') (hne : t ≠ t') :
    ∃ k u u', mem k n ∧ SatSupport.AgreeP H k t t' ∧ mem (kpair H k u) t ∧
      mem (kpair H k u') t' ∧ u ≠ u' := by
  obtain ⟨D, hD⟩ := sep_of H (fun k => ∃ u u', mem (kpair H k u) t ∧ mem (kpair H k u') t' ∧ u ≠ u')
    (.ex 3 (.ex 4 (.and (pmemF 1 0 3) (.and (pmemF 2 0 4) (.neg (.eq 3 4))))))
    (fun i => if i = 1 then t else t') (fun k => by
      simp only [NSat, nsat_neg, nsat_pmemF H]
      simp (disch := omega) only [upd_same, upd_other]
      rfl) n
  have hne' : ∃ k, mem k D := Classical.byContradiction fun hno =>
    hne (tup_ext H ht ht' fun i u u' hi hu hu' => Classical.byContradiction fun h =>
      hno ⟨i, (hD i).2 ⟨hi, u, u', hu, hu', h⟩⟩)
  obtain ⟨k, hk, hmin⟩ := (wo_nat H hR).least D hne' fun k hk =>
    ConstructibleZF.omega_trans H n hn k ((hD k).1 hk).1
  obtain ⟨hkn, u, u', hu, hu', huu⟩ := (hD k).1 hk
  refine ⟨k, u, u', hkn, fun i v v' hi hv hv' => Classical.byContradiction fun h => ?_, hu, hu',
    huu⟩
  rcases hmin i ((hD i).2 ⟨nat_transitive H n hn k hkn i hi, v, v', hv, hv', h⟩) with h' | rfl
  · exact mem_irrefl H hR k ((ord_of_mem (ConstructibleZF.ord_omega H)
      (ConstructibleZF.omega_trans H n hn k hkn)).1 i hi k h')
  · exact mem_irrefl H hR k hi

omit hR in
/-- The index of a first difference is unique. -/
theorem diff_index {n t t' k u u' k' v v' : V} (hn : mem n (omegaV H)) (hk : mem k n) (ha : SatSupport.AgreeP H k t t')
    (hu : mem (kpair H k u) t) (hu' : mem (kpair H k u') t') (huu : u ≠ u')
    (hk' : mem k' n) (ha' : SatSupport.AgreeP H k' t t') (hv : mem (kpair H k' v) t)
    (hv' : mem (kpair H k' v') t') (hvv : v ≠ v') : k = k' := by
  have hkω := ConstructibleZF.omega_trans H n hn k hk
  have hk'ω := ConstructibleZF.omega_trans H n hn k' hk'
  rcases nat_linear H k hkω k' hk'ω with h | h | h
  · exact absurd (ha' k u u' h hu hu') huu
  · exact h
  · exact absurd (ha k' v v' h hv hv') hvv

/-- **Lexicographic order of tuples of length `n` is total, antisymmetric and
transitive.** -/
theorem lexN_order (hW : IsWOS H W) {n : V} (hn : mem n (omegaV H)) :
    (∀ t t', IsTup H W n t → IsTup H W n t' → LexN H W n t t' ∨ LexN H W n t' t) ∧
    (∀ t t', IsTup H W n t → IsTup H W n t' → LexN H W n t t' → LexN H W n t' t → t = t') ∧
    (∀ t t' t'', IsTup H W n t → IsTup H W n t' → IsTup H W n t'' →
      LexN H W n t t' → LexN H W n t' t'' → LexN H W n t t'') := by
  have fval : ∀ t u u' i, IsTup H W n t → mem (kpair H i u) t → mem (kpair H i u') t → u = u' :=
    fun t u u' i ht h h' => ht.1.1 i u u' h h'
  refine ⟨fun t t' ht ht' => ?_, fun t t' ht ht' h1 h2 => ?_, fun t t' t'' ht ht' ht'' h1 h2 => ?_⟩
  · by_cases e : t = t'
    · exact Or.inl (Or.inl e)
    · obtain ⟨k, u, u', hk, ha, hu, hu', huu⟩ := first_diff H hR hn ht ht' e
      rcases hW.total u u' (ht.2 k u hu) (ht'.2 k u' hu') with h | h
      · exact Or.inl (Or.inr ⟨k, u, u', hk, ha, hu, hu', huu, h⟩)
      · exact Or.inr (Or.inr ⟨k, u', u, hk, fun i a b hi ha' hb => (ha i b a hi hb ha').symm,
          hu', hu, fun e => huu e.symm, h⟩)
  · rcases h1 with e | ⟨k, u, u', hk, ha, hu, hu', huu, hl⟩
    · exact e
    rcases h2 with e | ⟨k', v, v', hk', ha', hv, hv', hvv, hl'⟩
    · exact e.symm
    have hsym : SatSupport.AgreeP H k' t t' := fun i a b hi ha'' hb => (ha' i b a hi hb ha'').symm
    have e := diff_index H hn hk ha hu hu' huu hk' hsym hv' hv (fun e => hvv e.symm)
    subst e
    have e1 := fval t u v' k ht hu hv'
    have e2 := fval t' u' v k ht' hu' hv
    subst e1; subst e2
    exact absurd (hW.antisymm u u' hl hl') huu
  · rcases h1 with rfl | ⟨k, u, u', hk, ha, hu, hu', huu, hl⟩
    · exact h2
    rcases h2 with rfl | ⟨k', v, v', hk', ha', hv, hv', hvv, hl'⟩
    · exact Or.inr ⟨k, u, u', hk, ha, hu, hu', huu, hl⟩
    have hkω := ConstructibleZF.omega_trans H n hn k hk
    have hk'ω := ConstructibleZF.omega_trans H n hn k' hk'
    rcases nat_linear H k hkω k' hk'ω with h | rfl | h
    · -- the first difference of `t, t''` is at `k`
      obtain ⟨w, hw⟩ := ht''.1.2.1 k hk
      have e : u' = w := ha' k u' w h hu' hw
      subst e
      refine Or.inr ⟨k, u, u', hk, fun i a b hi hai hbi => ?_, hu, hw, huu, hl⟩
      obtain ⟨c, hc⟩ := ht'.1.2.1 i (nat_transitive H n hn k hk i hi)
      rw [ha i a c hi hai hc]
      exact ha' i c b (nat_transitive H k' hk'ω k h i hi) hc hbi
    · have e := fval t' u' v k ht' hu' hv
      subst e
      refine Or.inr ⟨k, u, v', hk, fun i a b hi hai hbi => ?_, hu, hv', fun e => ?_,
        hW.trans u u' v' hl hl'⟩
      · obtain ⟨c, hc⟩ := ht'.1.2.1 i (nat_transitive H n hn k hk i hi)
        rw [ha i a c hi hai hc]; exact ha' i c b hi hc hbi
      · subst e; exact huu (hW.antisymm u u' hl hl')
    · -- the first difference of `t, t''` is at `k'`
      obtain ⟨w, hw⟩ := ht.1.2.1 k' hk'
      have e : w = v := ha k' w v h hw hv
      subst e
      refine Or.inr ⟨k', w, v', hk', fun i a b hi hai hbi => ?_, hw, hv', hvv, hl'⟩
      obtain ⟨c, hc⟩ := ht'.1.2.1 i (nat_transitive H n hn k' hk' i hi)
      rw [ha i a c (nat_transitive H k hkω k' h i hi) hai hc]
      exact ha' i c b hi hc hbi

end Tuples

section Least

variable (H : ZFAxioms mem) (hR : Regular mem) {W : V}

theorem res_exists (t n : V) : ∃ s, ConstructibleAbs.IsRes H t n s :=
  sep_of H (fun p => ∃ i y, mem i n ∧ p = kpair H i y)
    (.ex 2 (.ex 3 (.and (.mem 2 1) (kpairF 0 2 3)))) (fun _ => n) (fun p => by
      simp only [NSat, nsat_kpairF H]
      simp (disch := omega) only [upd_same, upd_other]) t

theorem res_tup {n t s : V} (ht : IsTup H W (vsucc H n) t) (hs : ConstructibleAbs.IsRes H t n s) :
    IsTup H W n s := by
  refine ⟨⟨fun x y y' h h' => ht.1.1 x y y' ((hs _).1 h).1 ((hs _).1 h').1, fun i hi => ?_,
    fun p hp => ?_⟩, fun i y h => ht.2 i y ((hs _).1 h).1⟩
  · obtain ⟨y, hy⟩ := ht.1.2.1 i ((vsucc_spec H n i).2 (Or.inl hi))
    exact ⟨y, (hs _).2 ⟨hy, i, y, hi, rfl⟩⟩
  · obtain ⟨-, i, y, hi, rfl⟩ := (hs p).1 hp
    exact ⟨i, y, hi, rfl⟩

theorem res_unique {t n s s' : V} (hs : ConstructibleAbs.IsRes H t n s)
    (hs' : ConstructibleAbs.IsRes H t n s') : s = s' :=
  H.ext _ _ fun p => by rw [hs p, hs' p]

include hR

omit hR in
/-- **Least elements** for the lexicographic order of tuples of each length. -/
theorem lexN_least (hW : IsWOS H W) : ∀ n, mem n (omegaV H) → ∀ Z, (∃ z, mem z Z) →
    (∀ z, mem z Z → IsTup H W n z) → ∃ m, mem m Z ∧ ∀ z, mem z Z → LexN H W n m z := by
  let φ : NForm := .all 2 (.imp (.ex 3 (.mem 3 2)) (.imp (.all 3 (.imp (.mem 3 2) (isTupF 1 0 3)))
    (.ex 3 (.and (.mem 3 2) (.all 4 (.imp (.mem 4 2) (lexNF 1 0 3 4)))))))
  have hφ : ∀ n, Sat mem (scons n (fun _ => W)) (toForm id φ) ↔ ∀ Z, (∃ z, mem z Z) →
      (∀ z, mem z Z → IsTup H W n z) → ∃ m, mem m Z ∧ ∀ z, mem z Z → LexN H W n m z := by
    intro n
    rw [sat_toForm]
    simp only [φ, NSat, nsat_isTupF H, nsat_lexNF H]
    simp (disch := omega) only [upd_same, upd_other]
    rfl
  intro n hn
  refine (hφ n).1 (omega_ind H (toForm id φ) (fun _ => W) ((hφ _).2 ?_) (fun n hn ih => ?_) n hn)
  · -- length zero: the only tuple is empty
    intro Z ⟨z0, hz0⟩ hZ
    refine ⟨z0, hz0, fun z hz => Or.inl ?_⟩
    have hemp : ∀ t, IsTup H W (vempty H) t → ∀ p, ¬ mem p t := fun t ht p hp => by
      obtain ⟨i, y, hi, -⟩ := ht.1.2.2 p hp
      exact vempty_spec H i hi
    exact H.ext _ _ fun p => ⟨fun h => absurd h (hemp z0 (hZ z0 hz0) p),
      fun h => absurd h (hemp z (hZ z hz) p)⟩
  · have IH := (hφ n).1 ih
    refine (hφ _).2 ?_
    intro Z ⟨z0, hz0⟩ hZ
    -- prefixes
    obtain ⟨Z', hZ'⟩ := repl_of H (fun t s => ConstructibleAbs.IsRes H t n s)
      (.all 3 ((NForm.mem 3 0).iff (.and (.mem 3 1) (.ex 4 (.ex 5 (.and (.mem 4 2)
        (kpairF 3 4 5)))))))
      (fun _ => n) (fun t s => by
        simp only [NSat, nsat_iff, nsat_kpairF H]
        simp (disch := omega) only [upd_same, upd_other]
        rfl)
      (fun t s s' h h' => res_unique H h h') Z
    have hZ'tup : ∀ s, mem s Z' → IsTup H W n s := fun s hs => by
      obtain ⟨t, ht, hts⟩ := (hZ' s).1 hs
      exact res_tup H (hZ t ht) hts
    obtain ⟨s0, hs0⟩ := res_exists H z0 n
    obtain ⟨m', hm', hm'min⟩ := IH Z' ⟨s0, (hZ' s0).2 ⟨z0, hz0, hs0⟩⟩ hZ'tup
    -- tuples with the least prefix
    obtain ⟨Z'', hZ''⟩ := sep_of H (fun t => ConstructibleAbs.IsRes H t n m')
      (.all 3 ((NForm.mem 3 2).iff (.and (.mem 3 0) (.ex 4 (.ex 5 (.and (.mem 4 1)
        (kpairF 3 4 5)))))))
      (fun i => if i = 1 then n else m') (fun t => by
        simp only [NSat, nsat_iff, nsat_kpairF H]
        simp (disch := omega) only [upd_same, upd_other]
        rfl) Z
    -- their last values
    have hnn : mem n (vsucc H n) := vsucc_self H n
    obtain ⟨Vals, hVals⟩ := sep_of H (fun v => ∃ t, mem t Z'' ∧ mem (kpair H n v) t)
      (.ex 2 (.and (.mem 2 1) (pmemF 2 3 0))) (fun i => if i = 1 then Z'' else n)
      (fun v => by
        simp only [NSat, nsat_pmemF H]
        simp (disch := omega) only [upd_same, upd_other]
        rfl) (vunion H (vunion H (vunion H Z'')))
    have hValsIff : ∀ v, mem v Vals ↔ ∃ t, mem t Z'' ∧ mem (kpair H n v) t := fun v => by
      rw [hVals v]
      refine ⟨fun h => h.2, fun ⟨t, ht, hv⟩ => ⟨?_, t, ht, hv⟩⟩
      have h1 : mem (kpair H n v) (vunion H Z'') := (vunion_spec H _ _).2 ⟨t, hv, ht⟩
      have h2 : mem (vpair H n v) (vunion H (vunion H Z'')) :=
        (vunion_spec H _ _).2 ⟨_, (kpair_mem H n v _).2 (Or.inr rfl), h1⟩
      exact (vunion_spec H _ v).2 ⟨_, (vpair_spec H n v v).2 (Or.inr rfl), h2⟩
    obtain ⟨t0, ht0, ht0m⟩ := (hZ' m').1 hm'
    obtain ⟨w0, hw0⟩ := (hZ t0 ht0).1.2.1 n hnn
    obtain ⟨v0, hv0, hv0min⟩ := hW.least Vals
      ⟨w0, (hValsIff w0).2 ⟨t0, (hZ'' t0).2 ⟨ht0, ht0m⟩, hw0⟩⟩
      fun v hv => by
        obtain ⟨t, ht, htv⟩ := (hValsIff v).1 hv
        exact (hZ t ((hZ'' t).1 ht).1).2 n v htv
    obtain ⟨m, hm, hmv⟩ := (hValsIff v0).1 hv0
    obtain ⟨hmZ, hmres⟩ := (hZ'' m).1 hm
    refine ⟨m, hmZ, fun z hz => ?_⟩
    have htm := hZ m hmZ
    have htz := hZ z hz
    obtain ⟨s, hs⟩ := res_exists H z n
    have hsZ' : mem s Z' := (hZ' s).2 ⟨z, hz, hs⟩
    -- agreement below `n` of two tuples with the same prefix
    have agree_pre : ∀ {a b : V}, mem a Z → mem b Z → ConstructibleAbs.IsRes H a n m' →
        ConstructibleAbs.IsRes H b n m' → SatSupport.AgreeP H n a b := by
      intro a b _ _ ha hb i x y hi hx hy
      exact (hZ'tup m' hm').1.1 i x y ((ha _).2 ⟨hx, i, x, hi, rfl⟩) ((hb _).2 ⟨hy, i, y, hi, rfl⟩)
    rcases hm'min s hsZ' with e | ⟨k, u, u', hk, ha, hu, hu', huu, hl⟩
    · subst e
      obtain ⟨w, hw⟩ := htz.1.2.1 n hnn
      have hle := hv0min w ((hValsIff w).2 ⟨z, (hZ'' z).2 ⟨hz, hs⟩, hw⟩)
      have hag := agree_pre hmZ hz hmres hs
      by_cases e : v0 = w
      · subst e
        refine Or.inl (tup_ext H htm htz fun i x y hi hx hy => ?_)
        rcases (vsucc_spec H n i).1 hi with hi | rfl
        · exact hag i x y hi hx hy
        · rw [htm.1.1 i x v0 hx hmv, htz.1.1 i y v0 hy hw]
      · exact Or.inr ⟨n, v0, w, hnn, hag, hmv, hw, e, hle⟩
    · have hum : mem (kpair H k u) m := ((hmres _).1 hu).1
      have huz : mem (kpair H k u') z := ((hs _).1 hu').1
      refine Or.inr ⟨k, u, u', (vsucc_spec H n k).2 (Or.inl hk), fun i x y hi hx hy => ?_,
        hum, huz, huu, hl⟩
      have hin := nat_transitive H n hn k hk i hi
      exact ha i x y hi ((hmres _).2 ⟨hx, i, x, hin, rfl⟩) ((hs _).2 ⟨hy, i, y, hin, rfl⟩)

/-- **`LexN W n` well-orders the tuples of length `n`.** -/
theorem wo_lexN (hW : IsWOS H W) {n : V} (hn : mem n (omegaV H)) :
    IsWO mem (LexN H W n) (IsTup H W n) := by
  obtain ⟨htot, hanti, htrans⟩ := lexN_order H hR hW hn
  exact ⟨fun _ _ => Or.inl rfl, hanti, htrans, htot, lexN_least H hW n hn⟩

end Least

end SetTheory.BusyBeaver.ZFC.TupleOrder
