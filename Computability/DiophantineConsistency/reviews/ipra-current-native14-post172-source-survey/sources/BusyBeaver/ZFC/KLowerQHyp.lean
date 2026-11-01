import BusyBeaver.ZFC.KLowerEqv
import BusyBeaver.ZFC.KQ1Model
import BusyBeaver.ZFC.KQ1ZF

/-!
The tagged domain of a seed model satisfies the quotient interface `KQHyp.QHyp`
(Elliot Glazer's `KQuotUnion`, `KQuotPower`, `KQuotInfinity`, semantically).

* union: exact union in `D_t`, read up to `Eqv`;
* power: the separations of a tagged `a` over one fixed envelope `E` are raw subsets of a transitive
  set `v ∋ E, a`; the tagged members of `Pow(v)` whose tagged members lie in `a` represent every
  interpreted subset of `a` up to `Eqv` (`tag_power_member`);
* singleton-closed containers: a seed whose images are tagged singletons of tagged singletons, so
  that the tagged singleton of every collected element is a member of a member of the container
  (`tag_singleton_closed`).
-/

namespace SetTheory.BusyBeaver.ZFC.KLower

open Form Profile ProfilePairs ProfileCollection ProfileComposition ProfileAxioms
open SetTheory.BusyBeaver.ZFC.KSeed222

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- `v` is a tagged singleton of `x`: its members are some `{x}`, the marker `t`, and `x`. -/
def IsTSing (mem : V → V → Prop) (t x v : V) : Prop :=
  ∃ B, IsSing mem B x ∧ ∀ w, mem w v ↔ w = B ∨ w = t ∨ w = x

/-- Inside a matrix: slot `vi` is a tagged singleton of slot `xi`, marker in slot `ti`. -/
def tsingF (xi vi ti : Nat) : Form :=
  fEx (fAnd (singF 0 (xi + 1))
    (fAll (fIff (fMem 0 (vi + 2)) (fOr (fEq 0 1) (fOr (fEq 0 (ti + 2)) (fEq 0 (xi + 2)))))))

theorem sat_tsingF (env : Nat → V) (xi vi ti : Nat) :
    Sat mem env (tsingF xi vi ti) ↔ IsTSing mem (env ti) (env xi) (env vi) := by
  refine exists_congr fun B => and_congr (sat_singF _ 0 (xi + 1)) ?_
  exact forall_congr' fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Read a tagged-domain formula in one tagged free variable as a raw formula in slot 0. -/
theorem tag_formula {t : V} (φ : Form) (env : Nat → Tag mem t) (z : Tag mem t) :
    Sat mem (scons z.1 (scons t (fun i => (env i).1))) (rename swap01 (relT 0 φ)) ↔
      Sat (tmem mem t) (scons z env) φ := by
  rw [sat_top]
  exact Sat_rename_ext _ _ _ _ fun n => by rcases n with _ | _ | _ <;> rfl

section QHyp

variable (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) {t : V} (ht : ∀ z, ¬ mem z t)
include hs hirr ht

/-! ### Tagged singletons -/

theorem tsing_tagged {x v : V} (hv : IsTSing mem t x v) : mem t v := by
  obtain ⟨_, -, hv⟩ := hv
  exact (hv t).mpr (Or.inr (Or.inl rfl))

theorem tsing_members {x v : V} (hx : mem t x) (hv : IsTSing mem t x v) (z : V) (hz : mem t z) :
    mem z v ↔ z = x := by
  obtain ⟨B, hB, hv⟩ := hv
  rw [hv z]
  constructor
  · rintro (h | h | h)
    · subst h; exact absurd ((hB t).mp hz ▸ hx) (hirr t)
    · subst h; exact absurd hz (hirr z)
    · exact h
  · exact fun h => Or.inr (Or.inr h)

theorem tsing_exists (x : V) : ∃ v, IsTSing mem t x v := by
  obtain ⟨B, hB⟩ := raw_singleton hs x
  have hBt : B ≠ t := fun e => ht x (e ▸ (hB x).mpr rfl)
  obtain ⟨S, hS⟩ := raw_tagged hs hirr ht B hBt (fEq 0 0) (fun _ => t)
  exact ⟨S, B, hB, fun w => (hS w).trans (or_congr Iff.rfl (or_congr Iff.rfl
    ⟨fun h => (hB w).mp h.1, fun h => ⟨(hB w).mpr h, rfl⟩⟩))⟩

/-! ### Union -/

theorem tag_union_member (a : Tag mem t) :
    ∃ b, ∀ z, Member (tmem mem t) z b ↔ ∃ x, Member (tmem mem t) x a ∧ Member (tmem mem t) z x := by
  obtain ⟨w, hw⟩ := tag_union hs hirr ht a
  refine ⟨w, fun z => ⟨fun ⟨u, huw, hzu⟩ => ?_, fun ⟨x, hxa, hzx⟩ => ?_⟩⟩
  · obtain ⟨y, huy, hya⟩ := (hw u).mp huw
    exact ⟨y, member_raw hs hirr ht hya, u, huy, hzu⟩
  · obtain ⟨y, hya, hxy⟩ := hxa
    obtain ⟨u, hux, hzu⟩ := hzx
    obtain ⟨u', hu'y, huu'⟩ := member_right hs hirr ht hxy (member_raw hs hirr ht hux)
    exact ⟨u', (hw u').mpr ⟨y, hu'y, hya⟩, tag_trans hs hirr ht hzu huu'⟩

/-! ### Power -/

/-- Comprehension over `U` with a prescribed envelope `E`; the result's raw members are `E`, `t`
and members of `U`. -/
theorem dt_comp_env (U E : V) (hEt : E ≠ t) (htE : ¬ mem t E)
    (hUE : ∀ z, mem t z → mem z U → mem z E) (θ : Form) (ρ : Nat → V) :
    ∃ S, mem t S ∧ (∀ w, mem w S → w = E ∨ w = t ∨ mem w U) ∧
      ∀ z, mem t z → (mem z S ↔ mem z U ∧ Sat mem (scons z ρ) θ) := by
  have hθ : ∀ z, Sat mem (scons z (scons U ρ)) (rename (shiftAfter 0) θ) ↔ Sat mem (scons z ρ) θ :=
    fun z => Sat_rename_ext θ _ _ _ fun n => by cases n <;> rfl
  obtain ⟨S, hS⟩ := raw_tagged hs hirr ht E hEt (fAnd (fMem 0 1) (rename (shiftAfter 0) θ))
    (scons U ρ)
  refine ⟨S, (hS t).mpr (Or.inr (Or.inl rfl)), fun w hw => ?_, fun z hz => ?_⟩
  · exact ((hS w).mp hw).imp_right (Or.imp_right fun h => h.2.1)
  · have hzE : z ≠ E := fun e => htE (e ▸ hz)
    have hzt : z ≠ t := fun e => hirr t (e ▸ hz)
    rw [hS z]
    constructor
    · rintro (h | h | ⟨-, hzU, hθz⟩)
      · exact absurd h hzE
      · exact absurd h hzt
      · exact ⟨hzU, (hθ z).mp hθz⟩
    · rintro ⟨hzU, hθz⟩
      exact Or.inr (Or.inr ⟨hUE z hz hzU, hzU, (hθ z).mpr hθz⟩)

/-- An untagged envelope of a tagged set. -/
theorem envelope (a : V) (ha : mem t a) :
    ∃ E, E ≠ t ∧ ¬ mem t E ∧ ∀ z, mem t z → mem z a → mem z E := by
  obtain ⟨E, hE⟩ := raw_aug hs hirr a (fMem 1 0) (scons t (fun _ => t))
  have hat : a ≠ t := fun e => hirr t (e ▸ ha)
  refine ⟨E, fun e => ht a (e ▸ (hE a).mpr (Or.inl rfl)), fun h => ?_,
    fun z hz hza => (hE z).mpr (Or.inr ⟨hza, hz⟩)⟩
  rcases (hE t).mp h with h | ⟨-, h⟩
  · exact hat h.symm
  · exact hirr t h

theorem tag_power_member (a : Tag mem t) :
    ∃ p, ∀ x, Member (tmem mem t) x p ↔ InterpretedSub (tmem mem t) x a := by
  obtain ⟨E, hEt, htE, hEa⟩ := envelope hs hirr ht a.1 a.2
  obtain ⟨P, hP⟩ := raw_pair hs ht E a.1
  obtain ⟨v, hPv, hv⟩ := raw_transitive hs P
  have hEv : mem E v := hv P hPv E ((hP E).mpr (Or.inl rfl))
  have hav : mem a.1 v := hv P hPv a.1 ((hP a.1).mpr (Or.inr rfl))
  obtain ⟨W, hW⟩ := raw_power hs hirr v
  -- the tagged members of `Pow(v)` whose tagged members lie in `a`
  obtain ⟨p, hp⟩ := tag_of_bound hs hirr ht W
    (fun z => mem z.1 W ∧ ∀ w, mem t w → mem w z.1 → mem w a.1)
    (fAll (fImp (fMem 2 0) (fImp (fMem 0 1) (fMem 0 3)))) (scons t (scons a.1 (fun _ => t)))
    (fun z => Iff.rfl)
  refine ⟨p, fun x => ⟨fun ⟨u, hup, hxu⟩ z hz => ?_, fun hsub => ?_⟩⟩
  · obtain ⟨w, hwu, hzw⟩ := member_right hs hirr ht hxu hz
    exact ⟨w, ((hp u).mp hup).2 w.1 w.2 hwu, hzw⟩
  · -- the clean representative: the separation of `a` by `· ∈ x`, over the envelope `E`
    obtain ⟨S, htS, hSraw, hS⟩ := dt_comp_env hs hirr ht a.1 E hEt htE hEa
      (rename swap01 (relT 0 (KQ1Model.memberForm 0 1))) (scons t (fun _ => x.1))
    have hSm : ∀ z : Tag mem t, tmem mem t z ⟨S, htS⟩ ↔ tmem mem t z a ∧ Member (tmem mem t) z x :=
      fun z => (hS z.1 z.2).trans (and_congr Iff.rfl ((tag_formula _ (fun _ => x) z).trans
        (KQ1Model.sat_memberForm _ _ 0 1)))
    have hSW : mem S W := (hW S).mpr fun w hw => by
      rcases hSraw w hw with rfl | rfl | h
      · exact hEv
      · exact hv a.1 hav w a.2
      · exact hv a.1 hav w h
    have hSp : tmem mem t ⟨S, htS⟩ p :=
      (hp ⟨S, htS⟩).mpr ⟨hSW, fun w hw hwS => ((hSm ⟨w, hw⟩).mp hwS).1⟩
    refine ⟨⟨S, htS⟩, hSp, tag_ext hs hirr ht _ _ fun z => ⟨fun hz => ?_, fun ⟨w, hwS, hzw⟩ => ?_⟩⟩
    · obtain ⟨w, hwa, hzw⟩ := hsub z hz
      exact ⟨w, (hSm w).mpr ⟨hwa, member_left hs hirr ht hzw hz⟩, hzw⟩
    · exact member_left hs hirr ht (tag_symm hs hirr ht hzw) ((hSm w).mp hwS).2

/-! ### Singleton-closed containers -/

theorem tag_singleton_closed (r : Tag mem t) :
    ∃ Y, Member (tmem mem t) r Y ∧ ∀ x, Member (tmem mem t) x Y →
      ∃ s, Member (tmem mem t) s Y ∧ ∀ z, Member (tmem mem t) z s ↔ Eqv (tmem mem t) z x := by
  -- images: from the empty root, a tagged singleton of `r`; from `{x}` with `x` tagged, a tagged
  -- singleton of a tagged singleton of `x`
  let env : Nat → V := scons t (scons r.1 (fun _ => t))
  obtain ⟨C, h1, h2⟩ := hs (fOr (fAnd (fEq 1 2) (tsingF 3 0 2))
    (fEx (fAnd (fMem 3 0) (fAnd (singF 2 0) (fEx (fAnd (tsingF 1 0 4) (tsingF 0 2 4))))))) env t
  have hts : ∀ v, ¬ IsSing mem t v := fun v hv => ht v ((hv v).mpr rfl)
  -- every collected element has a collected tagged singleton
  have hstep : ∀ w z, mem w C → mem z w → mem t z → ∃ v w', IsTSing mem t z v ∧ mem v w' ∧ mem w' C := by
    intro w z hwC hzw hz
    obtain ⟨_, -, hcl⟩ := h2 w hwC
    obtain ⟨sz, hsz⟩ := raw_singleton hs z
    obtain ⟨v, hv⟩ := tsing_exists hs hirr ht z
    obtain ⟨w', hw'⟩ := tsing_exists hs hirr ht v
    obtain ⟨w'', hw'', hw''C⟩ := hcl sz (fun u hu => ((hsz u).mp hu) ▸ hzw) w'
      (Or.inr ⟨z, hz, (sat_singF _ 2 0).mpr hsz, v, (sat_tsingF _ 1 0 4).mpr hv,
        (sat_tsingF _ 0 2 4).mpr hw'⟩)
    rcases hw'' with ⟨h, -⟩ | ⟨x', -, hx', v', hv', hw'''⟩
    · exact (hts z ((show sz = t from h) ▸ hsz)).elim
    · have hx'z : x' = z := ((sat_singF _ 2 0).mp hx').unique hsz
      subst hx'z
      have hv'' := (sat_tsingF _ 1 0 4).mp hv'
      have hw4 := (sat_tsingF _ 0 2 4).mp hw'''
      obtain ⟨_, -, hw5⟩ := hw4
      exact ⟨v', w'', hv'', (hw5 v').mpr (Or.inr (Or.inr rfl)), hw''C⟩
  -- the root's image is a tagged singleton of `r`
  obtain ⟨w0, hw0⟩ := tsing_exists hs hirr ht r.1
  obtain ⟨w1, hw1, hw1C⟩ := h1 w0 (Or.inl ⟨rfl, (sat_tsingF _ 3 0 2).mpr hw0⟩)
  have hrw1 : mem r.1 w1 := by
    rcases hw1 with ⟨-, h⟩ | ⟨x', hx', hs', -⟩
    · obtain ⟨_, -, h⟩ := (sat_tsingF _ 3 0 2).mp h
      exact (h r.1).mpr (Or.inr (Or.inr rfl))
    · exact (hts x' ((sat_singF _ 2 0).mp hs')).elim
  -- Y: the tagged members of members of C, and r
  obtain ⟨P, hP⟩ := raw_pair hs ht C r.1
  obtain ⟨U, hPU, hU⟩ := raw_transitive hs P
  have hCU : mem C U := hU P hPU C ((hP C).mpr (Or.inl rfl))
  obtain ⟨Y, hY⟩ := tag_of_bound hs hirr ht U
    (fun z => mem z.1 U ∧ (z.1 = r.1 ∨ ∃ w, mem w C ∧ mem z.1 w))
    (fOr (fEq 0 1) (fEx (fAnd (fMem 0 3) (fMem 1 0)))) (scons r.1 (scons C (fun _ => t)))
    (fun z => Iff.rfl)
  have hYm : ∀ z : Tag mem t, (z.1 = r.1 ∨ ∃ w, mem w C ∧ mem z.1 w) → tmem mem t z Y := by
    intro z hz
    refine (hY z).mpr ⟨?_, hz⟩
    rcases hz with h | ⟨w, hwC, hzw⟩
    · rw [h]; exact hU P hPU r.1 ((hP r.1).mpr (Or.inr rfl))
    · exact hU w (hU C hCU w hwC) z.1 hzw
  refine ⟨Y, member_raw hs hirr ht (hYm r (Or.inl rfl)), fun x ⟨u, huY, hxu⟩ => ?_⟩
  -- a collected tagged singleton of `u`
  have hu := ((hY u).mp huY).2
  obtain ⟨v, w', hv, hvw', hw'C⟩ : ∃ v w', IsTSing mem t u.1 v ∧ mem v w' ∧ mem w' C := by
    rcases hu with h | ⟨w, hwC, huw⟩
    · exact hstep w1 u.1 hw1C (h ▸ hrw1) u.2
    · exact hstep w u.1 hwC huw u.2
  have htv : mem t v := tsing_tagged hs hirr ht hv
  refine ⟨⟨v, htv⟩, member_raw hs hirr ht (hYm ⟨v, htv⟩ (Or.inr ⟨w', hw'C, hvw'⟩)), fun z => ?_⟩
  constructor
  · rintro ⟨w, hwv, hzw⟩
    have : w = u := Subtype.ext ((tsing_members hs hirr ht u.2 hv w.1 w.2).mp hwv)
    subst this
    exact tag_trans hs hirr ht hzw (tag_symm hs hirr ht hxu)
  · intro hzx
    exact ⟨u, (tsing_members hs hirr ht u.2 hv u.1 u.2).mpr rfl, tag_trans hs hirr ht hzx hxu⟩

/-- **The tagged domain satisfies the quotient interface.** -/
theorem tag_qhyp : KQHyp.QHyp (tmem mem t) where
  gic := tag_gic hs hirr ht
  refl := tag_refl hs hirr ht
  symm := tag_symm hs hirr ht
  trans := tag_trans hs hirr ht
  ext := tag_ext hs hirr ht
  pairs := tag_pairs hs hirr ht
  union := tag_union_member hs hirr ht
  power := tag_power_member hs hirr ht
  singleton := tag_singleton_closed hs hirr ht

end QHyp

/-- **A full seed model refutes no ZF proof of falsity.** -/
theorem zf_consistent_of_formSeed (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) (w : V) :
    ¬ BProv ZFax_s [] Form.fBot := by
  obtain ⟨t, ht⟩ := raw_empty hs w
  obtain ⟨x, hx⟩ := tag_inhabited hs hirr ht
  exact KQ1ZF.zf_consistent (tmem mem t) ⟨x, hx⟩ (tag_qhyp hs hirr ht)

end SetTheory.BusyBeaver.ZFC.KLower
