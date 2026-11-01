import BusyBeaver.ZFC.InternalWO

/-!
Transfinite recursion of end-extending well-orders.

A relation is read from the Kuratowski-pair members of a set `W`, reflexive
on its field `{x | ⟨x, x⟩ ∈ W}` (`IsWOS`). Nonpair members of `W` are ignored;
a consumer requiring a literal relation set must separately remove them. A stage operation of the shape

    G W = W ∪ (field W × N W) ∪ O W,

where `N W` is a set of new elements and `O W` a well-order of `N W`, appends
the new elements after the old ones. Every stage of the `TransRec` hierarchy
of such a `G` is then a well-order, and end-extends every earlier stage
(`stage_wos`): the union of a chain of end-extensions of well-orders is a
well-order. This supplies recursion machinery for future well-orders of
formula codes and the constructible hierarchy; neither concrete construction
is supplied here.
-/

namespace SetTheory.BusyBeaver.ZFC.OrderRec

open NamedZF NForm InternalOrd InternalRank TransRec InternalWO LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

section Defs

variable (H : ZFAxioms mem)

/-- `⟨x, y⟩ ∈ W`. -/
def Le (W x y : V) : Prop := mem (kpair H x y) W

/-- `x` is in the field of `W`. -/
def Fld (W x : V) : Prop := Le H W x x

/-- `W` is a reflexive well-order of its field. -/
structure IsWOS (W : V) : Prop where
  fld : ∀ x y, Le H W x y → Fld H W x ∧ Fld H W y
  antisymm : ∀ x y, Le H W x y → Le H W y x → x = y
  trans : ∀ x y z, Le H W x y → Le H W y z → Le H W x z
  total : ∀ x y, Fld H W x → Fld H W y → Le H W x y ∨ Le H W y x
  least : ∀ Z, (∃ z, mem z Z) → (∀ z, mem z Z → Fld H W z) →
    ∃ m, mem m Z ∧ ∀ z, mem z Z → Le H W m z

theorem IsWOS.wo {W : V} (h : IsWOS H W) : IsWO mem (Le H W) (Fld H W) :=
  ⟨fun _ hx => hx, fun x y _ _ => h.antisymm x y, fun x y z _ _ _ => h.trans x y z,
    h.total, h.least⟩

theorem isWOS_of_wo {W : V} (h : IsWO mem (Le H W) (Fld H W))
    (hf : ∀ x y, Le H W x y → Fld H W x ∧ Fld H W y) : IsWOS H W :=
  ⟨hf, fun x y hxy hyx => h.antisymm x y (hf x y hxy).1 (hf x y hxy).2 hxy hyx,
    fun x y z hxy hyz => h.trans x y z (hf x y hxy).1 (hf x y hxy).2 (hf y z hyz).2 hxy hyz,
    h.total, h.least⟩

/-- `B` end-extends `A`: `A` is `B` restricted to `A`'s field, and every element
of `B`'s field outside `A`'s field lies above all of `A`'s field. -/
def EndExt (A B : V) : Prop :=
  (∀ x y, Le H A x y ↔ (Le H B x y ∧ Fld H A x ∧ Fld H A y)) ∧
  (∀ x y, Fld H A x → Fld H B y → ¬ Fld H A y → Le H B x y)

theorem EndExt.fld {A B : V} (h : EndExt H A B) {x : V} (hx : Fld H A x) : Fld H B x :=
  ((h.1 x x).1 hx).1

theorem EndExt.refl (A : V) (hA : ∀ x y, Le H A x y → Fld H A x ∧ Fld H A y) : EndExt H A A :=
  ⟨fun x y => ⟨fun h => ⟨h, hA x y h⟩, fun h => h.1⟩, fun _ _ _ hy hny => absurd hy hny⟩

theorem EndExt.trans {A B C : V} (hAB : EndExt H A B) (hBC : EndExt H B C) :
    EndExt H A C := by
  refine ⟨fun x y => ?_, fun x y hx hy hny => ?_⟩
  · rw [hAB.1 x y, hBC.1 x y]
    exact ⟨fun ⟨⟨h, _, _⟩, hx, hy⟩ => ⟨h, hx, hy⟩,
      fun ⟨h, hx, hy⟩ => ⟨⟨h, hAB.fld H hx, hAB.fld H hy⟩, hx, hy⟩⟩
  · by_cases hyB : Fld H B y
    · exact (hBC.1 x y).1 (hAB.2 x y hx hyB hny) |>.1
    · exact hBC.2 x y (hAB.fld H hx) hy hyB

/-- Named formula for `IsWOS` (free name `w`). -/
def isWOSF (w : Nat) : NForm :=
  let n := w + 1
  .and (.all n (.all (n + 1) (.imp (pmemF w n (n + 1)) (.and (pmemF w n n) (pmemF w (n + 1) (n + 1))))))
  (.and (.all n (.all (n + 1) (.imp (pmemF w n (n + 1)) (.imp (pmemF w (n + 1) n) (.eq n (n + 1))))))
  (.and (.all n (.all (n + 1) (.all (n + 2) (.imp (pmemF w n (n + 1))
      (.imp (pmemF w (n + 1) (n + 2)) (pmemF w n (n + 2)))))))
  (.and (.all n (.all (n + 1) (.imp (pmemF w n n) (.imp (pmemF w (n + 1) (n + 1))
      (.or (pmemF w n (n + 1)) (pmemF w (n + 1) n))))))
  (.all n (.imp (.ex (n + 1) (.mem (n + 1) n)) (.imp (.all (n + 1) (.imp (.mem (n + 1) n)
      (pmemF w (n + 1) (n + 1)))) (.ex (n + 1) (.and (.mem (n + 1) n) (.all (n + 2)
        (.imp (.mem (n + 2) n) (pmemF w (n + 1) (n + 2))))))))))))

theorem nsat_isWOSF (ρ : Nat → V) (w : Nat) : NSat mem ρ (isWOSF w) ↔ IsWOS H (ρ w) := by
  simp only [isWOSF, NSat, nsat_pmemF H]
  simp (disch := omega) only [upd_same, upd_other]
  exact ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩⟩

/-- Named formula for `EndExt` (free names `a`, `b`). -/
def endExtF (a b : Nat) : NForm :=
  let n := a + b + 1
  .and (.all n (.all (n + 1) ((pmemF a n (n + 1)).iff (.and (pmemF b n (n + 1))
    (.and (pmemF a n n) (pmemF a (n + 1) (n + 1)))))))
  (.all n (.all (n + 1) (.imp (pmemF a n n) (.imp (pmemF b (n + 1) (n + 1))
    (.imp (.neg (pmemF a (n + 1) (n + 1))) (pmemF b n (n + 1)))))))

theorem nsat_endExtF (ρ : Nat → V) (a b : Nat) :
    NSat mem ρ (endExtF a b) ↔ EndExt H (ρ a) (ρ b) := by
  simp only [endExtF, NSat, nsat_iff, nsat_pmemF H, nsat_neg]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

end Defs

section Step

variable (H : ZFAxioms mem)

/-- The shape of an appending step operation. -/
structure AppendOp (G N O : V → V) : Prop where
  le_iff : ∀ W, IsWOS H W → ∀ x y, Le H (G W) x y ↔ Le H W x y ∨ (Fld H W x ∧ mem y (N W)) ∨ Le H (O W) x y
  new : ∀ W, IsWOS H W → ∀ y, mem y (N W) → ¬ Fld H W y
  wo : ∀ W, IsWOS H W → IsWO mem (Le H (O W)) (fun y => mem y (N W))
  ofld : ∀ W, IsWOS H W → ∀ x y, Le H (O W) x y → mem x (N W) ∧ mem y (N W)

variable {G N O : V → V} (hG : AppendOp H G N O)
include hG

theorem fld_step {W : V} (hW : IsWOS H W) (x : V) : Fld H (G W) x ↔ Fld H W x ∨ mem x (N W) := by
  unfold Fld
  rw [hG.le_iff W hW]
  constructor
  · rintro (h | ⟨_, h⟩ | h)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (hG.ofld W hW x x h).1
  · exact fun h => h.imp_right fun h => Or.inr ((hG.wo W hW).refl x h)

/-- **One step**: `G W` is a well-order end-extending `W`. -/
theorem step_wos {W : V} (hW : IsWOS H W) : IsWOS H (G W) ∧ EndExt H W (G W) := by
  have hwo := wo_append hW.wo (hG.wo W hW) (fun x hx hy => hG.new W hW x hy hx)
    (fun Z => sep_of H (fun z => Fld H W z) (pmemF 1 0 0) (fun _ => W)
      (fun z => by
        simp only [nsat_pmemF H]
        simp (disch := omega) only [upd_same, upd_other]
        rfl) Z)
  have hiff : ∀ x y, (Fld H W x ∨ mem x (N W)) → (Fld H W y ∨ mem y (N W)) →
      (((Fld H W x ∧ Fld H W y ∧ Le H W x y) ∨ (Fld H W x ∧ mem y (N W)) ∨
        (mem x (N W) ∧ mem y (N W) ∧ Le H (O W) x y)) ↔ Le H (G W) x y) := by
    intro x y _ _
    rw [hG.le_iff W hW]
    constructor
    · rintro (⟨-, -, h⟩ | h | ⟨-, -, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl ⟨(hW.fld x y h).1, (hW.fld x y h).2, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨(hG.ofld W hW x y h).1, (hG.ofld W hW x y h).2, h⟩)
  have hwo' : IsWO mem (Le H (G W)) (Fld H (G W)) :=
    (hwo.congr hiff).mono fun x hx => (fld_step H hG hW x).1 hx
  have hf : ∀ x y, Le H (G W) x y → Fld H (G W) x ∧ Fld H (G W) y := by
    intro x y h
    rw [fld_step H hG hW, fld_step H hG hW]
    rcases (hG.le_iff W hW x y).1 h with h | ⟨hx, hy⟩ | h
    · exact ⟨Or.inl (hW.fld x y h).1, Or.inl (hW.fld x y h).2⟩
    · exact ⟨Or.inl hx, Or.inr hy⟩
    · exact ⟨Or.inr (hG.ofld W hW x y h).1, Or.inr (hG.ofld W hW x y h).2⟩
  refine ⟨isWOS_of_wo H hwo' hf, fun x y => ?_, fun x y hx hy hny => ?_⟩
  · refine ⟨fun h => ⟨(hG.le_iff W hW x y).2 (Or.inl h), hW.fld x y h⟩, ?_⟩
    rintro ⟨h, hx, hy⟩
    rcases (hG.le_iff W hW x y).1 h with h | ⟨_, h⟩ | h
    · exact h
    · exact absurd hy (hG.new W hW y h)
    · exact absurd hx (hG.new W hW x (hG.ofld W hW x y h).1)
  · have hyN := ((fld_step H hG hW y).1 hy).resolve_left hny
    exact (hG.le_iff W hW x y).2 (Or.inr (Or.inl ⟨hx, hyN⟩))

end Step

section Recursion

variable (H : ZFAxioms mem) (hR : Regular mem) {G N O : V → V} (D : DefOp mem G)
  (hG : AppendOp H G N O)
include hR D hG

/-- **Every stage is a well-order end-extending the images of earlier stages.** -/
theorem stage_wos : ∀ a, Ord mem a → ∀ W, IsStage H G a W →
    IsWOS H W ∧ ∀ c Wc, mem c a → IsStage H G c Wc → EndExt H (G Wc) W := by
  refine ord_induction H hR _
    (.all 1 (.imp (isStageF D 0 1) (.and (isWOSF 1) (.all 2 (.all 3 (.imp (.mem 2 0)
      (.imp (isStageF D 2 3) (.ex 4 (.and (D.gF 4 3) (endExtF 4 1))))))))))
    (fun _ => vempty H) (fun a => by
      simp only [NSat, nsat_isStageF H D, nsat_isWOSF H, nsat_endExtF H, D.spec]
      simp (disch := omega) only [upd_same, upd_other]
      refine forall_congr' fun W => imp_congr_right fun _ => and_congr_right fun _ =>
        forall_congr' fun c => forall_congr' fun Wc => imp_congr_right fun _ =>
          imp_congr_right fun _ => ?_
      exact ⟨fun ⟨_, e, h⟩ => e ▸ h, fun h => ⟨_, rfl, h⟩⟩) ?_
  intro a ha IH W hW
  have hspec := stage_spec H hR D ha hW
  -- the images of earlier stages
  have hstage : ∀ c, mem c a → ∃ Wc, IsStage H G c Wc := fun c hc =>
    stage_exists' H hR D (ord_of_mem ha hc)
  have hwos : ∀ c Wc, mem c a → IsStage H G c Wc → IsWOS H Wc := fun c Wc hc h =>
    (IH c hc Wc h).1
  have hstepW : ∀ c Wc, mem c a → IsStage H G c Wc → IsWOS H (G Wc) ∧ EndExt H Wc (G Wc) :=
    fun c Wc hc h => step_wos H hG (hwos c Wc hc h)
  -- comparability of the images
  have hchain : ∀ c c' Wc Wc', mem c a → mem c' a → IsStage H G c Wc → IsStage H G c' Wc' →
      mem c c' → EndExt H (G Wc) (G Wc') := fun c c' Wc Wc' hc hc' h h' hcc' =>
    EndExt.trans H ((IH c' hc' Wc' h').2 c Wc hcc' h) (hstepW c' Wc' hc' h').2
  have hsame : ∀ c Wc Wc', mem c a → IsStage H G c Wc → IsStage H G c Wc' → Wc = Wc' :=
    fun c Wc Wc' hc h h' => stage_unique H hR (ord_of_mem ha hc) h h'
  have hle : ∀ x y, Le H W x y ↔ ∃ c Wc, mem c a ∧ IsStage H G c Wc ∧ Le H (G Wc) x y :=
    fun x y => hspec _
  -- any two images: the earlier one is end-extended by the later one
  have hcmp : ∀ c c' Wc Wc', mem c a → mem c' a → IsStage H G c Wc → IsStage H G c' Wc' →
      EndExt H (G Wc) (G Wc') ∨ EndExt H (G Wc') (G Wc) := by
    intro c c' Wc Wc' hc hc' h h'
    rcases trichotomy H hR c (ord_of_mem ha hc) c' (ord_of_mem ha hc') with e | rfl | e
    · exact Or.inl (hchain c c' Wc Wc' hc hc' h h' e)
    · rw [hsame c Wc Wc' hc h h']
      exact Or.inl (EndExt.refl H _ (hstepW c Wc' hc h').1.fld)
    · exact Or.inr (hchain c' c Wc' Wc hc' hc h' h e)
  have hfld : ∀ x, Fld H W x ↔ ∃ c Wc, mem c a ∧ IsStage H G c Wc ∧ Fld H (G Wc) x :=
    fun x => hle x x
  -- relations of `W` are read in any image containing both points
  have hread : ∀ c Wc x y, mem c a → IsStage H G c Wc → Fld H (G Wc) x → Fld H (G Wc) y →
      (Le H W x y ↔ Le H (G Wc) x y) := by
    intro c Wc x y hc h hx hy
    rw [hle]
    refine ⟨fun ⟨c', Wc', hc', h', hxy⟩ => ?_, fun hxy => ⟨c, Wc, hc, h, hxy⟩⟩
    rcases hcmp c c' Wc Wc' hc hc' h h' with e | e
    · exact (e.1 x y).2 ⟨hxy, hx, hy⟩
    · exact ((e.1 x y).1 hxy).1
  -- two images have a common upper image
  have hjoin : ∀ c c' Wc Wc', mem c a → mem c' a → IsStage H G c Wc → IsStage H G c' Wc' →
      ∃ d Wd, mem d a ∧ IsStage H G d Wd ∧ (∀ x, Fld H (G Wc) x → Fld H (G Wd) x) ∧
        (∀ x, Fld H (G Wc') x → Fld H (G Wd) x) := by
    intro c c' Wc Wc' hc hc' h h'
    rcases hcmp c c' Wc Wc' hc hc' h h' with e | e
    · exact ⟨c', Wc', hc', h', fun x hx => e.fld H hx, fun x hx => hx⟩
    · exact ⟨c, Wc, hc, h, fun x hx => hx, fun x hx => e.fld H hx⟩
  have hW' : IsWOS H W := by
    refine ⟨fun x y hxy => ?_, fun x y hxy hyx => ?_, fun x y z hxy hyz => ?_,
      fun x y hx hy => ?_, fun Z hne hZ => ?_⟩
    · obtain ⟨c, Wc, hc, h, hxy'⟩ := (hle x y).1 hxy
      have := (hstepW c Wc hc h).1.fld x y hxy'
      exact ⟨(hfld x).2 ⟨c, Wc, hc, h, this.1⟩, (hfld y).2 ⟨c, Wc, hc, h, this.2⟩⟩
    · obtain ⟨c, Wc, hc, h, hxy'⟩ := (hle x y).1 hxy
      have hf := (hstepW c Wc hc h).1.fld x y hxy'
      exact (hstepW c Wc hc h).1.antisymm x y hxy' ((hread c Wc y x hc h hf.2 hf.1).1 hyx)
    · obtain ⟨c, Wc, hc, h, hxy'⟩ := (hle x y).1 hxy
      obtain ⟨c', Wc', hc', h', hyz'⟩ := (hle y z).1 hyz
      obtain ⟨d, Wd, hd, hd', s1, s2⟩ := hjoin c c' Wc Wc' hc hc' h h'
      have f1 := (hstepW c Wc hc h).1.fld x y hxy'
      have f2 := (hstepW c' Wc' hc' h').1.fld y z hyz'
      have := (hstepW d Wd hd hd').1.trans x y z
        ((hread d Wd x y hd hd' (s1 x f1.1) (s1 y f1.2)).1 hxy)
        ((hread d Wd y z hd hd' (s2 y f2.1) (s2 z f2.2)).1 hyz)
      exact (hle x z).2 ⟨d, Wd, hd, hd', this⟩
    · obtain ⟨c, Wc, hc, h, hx'⟩ := (hfld x).1 hx
      obtain ⟨c', Wc', hc', h', hy'⟩ := (hfld y).1 hy
      obtain ⟨d, Wd, hd, hd', s1, s2⟩ := hjoin c c' Wc Wc' hc hc' h h'
      exact ((hstepW d Wd hd hd').1.total x y (s1 x hx') (s2 y hy')).imp
        (fun e => (hle x y).2 ⟨d, Wd, hd, hd', e⟩) fun e => (hle y x).2 ⟨d, Wd, hd, hd', e⟩
    · obtain ⟨z0, hz0⟩ := hne
      obtain ⟨c, Wc, hc, h, hz0'⟩ := (hfld z0).1 (hZ z0 hz0)
      obtain ⟨Z', hZ'⟩ := sep_of H (fun z => Fld H (G Wc) z) (pmemF 1 0 0) (fun _ => G Wc)
        (fun z => by
          simp only [nsat_pmemF H]
          simp (disch := omega) only [upd_same, upd_other]
          rfl) Z
      obtain ⟨m, hm, hmin⟩ := (hstepW c Wc hc h).1.least Z' ⟨z0, (hZ' z0).2 ⟨hz0, hz0'⟩⟩
        fun z hz => ((hZ' z).1 hz).2
      obtain ⟨hmZ, hmF⟩ := (hZ' m).1 hm
      refine ⟨m, hmZ, fun z hz => ?_⟩
      by_cases hzc : Fld H (G Wc) z
      · exact (hle m z).2 ⟨c, Wc, hc, h, hmin z ((hZ' z).2 ⟨hz, hzc⟩)⟩
      · obtain ⟨c', Wc', hc', h', hz'⟩ := (hfld z).1 (hZ z hz)
        rcases hcmp c c' Wc Wc' hc hc' h h' with e | e
        · exact (hle m z).2 ⟨c', Wc', hc', h', e.2 m z hmF hz' hzc⟩
        · exact absurd (e.fld H hz') hzc
  refine ⟨hW', fun c Wc hc h => ⟨fun x y => ?_, fun x y hx hy hny => ?_⟩⟩
  · exact ⟨fun hxy => ⟨(hle x y).2 ⟨c, Wc, hc, h, hxy⟩, (hstepW c Wc hc h).1.fld x y hxy⟩,
      fun ⟨hxy, hx, hy⟩ => (hread c Wc x y hc h hx hy).1 hxy⟩
  · obtain ⟨c', Wc', hc', h', hy'⟩ := (hfld y).1 hy
    rcases hcmp c c' Wc Wc' hc hc' h h' with e | e
    · exact (hle x y).2 ⟨c', Wc', hc', h', e.2 x y hx hy' hny⟩
    · exact absurd (e.fld H hy') hny

end Recursion

end SetTheory.BusyBeaver.ZFC.OrderRec
