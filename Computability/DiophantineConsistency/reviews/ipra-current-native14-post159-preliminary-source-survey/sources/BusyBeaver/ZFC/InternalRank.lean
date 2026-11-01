import BusyBeaver.ZFC.InternalOrd

/-!
The cumulative hierarchy inside an arbitrary model of ZF with Foundation.

`V_β = {z | z ⊆ V_γ for some γ ∈ β}` is built by transfinite recursion on
the internal ordinals, for any definable relation `R z T` in place of `z ⊆ T`
(`TransRec` takes `z ∈ G T`). An *approximation* on an ordinal `d` is a set of
Kuratowski pairs `⟨β, S⟩`, one for each `β ∈ d`, obeying that recursion
(`RApprox`). Approximations agree where both are defined (`rapprox_unique`,
by ordinal induction), every ordinal carries one (`rapprox_exists`: extend
by one stage, then glue the approximations of the successors below by
Replacement), and the stages are read off them (`RStage`; `IsV` for `R = Sub`).
-/

namespace SetTheory.BusyBeaver.ZFC.InternalRank

open NamedZF NForm InternalOrd

universe u
variable {V : Type u} {mem : V → V → Prop}

/-! ## Formulas for subsets, pairs and power sets -/

/-- `z ⊆ t`. -/
def subF (z t : Nat) : NForm := .all (z + t + 1) (.imp (.mem (z + t + 1) z) (.mem (z + t + 1) t))

theorem nsat_subF (ρ : Nat → V) (z t : Nat) : NSat mem ρ (subF z t) ↔ Sub mem (ρ z) (ρ t) := by
  simp (disch := omega) only [subF, NSat, upd_same, upd_other]
  rfl

/-- `s = {x}`. -/
def singF (s x : Nat) : NForm := .all (s + x + 1) ((NForm.mem (s + x + 1) s).iff (.eq (s + x + 1) x))

/-- `p = {x, y}`. -/
def upairF (p x y : Nat) : NForm :=
  .all (p + x + y + 1)
    ((NForm.mem (p + x + y + 1) p).iff (.or (.eq (p + x + y + 1) x) (.eq (p + x + y + 1) y)))

/-- `p = ⟨x, y⟩ = {{x}, {x, y}}`. -/
def kpairF (p x y : Nat) : NForm :=
  .all (p + x + y + 1)
    ((NForm.mem (p + x + y + 1) p).iff (.or (singF (p + x + y + 1) x) (upairF (p + x + y + 1) x y)))

/-- `⟨x, y⟩ ∈ f`. -/
def pmemF (f x y : Nat) : NForm :=
  .ex (f + x + y + 1) (.and (kpairF (f + x + y + 1) x y) (.mem (f + x + y + 1) f))

/-- `y` is the power set of `t`. -/
def powF (y t : Nat) : NForm := .all (y + t + 1) ((NForm.mem (y + t + 1) y).iff (subF (y + t + 1) t))

section Pairs

variable (H : ZFAxioms mem)

theorem nsat_singF (ρ : Nat → V) (s x : Nat) : NSat mem ρ (singF s x) ↔ ρ s = vsingle H (ρ x) := by
  simp (disch := omega) only [singF, NSat, nsat_iff, upd_same, upd_other]
  exact ⟨fun h => H.ext _ _ fun d => (h d).trans (vsingle_spec H _ d).symm,
    fun h d => by rw [h]; exact vsingle_spec H _ d⟩

theorem nsat_upairF (ρ : Nat → V) (p x y : Nat) :
    NSat mem ρ (upairF p x y) ↔ ρ p = vpair H (ρ x) (ρ y) := by
  simp (disch := omega) only [upairF, NSat, nsat_iff, upd_same, upd_other]
  exact ⟨fun h => H.ext _ _ fun d => (h d).trans (vpair_spec H _ _ d).symm,
    fun h d => by rw [h]; exact vpair_spec H _ _ d⟩

theorem nsat_kpairF (ρ : Nat → V) (p x y : Nat) :
    NSat mem ρ (kpairF p x y) ↔ ρ p = kpair H (ρ x) (ρ y) := by
  simp only [kpairF, NSat, nsat_iff, nsat_singF H, nsat_upairF H]
  simp (disch := omega) only [upd_same, upd_other]
  exact ⟨fun h => H.ext _ _ fun d => (h d).trans (kpair_mem H _ _ d).symm,
    fun h d => by rw [h]; exact kpair_mem H _ _ d⟩

theorem nsat_pmemF (ρ : Nat → V) (f x y : Nat) :
    NSat mem ρ (pmemF f x y) ↔ mem (kpair H (ρ x) (ρ y)) (ρ f) := by
  simp only [pmemF, NSat, nsat_kpairF H]
  simp (disch := omega) only [upd_same, upd_other]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

end Pairs

/-! ## Recursion along the ordinals

The development is generic in the relation `R z T` ("`z` enters a stage from the earlier
stage `T`"), named by a formula `rF`: `Sub` gives the cumulative hierarchy below, and
`TransRec` takes `z ∈ G T` for a definable operation `G`. -/

variable {R : V → V → Prop} {rF : Nat → Nat → NForm}

/-- `rF` names `R`. -/
abbrev RDef (mem : V → V → Prop) (R : V → V → Prop) (rF : Nat → Nat → NForm) : Prop :=
  ∀ (ρ : Nat → V) (z t : Nat), NSat mem ρ (rF z t) ↔ R (ρ z) (ρ t)

/-- Every class `{z | R z T}` is a set. -/
abbrev RSets (mem : V → V → Prop) (R : V → V → Prop) : Prop := ∀ T, ∃ P, ∀ z, mem z P ↔ R z T

/-- `y = {z | R z t}`. -/
def classF (rF : Nat → Nat → NForm) (y t : Nat) : NForm :=
  .all (y + t + 1) ((NForm.mem (y + t + 1) y).iff (rF (y + t + 1) t))

theorem nsat_classF (hrF : RDef mem R rF) (ρ : Nat → V) (y t : Nat) :
    NSat mem ρ (classF rF y t) ↔ ∀ z, mem z (ρ y) ↔ R z (ρ t) := by
  simp only [classF, NSat, nsat_iff, hrF]
  simp (disch := omega) only [upd_same, upd_other]

/-- `f` approximates the `R`-hierarchy on the ordinal `d`. -/
def RApprox (H : ZFAxioms mem) (R : V → V → Prop) (f d : V) : Prop :=
  (∀ p, mem p f → ∃ b S, mem b d ∧ p = kpair H b S) ∧
  (∀ b, mem b d → ∃ S, mem (kpair H b S) f) ∧
  (∀ b S S', mem (kpair H b S) f → mem (kpair H b S') f → S = S') ∧
  (∀ b S, mem (kpair H b S) f →
    ∀ z, mem z S ↔ ∃ c T, mem c b ∧ mem (kpair H c T) f ∧ R z T)

/-- The named formula for `RApprox` (free names `f`, `d`). -/
def rapproxF (rF : Nat → Nat → NForm) (f d : Nat) : NForm :=
  let n := f + d + 1
  -- every member is a pair with first coordinate in `d`
  let c1 := NForm.all n (.imp (.mem n f) (.ex (n + 1) (.ex (n + 2)
    (.and (.mem (n + 1) d) (kpairF n (n + 1) (n + 2))))))
  -- every `b ∈ d` has a value
  let c2 := NForm.all n (.imp (.mem n d) (.ex (n + 1) (pmemF f n (n + 1))))
  -- values are unique
  let c3 := NForm.all n (.all (n + 1) (.all (n + 2)
    (.imp (.and (pmemF f n (n + 1)) (pmemF f n (n + 2))) (.eq (n + 1) (n + 2)))))
  -- the recursion
  let rhs := NForm.ex (n + 3) (.ex (n + 4) (.and (.mem (n + 3) n)
    (.and (pmemF f (n + 3) (n + 4)) (rF (n + 2) (n + 4)))))
  let c4 := NForm.all n (.all (n + 1) (.imp (pmemF f n (n + 1))
    (.all (n + 2) ((NForm.mem (n + 2) (n + 1)).iff rhs))))
  .and c1 (.and c2 (.and c3 c4))

theorem nsat_rapproxF (H : ZFAxioms mem) (hrF : RDef mem R rF) (ρ : Nat → V) (f d : Nat) :
    NSat mem ρ (rapproxF rF f d) ↔ RApprox H R (ρ f) (ρ d) := by
  simp only [rapproxF, NSat, nsat_iff, nsat_kpairF H, nsat_pmemF H, hrF, and_imp]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

section Unique

variable (H : ZFAxioms mem) (hR : Regular mem)
include H hR

/-- Two approximations agree wherever both are defined. -/
theorem rapprox_unique {f g d e : V} (hf : RApprox H R f d) (hg : RApprox H R g e)
    (hd : Ord mem d) (he : Ord mem e) :
    ∀ b, Ord mem b → mem b d → mem b e →
      ∀ S S', mem (kpair H b S) f → mem (kpair H b S') g → S = S' := by
  exact ord_induction H hR
    (fun b => mem b d → mem b e → ∀ S S', mem (kpair H b S) f → mem (kpair H b S') g → S = S')
    (.imp (.mem 0 3) (.imp (.mem 0 4) (.all 5 (.all 6
      (.imp (.and (pmemF 1 0 5) (pmemF 2 0 6)) (.eq 5 6))))))
    (fun i => if i = 1 then f else if i = 2 then g else if i = 3 then d else e)
    (fun x => by
      simp only [NSat, nsat_pmemF H]
      simp (disch := omega) only [upd_same, upd_other]
      simp)
    (fun a ha IH had hae S S' hS hS' => by
      apply H.ext; intro z
      rw [hf.2.2.2 a S hS z, hg.2.2.2 a S' hS' z]
      constructor
      · rintro ⟨c, T, hca, hcT, hzT⟩
        have hcd : mem c d := hd.1 a had c hca
        have hce : mem c e := he.1 a hae c hca
        obtain ⟨T', hT'⟩ := hg.2.1 c hce
        exact ⟨c, T', hca, hT', IH c hca hcd hce T T' hcT hT' ▸ hzT⟩
      · rintro ⟨c, T', hca, hcT', hzT⟩
        have hcd : mem c d := hd.1 a had c hca
        have hce : mem c e := he.1 a hae c hca
        obtain ⟨T, hT⟩ := hf.2.1 c hcd
        exact ⟨c, T, hca, hT, (IH c hca hcd hce T T' hT hcT') ▸ hzT⟩)

end Unique

/-- `m = a ∪ {a}`. -/
def succF (m a : Nat) : NForm :=
  .all (m + a + 1) ((NForm.mem (m + a + 1) m).iff (.or (.mem (m + a + 1) a) (.eq (m + a + 1) a)))

theorem nsat_succF (H : ZFAxioms mem) (ρ : Nat → V) (m a : Nat) :
    NSat mem ρ (succF m a) ↔ ρ m = vsucc H (ρ a) := by
  simp (disch := omega) only [succF, NSat, nsat_iff, upd_same, upd_other]
  exact ⟨fun h => H.ext _ _ fun d => (h d).trans (vsucc_spec H _ d).symm,
    fun h d => by rw [h]; exact vsucc_spec H _ d⟩

section Exists

variable (H : ZFAxioms mem) (hR : Regular mem)
include H hR

/-- Approximations on the same ordinal are equal. -/
theorem rapprox_eq {f g d : V} (hf : RApprox H R f d) (hg : RApprox H R g d) (hd : Ord mem d) :
    f = g := by
  apply H.ext; intro p
  constructor
  · intro hp
    obtain ⟨b, S, hb, rfl⟩ := hf.1 p hp
    obtain ⟨S', hS'⟩ := hg.2.1 b hb
    rwa [rapprox_unique H hR hf hg hd hd b (ord_of_mem hd hb) hb hb S S' hp hS']
  · intro hp
    obtain ⟨b, S, hb, rfl⟩ := hg.1 p hp
    obtain ⟨S', hS'⟩ := hf.2.1 b hb
    rwa [← rapprox_unique H hR hf hg hd hd b (ord_of_mem hd hb) hb hb S' S hS' hp]

omit hR in
/-- First coordinates of pairs in an approximation lie in its domain. -/
theorem rapprox_dom {f d b S : V} (hf : RApprox H R f d) (h : mem (kpair H b S) f) : mem b d := by
  obtain ⟨b', S', hb', he⟩ := hf.1 _ h
  rwa [(kpair_inj H _ _ _ _ he).1]

omit hR in
/-- The next stage `⋃ {{z | R z T} | ⟨c, T⟩ ∈ f}` exists. -/
theorem rstage_exists (hrF : RDef mem R rF) (hS : RSets mem R) {f b : V} (hf : RApprox H R f b) :
    ∃ S, ∀ z, mem z S ↔ ∃ c T, mem c b ∧ mem (kpair H c T) f ∧ R z T := by
  obtain ⟨Q, hQ⟩ := repl_of H (fun p P => ∃ c T, p = kpair H c T ∧ ∀ z, mem z P ↔ R z T)
    (.ex 2 (.ex 3 (.and (kpairF 1 2 3) (classF rF 0 3)))) (fun _ => f)
    (fun x y => by
      simp only [NSat, nsat_kpairF H, nsat_classF hrF]
      simp (disch := omega) only [upd_same, upd_other])
    (fun p P1 P2 ⟨c, T, hp, h1⟩ ⟨c', T', hp', h2⟩ => by
      rw [hp] at hp'
      obtain ⟨-, rfl⟩ := kpair_inj H _ _ _ _ hp'
      exact H.ext _ _ fun z => (h1 z).trans (h2 z).symm) f
  refine ⟨vunion H Q, fun z => ?_⟩
  rw [vunion_spec H Q z]
  constructor
  · rintro ⟨P, hzP, hPQ⟩
    obtain ⟨p, hp, c, T, rfl, hPT⟩ := (hQ P).1 hPQ
    exact ⟨c, T, rapprox_dom H hf hp, hp, (hPT z).1 hzP⟩
  · rintro ⟨c, T, -, hcT, hzT⟩
    obtain ⟨P, hPT⟩ := hS T
    exact ⟨P, (hPT z).2 hzT, (hQ P).2 ⟨_, hcT, c, T, rfl, hPT⟩⟩

/-- Extend an approximation on `b` by the stage `b`. -/
theorem rapprox_extend {f b S : V} (hf : RApprox H R f b) (hb : Ord mem b)
    (hS : ∀ z, mem z S ↔ ∃ c T, mem c b ∧ mem (kpair H c T) f ∧ R z T) :
    RApprox H R (vcup H f (vsingle H (kpair H b S))) (vsucc H b) := by
  have hg : ∀ p, mem p (vcup H f (vsingle H (kpair H b S))) ↔ mem p f ∨ p = kpair H b S := by
    intro p; rw [vcup_spec H _ _ p, vsingle_spec H _ p]
  -- no pair of `f` sits at `b`
  have hnb : ∀ T, ¬ mem (kpair H b T) f := fun T h => mem_irrefl H hR b (rapprox_dom H hf h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases (hg p).1 hp with hp | rfl
    · obtain ⟨c, T, hc, rfl⟩ := hf.1 p hp
      exact ⟨c, T, (vsucc_spec H b c).2 (Or.inl hc), rfl⟩
    · exact ⟨b, S, vsucc_self H b, rfl⟩
  · intro c hc
    rcases (vsucc_spec H b c).1 hc with hc | rfl
    · obtain ⟨T, hT⟩ := hf.2.1 c hc
      exact ⟨T, (hg _).2 (Or.inl hT)⟩
    · exact ⟨S, (hg _).2 (Or.inr rfl)⟩
  · intro c S1 S2 h1 h2
    rcases (hg _).1 h1 with e1 | e1 <;> rcases (hg _).1 h2 with e2 | e2
    · exact hf.2.2.1 c S1 S2 e1 e2
    · obtain ⟨rfl, -⟩ := kpair_inj H _ _ _ _ e2; exact absurd e1 (hnb S1)
    · obtain ⟨rfl, -⟩ := kpair_inj H _ _ _ _ e1; exact absurd e2 (hnb S2)
    · rw [(kpair_inj H _ _ _ _ e1).2, (kpair_inj H _ _ _ _ e2).2]
  · intro c S1 h1 z
    -- pairs of the extension below a stage of `f` are pairs of `f`
    have back : ∀ x, mem x b → ∀ c' T, mem c' x → mem (kpair H c' T) (vcup H f (vsingle H (kpair H b S))) →
        mem (kpair H c' T) f := by
      intro x hx c' T hc' hT
      rcases (hg _).1 hT with hT | hT
      · exact hT
      · obtain ⟨rfl, -⟩ := kpair_inj H _ _ _ _ hT
        exact absurd (hb.1 x hx c' hc') (mem_irrefl H hR c')
    rcases (hg _).1 h1 with h1 | h1
    · rw [hf.2.2.2 c S1 h1 z]
      exact ⟨fun ⟨c', T, hc', hT, hz⟩ => ⟨c', T, hc', (hg _).2 (Or.inl hT), hz⟩,
        fun ⟨c', T, hc', hT, hz⟩ => ⟨c', T, hc', back c (rapprox_dom H hf h1) c' T hc' hT, hz⟩⟩
    · obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ h1
      rw [hS z]
      constructor
      · rintro ⟨c', T, hc', hT, hz⟩; exact ⟨c', T, hc', (hg _).2 (Or.inl hT), hz⟩
      · rintro ⟨c', T, hc', hT, hz⟩
        rcases (hg _).1 hT with hT | hT
        · exact ⟨c', T, hc', hT, hz⟩
        · obtain ⟨rfl, -⟩ := kpair_inj H _ _ _ _ hT
          exact absurd hc' (mem_irrefl H hR _)

/-- Glue the approximations on the successors below `d`. -/
theorem rapprox_glue (hrF : RDef mem R rF) {d : V} (hd : Ord mem d) (h : ∀ b, mem b d → ∃ g, RApprox H R g (vsucc H b)) :
    ∃ F, RApprox H R F d := by
  obtain ⟨G, hG⟩ := repl_of H (fun b g => Ord mem b ∧ RApprox H R g (vsucc H b))
    (.and (ordF 1) (.ex 2 (.and (succF 2 1) (rapproxF rF 0 2)))) (fun _ => d)
    (fun x y => by
      simp only [NSat, nsat_ordF, nsat_succF H, nsat_rapproxF H hrF]
      simp (disch := omega) only [upd_same, upd_other]
      exact ⟨fun ⟨ho, _, rfl, hm⟩ => ⟨ho, hm⟩, fun ⟨ho, hm⟩ => ⟨ho, _, rfl, hm⟩⟩)
    (fun _ _ _ h1 h2 => rapprox_eq H hR h1.2 h2.2 (ord_succ H h1.1)) d
  have hF : ∀ p, mem p (vunion H G) ↔
      ∃ b g, mem b d ∧ RApprox H R g (vsucc H b) ∧ mem p g := by
    intro p; rw [vunion_spec H G p]
    constructor
    · rintro ⟨g, hpg, hgG⟩
      obtain ⟨b, hb, -, hg⟩ := (hG g).1 hgG
      exact ⟨b, g, hb, hg, hpg⟩
    · rintro ⟨b, g, hb, hg, hpg⟩
      exact ⟨g, hpg, (hG g).2 ⟨b, hb, ord_of_mem hd hb, hg⟩⟩
  have agree : ∀ b1 g1 b2 g2 c S1 S2, mem b1 d → RApprox H R g1 (vsucc H b1) → mem b2 d →
      RApprox H R g2 (vsucc H b2) → mem (kpair H c S1) g1 → mem (kpair H c S2) g2 → S1 = S2 := by
    intro b1 g1 b2 g2 c S1 S2 hb1 hg1 hb2 hg2 h1 h2
    have hc1 := rapprox_dom H hg1 h1
    have ho1 := ord_succ H (ord_of_mem hd hb1)
    exact rapprox_unique H hR hg1 hg2 ho1 (ord_succ H (ord_of_mem hd hb2)) c
      (ord_of_mem ho1 hc1) hc1 (rapprox_dom H hg2 h2) S1 S2 h1 h2
  have succ_sub : ∀ b c, mem b d → mem c (vsucc H b) → mem c d := fun b c hb hc =>
    ((vsucc_spec H b c).1 hc).elim (hd.1 b hb c) fun (e : c = b) => e ▸ hb
  refine ⟨vunion H G, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨b, g, hb, hg, hpg⟩ := (hF p).1 hp
    obtain ⟨c, S, hc, rfl⟩ := hg.1 p hpg
    exact ⟨c, S, succ_sub b c hb hc, rfl⟩
  · intro c hc
    obtain ⟨g, hg⟩ := h c hc
    obtain ⟨S, hS⟩ := hg.2.1 c (vsucc_self H c)
    exact ⟨S, (hF _).2 ⟨c, g, hc, hg, hS⟩⟩
  · intro c S1 S2 h1 h2
    obtain ⟨b1, g1, hb1, hg1, h1⟩ := (hF _).1 h1
    obtain ⟨b2, g2, hb2, hg2, h2⟩ := (hF _).1 h2
    exact agree b1 g1 b2 g2 c S1 S2 hb1 hg1 hb2 hg2 h1 h2
  · intro c S1 h1 z
    obtain ⟨b1, g1, hb1, hg1, h1⟩ := (hF _).1 h1
    rw [hg1.2.2.2 c S1 h1 z]
    constructor
    · rintro ⟨c', T, hc', hT, hz⟩
      exact ⟨c', T, hc', (hF _).2 ⟨b1, g1, hb1, hg1, hT⟩, hz⟩
    · rintro ⟨c', T, hc', hT, hz⟩
      obtain ⟨b2, g2, hb2, hg2, hT⟩ := (hF _).1 hT
      obtain ⟨T1, hT1⟩ :=
        hg1.2.1 c' ((ord_succ H (ord_of_mem hd hb1)).1 c (rapprox_dom H hg1 h1) c' hc')
      refine ⟨c', T1, hc', hT1, ?_⟩
      rwa [agree b1 g1 b2 g2 c' T1 T hb1 hg1 hb2 hg2 hT1 hT]

/-- **Every ordinal carries an approximation of the hierarchy.** -/
theorem rapprox_exists (hrF : RDef mem R rF) (hS : RSets mem R) :
    ∀ d, Ord mem d → ∃ f, RApprox H R f d :=
  ord_induction H hR (fun d => ∃ f, RApprox H R f d) (.ex 1 (rapproxF rF 1 0)) (fun _ => vempty H)
    (fun x => by
      simp only [NSat, nsat_rapproxF H hrF]
      simp (disch := omega) only [upd_same, upd_other])
    (fun d hd IH => rapprox_glue H hR hrF hd fun b hb => by
      obtain ⟨f, hf⟩ := IH b hb
      obtain ⟨S, hS'⟩ := rstage_exists H hrF hS hf
      exact ⟨_, rapprox_extend H hR hf (ord_of_mem hd hb) hS'⟩)

end Exists

/-! ## The hierarchy -/

/-- `S` is the stage `a` of the `R`-hierarchy. -/
def RStage (H : ZFAxioms mem) (R : V → V → Prop) (a S : V) : Prop :=
  ∃ f, RApprox H R f (vsucc H a) ∧ mem (kpair H a S) f

/-- The named formula for `RStage` (free names `a`, `S`). -/
def rstageF (rF : Nat → Nat → NForm) (a S : Nat) : NForm :=
  let n := a + S + 1
  .ex n (.and (.ex (n + 1) (.and (succF (n + 1) a) (rapproxF rF n (n + 1)))) (pmemF n a S))

theorem nsat_rstageF (H : ZFAxioms mem) (hrF : RDef mem R rF) (ρ : Nat → V) (a S : Nat) :
    NSat mem ρ (rstageF rF a S) ↔ RStage H R (ρ a) (ρ S) := by
  simp only [rstageF, NSat, nsat_succF H, nsat_rapproxF H hrF, nsat_pmemF H]
  simp (disch := omega) only [upd_same, upd_other]
  exact ⟨fun ⟨f, ⟨_, rfl, hf⟩, h⟩ => ⟨f, hf, h⟩, fun ⟨f, hf, h⟩ => ⟨f, ⟨_, rfl, hf⟩, h⟩⟩

section Stages

variable (H : ZFAxioms mem) (hR : Regular mem)
include H hR

theorem rstage_exists' (hrF : RDef mem R rF) (hS : RSets mem R) {a : V} (ha : Ord mem a) :
    ∃ S, RStage H R a S := by
  obtain ⟨f, hf⟩ := rapprox_exists H hR hrF hS _ (ord_succ H ha)
  obtain ⟨S, hS⟩ := hf.2.1 a (vsucc_self H a)
  exact ⟨S, f, hf, hS⟩

theorem rstage_unique {a S S' : V} (ha : Ord mem a) (h : RStage H R a S) (h' : RStage H R a S') :
    S = S' := by
  obtain ⟨f, hf, hS⟩ := h
  obtain ⟨g, hg, hS'⟩ := h'
  have ho := ord_succ H ha
  exact rapprox_unique H hR hf hg ho ho a ha (vsucc_self H a) (vsucc_self H a) S S' hS hS'

/-- **The recursion equation:** `stage a = {z | R z (stage c) for some c ∈ a}`. -/
theorem rstage_spec (hrF : RDef mem R rF) (hS : RSets mem R) {a S : V} (ha : Ord mem a)
    (h : RStage H R a S) : ∀ z, mem z S ↔ ∃ c T, mem c a ∧ RStage H R c T ∧ R z T := by
  obtain ⟨f, hf, hS0⟩ := h
  have ho := ord_succ H ha
  intro z
  rw [hf.2.2.2 a S hS0 z]
  constructor
  · rintro ⟨c, T, hc, hcT, hz⟩
    have hoc := ord_of_mem ha hc
    obtain ⟨T', g, hg, hcg⟩ := rstage_exists' H hR hrF hS hoc
    have e : T = T' := rapprox_unique H hR hf hg ho (ord_succ H hoc) c hoc
      ((vsucc_spec H a c).2 (Or.inl hc)) (vsucc_self H c) T T' hcT hcg
    exact ⟨c, T, hc, ⟨g, hg, by rwa [e]⟩, hz⟩
  · rintro ⟨c, T, hc, ⟨g, hg, hcg⟩, hz⟩
    have hoc := ord_of_mem ha hc
    obtain ⟨T0, hT0⟩ := hf.2.1 c ((vsucc_spec H a c).2 (Or.inl hc))
    have e : T0 = T := rapprox_unique H hR hf hg ho (ord_succ H hoc) c hoc
      ((vsucc_spec H a c).2 (Or.inl hc)) (vsucc_self H c) T0 T hT0 hcg
    exact ⟨c, T0, hc, hT0, by rwa [e]⟩

/-- Stages grow along the ordinals. -/
theorem rstage_mono (hrF : RDef mem R rF) (hS : RSets mem R) {a c S T : V} (ha : Ord mem a)
    (hc : mem c a) (hT : RStage H R c T) (hSa : RStage H R a S) : Sub mem T S := by
  intro z hz
  obtain ⟨c', T', hc', hT', hzT'⟩ := (rstage_spec H hR hrF hS (ord_of_mem ha hc) hT z).1 hz
  exact (rstage_spec H hR hrF hS ha hSa z).2 ⟨c', T', ha.1 c hc c' hc', hT', hzT'⟩

end Stages

/-! ## The cumulative hierarchy: `R = Sub` -/

/-- `S = V_a`. -/
def IsV (H : ZFAxioms mem) (a S : V) : Prop := RStage H (Sub mem) a S

/-- The named formula for `IsV` (free names `a`, `S`). -/
def isVF (a S : Nat) : NForm := rstageF subF a S

theorem nsat_isVF (H : ZFAxioms mem) (ρ : Nat → V) (a S : Nat) :
    NSat mem ρ (isVF a S) ↔ IsV H (ρ a) (ρ S) :=
  nsat_rstageF H nsat_subF ρ a S

section Hierarchy

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP

theorem isV_exists {a : V} (ha : Ord mem a) : ∃ S, IsV H a S := rstage_exists' H hR nsat_subF hP ha

omit hP in
theorem isV_unique {a S S' : V} (ha : Ord mem a) (h : IsV H a S) (h' : IsV H a S') : S = S' :=
  rstage_unique H hR ha h h'

/-- **The recursion equation:** `V_a = {z | z ⊆ V_c for some c ∈ a}`. -/
theorem isV_spec {a S : V} (ha : Ord mem a) (h : IsV H a S) :
    ∀ z, mem z S ↔ ∃ c T, mem c a ∧ IsV H c T ∧ Sub mem z T :=
  rstage_spec H hR nsat_subF hP ha h

theorem isV_mono {a c S T : V} (ha : Ord mem a) (hc : mem c a) (hT : IsV H c T)
    (hS : IsV H a S) : Sub mem T S :=
  rstage_mono H hR nsat_subF hP ha hc hT hS

theorem isV_trans {a S : V} (ha : Ord mem a) (hS : IsV H a S) : Trans mem S := by
  intro z hz w hw
  obtain ⟨c, T, hc, hT, hzT⟩ := (isV_spec H hR hP ha hS z).1 hz
  exact isV_mono H hR hP ha hc hT hS w (hzT w hw)

end Hierarchy

end SetTheory.BusyBeaver.ZFC.InternalRank
