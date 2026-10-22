import BusyBeaver.ZFC.InternalRank

/-!
Transfinite recursion for a definable stage operation.

Given an operation `G` on the sets of a model of ZF with Foundation whose graph
is defined by a named formula, there is a unique hierarchy

    stage a = ⋃ { G (stage c) | c ∈ a }

along the internal ordinals. With `G = P` this is the cumulative hierarchy of
`InternalRank`; with `G = Def` it will be Gödel's constructible hierarchy.

The development follows `InternalRank`, with `z ⊆ T` replaced by `z ∈ G T`:
approximations are sets of Kuratowski pairs obeying the recursion; they agree
where both are defined, extend by one stage, glue below every ordinal, and so
exist (`approx_exists`); `IsStage` reads the hierarchy off them.
-/

namespace SetTheory.BusyBeaver.ZFC.TransRec

open NamedZF NForm InternalOrd InternalRank

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- A definable operation: `gF y x` defines `y = G x` (output name `y`, input name `x`). -/
structure DefOp (mem : V → V → Prop) (G : V → V) where
  gF : Nat → Nat → NForm
  spec : ∀ (ρ : Nat → V) (y x : Nat), NSat mem ρ (gF y x) ↔ ρ y = G (ρ x)

variable {G : V → V}

/-- `z ∈ G t`, with a fresh witness name. -/
def inGF (D : DefOp mem G) (z t : Nat) : NForm :=
  .ex (z + t + 1) (.and (D.gF (z + t + 1) t) (.mem z (z + t + 1)))

theorem nsat_inGF (D : DefOp mem G) (ρ : Nat → V) (z t : Nat) :
    NSat mem ρ (inGF D z t) ↔ mem (ρ z) (G (ρ t)) := by
  simp only [inGF, NSat, D.spec]
  simp (disch := omega) only [upd_same, upd_other]
  constructor
  · rintro ⟨d, rfl, h⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

/-! ## Approximations -/

/-- `f` approximates the `G`-hierarchy on the ordinal `d`. -/
def Approx (H : ZFAxioms mem) (G : V → V) (f d : V) : Prop :=
  (∀ p, mem p f → ∃ b S, mem b d ∧ p = kpair H b S) ∧
  (∀ b, mem b d → ∃ S, mem (kpair H b S) f) ∧
  (∀ b S S', mem (kpair H b S) f → mem (kpair H b S') f → S = S') ∧
  (∀ b S, mem (kpair H b S) f →
    ∀ z, mem z S ↔ ∃ c T, mem c b ∧ mem (kpair H c T) f ∧ mem z (G T))

def approxF (D : DefOp mem G) (f d : Nat) : NForm :=
  let n := f + d + 1
  let c1 := NForm.all n (.imp (.mem n f) (.ex (n + 1) (.ex (n + 2)
    (.and (.mem (n + 1) d) (kpairF n (n + 1) (n + 2))))))
  let c2 := NForm.all n (.imp (.mem n d) (.ex (n + 1) (pmemF f n (n + 1))))
  let c3 := NForm.all n (.all (n + 1) (.all (n + 2)
    (.imp (.and (pmemF f n (n + 1)) (pmemF f n (n + 2))) (.eq (n + 1) (n + 2)))))
  let rhs := NForm.ex (n + 3) (.ex (n + 4) (.and (.mem (n + 3) n)
    (.and (pmemF f (n + 3) (n + 4)) (inGF D (n + 2) (n + 4)))))
  let c4 := NForm.all n (.all (n + 1) (.imp (pmemF f n (n + 1))
    (.all (n + 2) ((NForm.mem (n + 2) (n + 1)).iff rhs))))
  .and c1 (.and c2 (.and c3 c4))

theorem nsat_approxF (H : ZFAxioms mem) (D : DefOp mem G) (ρ : Nat → V) (f d : Nat) :
    NSat mem ρ (approxF D f d) ↔ Approx H G (ρ f) (ρ d) := by
  simp only [approxF, NSat, nsat_iff, nsat_kpairF H, nsat_pmemF H, nsat_inGF D, and_imp]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

section Recursion

variable (H : ZFAxioms mem) (hR : Regular mem) (D : DefOp mem G)
include H hR D

omit D in
theorem approx_unique {f g d e : V} (hf : Approx H G f d) (hg : Approx H G g e)
    (hd : Ord mem d) (he : Ord mem e) :
    ∀ b, Ord mem b → mem b d → mem b e →
      ∀ S S', mem (kpair H b S) f → mem (kpair H b S') g → S = S' := by
  have key := ord_induction H hR
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
      · rintro ⟨c, T, hca, hcT, hz⟩
        have hcd : mem c d := hd.1 a had c hca
        have hce : mem c e := he.1 a hae c hca
        obtain ⟨T', hT'⟩ := hg.2.1 c hce
        exact ⟨c, T', hca, hT', IH c hca hcd hce T T' hcT hT' ▸ hz⟩
      · rintro ⟨c, T', hca, hcT', hz⟩
        have hcd : mem c d := hd.1 a had c hca
        have hce : mem c e := he.1 a hae c hca
        obtain ⟨T, hT⟩ := hf.2.1 c hcd
        exact ⟨c, T, hca, hT, (IH c hca hcd hce T T' hT hcT') ▸ hz⟩)
  exact key

omit D in
theorem approx_eq {f g d : V} (hf : Approx H G f d) (hg : Approx H G g d) (hd : Ord mem d) :
    f = g := by
  apply H.ext; intro p
  constructor
  · intro hp
    obtain ⟨b, S, hb, rfl⟩ := hf.1 p hp
    obtain ⟨S', hS'⟩ := hg.2.1 b hb
    rwa [approx_unique H hR hf hg hd hd b (ord_of_mem hd hb) hb hb S S' hp hS']
  · intro hp
    obtain ⟨b, S, hb, rfl⟩ := hg.1 p hp
    obtain ⟨S', hS'⟩ := hf.2.1 b hb
    rwa [← approx_unique H hR hf hg hd hd b (ord_of_mem hd hb) hb hb S' S hS' hp]

omit hR D in
theorem approx_dom {f d b S : V} (hf : Approx H G f d) (h : mem (kpair H b S) f) : mem b d := by
  obtain ⟨b', S', hb', he⟩ := hf.1 _ h
  rw [(kpair_inj H _ _ _ _ he).1]; exact hb'

omit hR in
/-- The next stage `⋃ {G T | ⟨c, T⟩ ∈ f}` exists. -/
theorem stage_exists {f b : V} (hf : Approx H G f b) :
    ∃ S, ∀ z, mem z S ↔ ∃ c T, mem c b ∧ mem (kpair H c T) f ∧ mem z (G T) := by
  obtain ⟨Q, hQ⟩ := repl_of H (fun p P => ∃ c T, p = kpair H c T ∧ P = G T)
    (.ex 2 (.ex 3 (.and (kpairF 1 2 3) (D.gF 0 3)))) (fun _ => f)
    (fun x y => by
      simp only [NSat, nsat_kpairF H, D.spec]
      simp (disch := omega) only [upd_same, upd_other])
    (fun p P1 P2 ⟨c, T, hp, h1⟩ ⟨c', T', hp', h2⟩ => by
      rw [hp] at hp'
      obtain ⟨-, rfl⟩ := kpair_inj H _ _ _ _ hp'
      rw [h1, h2]) f
  refine ⟨vunion H Q, fun z => ?_⟩
  rw [vunion_spec H Q z]
  constructor
  · rintro ⟨P, hzP, hPQ⟩
    obtain ⟨p, hp, c, T, rfl, rfl⟩ := (hQ P).1 hPQ
    exact ⟨c, T, approx_dom H hf hp, hp, hzP⟩
  · rintro ⟨c, T, -, hcT, hz⟩
    exact ⟨G T, hz, (hQ _).2 ⟨_, hcT, c, T, rfl, rfl⟩⟩

omit D in
theorem approx_extend {f b S : V} (hf : Approx H G f b) (hb : Ord mem b)
    (hS : ∀ z, mem z S ↔ ∃ c T, mem c b ∧ mem (kpair H c T) f ∧ mem z (G T)) :
    Approx H G (vcup H f (vsingle H (kpair H b S))) (vsucc H b) := by
  have hg : ∀ p, mem p (vcup H f (vsingle H (kpair H b S))) ↔ mem p f ∨ p = kpair H b S := by
    intro p; rw [vcup_spec H _ _ p, vsingle_spec H _ p]
  have hnb : ∀ T, ¬ mem (kpair H b T) f := fun T h => mem_irrefl H hR b (approx_dom H hf h)
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
    have back : ∀ x, mem x b → ∀ c' T, mem c' x →
        mem (kpair H c' T) (vcup H f (vsingle H (kpair H b S))) → mem (kpair H c' T) f := by
      intro x hx c' T hc' hT
      rcases (hg _).1 hT with hT | hT
      · exact hT
      · obtain ⟨rfl, -⟩ := kpair_inj H _ _ _ _ hT
        exact absurd (hb.1 x hx c' hc') (mem_irrefl H hR c')
    rcases (hg _).1 h1 with h1 | h1
    · have hcb := approx_dom H hf h1
      rw [hf.2.2.2 c S1 h1 z]
      constructor
      · rintro ⟨c', T, hc', hT, hz⟩; exact ⟨c', T, hc', (hg _).2 (Or.inl hT), hz⟩
      · rintro ⟨c', T, hc', hT, hz⟩; exact ⟨c', T, hc', back c hcb c' T hc' hT, hz⟩
    · obtain ⟨rfl, rfl⟩ := kpair_inj H _ _ _ _ h1
      rw [hS z]
      constructor
      · rintro ⟨c', T, hc', hT, hz⟩; exact ⟨c', T, hc', (hg _).2 (Or.inl hT), hz⟩
      · rintro ⟨c', T, hc', hT, hz⟩
        rcases (hg _).1 hT with hT | hT
        · exact ⟨c', T, hc', hT, hz⟩
        · obtain ⟨rfl, -⟩ := kpair_inj H _ _ _ _ hT
          exact absurd hc' (mem_irrefl H hR _)

theorem approx_glue {d : V} (hd : Ord mem d)
    (h : ∀ b, mem b d → ∃ g, Approx H G g (vsucc H b)) : ∃ F, Approx H G F d := by
  obtain ⟨Gs, hG⟩ := repl_of H (fun b g => Ord mem b ∧ Approx H G g (vsucc H b))
    (.and (ordF 1) (.ex 2 (.and (succF 2 1) (approxF D 0 2)))) (fun _ => d)
    (fun x y => by
      simp only [NSat, nsat_ordF, nsat_succF H, nsat_approxF H D]
      simp (disch := omega) only [upd_same, upd_other]
      constructor
      · rintro ⟨ho, m, rfl, hm⟩; exact ⟨ho, hm⟩
      · rintro ⟨ho, hm⟩; exact ⟨ho, _, rfl, hm⟩)
    (fun _ _ _ h1 h2 => approx_eq H hR h1.2 h2.2 (ord_succ H h1.1)) d
  have hF : ∀ p, mem p (vunion H Gs) ↔
      ∃ b g, mem b d ∧ Approx H G g (vsucc H b) ∧ mem p g := by
    intro p; rw [vunion_spec H Gs p]
    constructor
    · rintro ⟨g, hpg, hgG⟩
      obtain ⟨b, hb, -, hg⟩ := (hG g).1 hgG
      exact ⟨b, g, hb, hg, hpg⟩
    · rintro ⟨b, g, hb, hg, hpg⟩
      exact ⟨g, hpg, (hG g).2 ⟨b, hb, ord_of_mem hd hb, hg⟩⟩
  have agree : ∀ b1 g1 b2 g2 c S1 S2, mem b1 d → Approx H G g1 (vsucc H b1) → mem b2 d →
      Approx H G g2 (vsucc H b2) → mem (kpair H c S1) g1 → mem (kpair H c S2) g2 → S1 = S2 := by
    intro b1 g1 b2 g2 c S1 S2 hb1 hg1 hb2 hg2 h1 h2
    have hc1 := approx_dom H hg1 h1
    have ho1 := ord_succ H (ord_of_mem hd hb1)
    exact approx_unique H hR hg1 hg2 ho1 (ord_succ H (ord_of_mem hd hb2)) c
      (ord_of_mem ho1 hc1) hc1 (approx_dom H hg2 h2) S1 S2 h1 h2
  have succ_sub : ∀ b c, mem b d → mem c (vsucc H b) → mem c d := by
    intro b c hb hc
    rcases (vsucc_spec H b c).1 hc with hc | rfl
    · exact hd.1 b hb c hc
    · exact hb
  refine ⟨vunion H Gs, ?_, ?_, ?_, ?_⟩
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
    have hcs := approx_dom H hg1 h1
    constructor
    · rintro ⟨c', T, hc', hT, hz⟩
      exact ⟨c', T, hc', (hF _).2 ⟨b1, g1, hb1, hg1, hT⟩, hz⟩
    · rintro ⟨c', T, hc', hT, hz⟩
      obtain ⟨b2, g2, hb2, hg2, hT⟩ := (hF _).1 hT
      have hc's : mem c' (vsucc H b1) := (ord_succ H (ord_of_mem hd hb1)).1 c hcs c' hc'
      obtain ⟨T1, hT1⟩ := hg1.2.1 c' hc's
      refine ⟨c', T1, hc', hT1, ?_⟩
      rwa [agree b1 g1 b2 g2 c' T1 T hb1 hg1 hb2 hg2 hT1 hT]

/-- **Every ordinal carries an approximation of the `G`-hierarchy.** -/
theorem approx_exists : ∀ d, Ord mem d → ∃ f, Approx H G f d :=
  ord_induction H hR (fun d => ∃ f, Approx H G f d) (.ex 1 (approxF D 1 0)) (fun _ => vempty H)
    (fun x => by
      simp only [NSat, nsat_approxF H D]
      simp (disch := omega) only [upd_same, upd_other])
    (fun d hd IH => approx_glue H hR D hd fun b hb => by
      obtain ⟨f, hf⟩ := IH b hb
      obtain ⟨S, hS⟩ := stage_exists H D hf
      exact ⟨_, approx_extend H hR hf (ord_of_mem hd hb) hS⟩)

end Recursion

/-! ## The hierarchy -/

/-- `S` is the stage `a` of the `G`-hierarchy. -/
def IsStage (H : ZFAxioms mem) (G : V → V) (a S : V) : Prop :=
  ∃ f, Approx H G f (vsucc H a) ∧ mem (kpair H a S) f

def isStageF (D : DefOp mem G) (a S : Nat) : NForm :=
  let n := a + S + 1
  .ex n (.and (.ex (n + 1) (.and (succF (n + 1) a) (approxF D n (n + 1)))) (pmemF n a S))

theorem nsat_isStageF (H : ZFAxioms mem) (D : DefOp mem G) (ρ : Nat → V) (a S : Nat) :
    NSat mem ρ (isStageF D a S) ↔ IsStage H G (ρ a) (ρ S) := by
  simp only [isStageF, NSat, nsat_succF H, nsat_approxF H D, nsat_pmemF H]
  simp (disch := omega) only [upd_same, upd_other]
  constructor
  · rintro ⟨f, ⟨m, rfl, hf⟩, h⟩; exact ⟨f, hf, h⟩
  · rintro ⟨f, hf, h⟩; exact ⟨f, ⟨_, rfl, hf⟩, h⟩

section Hierarchy

variable (H : ZFAxioms mem) (hR : Regular mem) (D : DefOp mem G)
include H hR D

theorem stage_exists' {a : V} (ha : Ord mem a) : ∃ S, IsStage H G a S := by
  obtain ⟨f, hf⟩ := approx_exists H hR D _ (ord_succ H ha)
  obtain ⟨S, hS⟩ := hf.2.1 a (vsucc_self H a)
  exact ⟨S, f, hf, hS⟩

omit D in
theorem stage_unique {a S S' : V} (ha : Ord mem a) (h : IsStage H G a S) (h' : IsStage H G a S') :
    S = S' := by
  obtain ⟨f, hf, hS⟩ := h
  obtain ⟨g, hg, hS'⟩ := h'
  have ho := ord_succ H ha
  exact approx_unique H hR hf hg ho ho a ha (vsucc_self H a) (vsucc_self H a) S S' hS hS'

/-- **The recursion equation:** `stage a = ⋃ {G (stage c) | c ∈ a}`. -/
theorem stage_spec {a S : V} (ha : Ord mem a) (h : IsStage H G a S) :
    ∀ z, mem z S ↔ ∃ c T, mem c a ∧ IsStage H G c T ∧ mem z (G T) := by
  obtain ⟨f, hf, hS⟩ := h
  have ho := ord_succ H ha
  intro z
  rw [hf.2.2.2 a S hS z]
  constructor
  · rintro ⟨c, T, hc, hcT, hz⟩
    have hoc := ord_of_mem ha hc
    obtain ⟨T', g, hg, hcg⟩ := stage_exists' H hR D hoc
    have e : T = T' := approx_unique H hR hf hg ho (ord_succ H hoc) c hoc
      ((vsucc_spec H a c).2 (Or.inl hc)) (vsucc_self H c) T T' hcT hcg
    exact ⟨c, T, hc, ⟨g, hg, by rw [e]; exact hcg⟩, hz⟩
  · rintro ⟨c, T, hc, ⟨g, hg, hcg⟩, hz⟩
    have hoc := ord_of_mem ha hc
    obtain ⟨T0, hT0⟩ := hf.2.1 c ((vsucc_spec H a c).2 (Or.inl hc))
    have e : T0 = T := approx_unique H hR hf hg ho (ord_succ H hoc) c hoc
      ((vsucc_spec H a c).2 (Or.inl hc)) (vsucc_self H c) T0 T hT0 hcg
    exact ⟨c, T0, hc, hT0, by rw [e]; exact hz⟩

/-- Stages grow along the ordinals. -/
theorem stage_mono {a c S T : V} (ha : Ord mem a) (hc : mem c a) (hT : IsStage H G c T)
    (hS : IsStage H G a S) : Sub mem T S := by
  intro z hz
  obtain ⟨c', T', hc', hT', hzT'⟩ := (stage_spec H hR D (ord_of_mem ha hc) hT z).1 hz
  exact (stage_spec H hR D ha hS z).2 ⟨c', T', ha.1 c hc c' hc', hT', hzT'⟩

end Hierarchy

end SetTheory.BusyBeaver.ZFC.TransRec
