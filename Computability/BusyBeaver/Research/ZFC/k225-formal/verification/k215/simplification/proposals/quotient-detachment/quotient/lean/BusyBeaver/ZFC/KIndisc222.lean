import BusyBeaver.ZFC.KSeedModel222

/-!
From equality-free seed instances to all of them, through the indiscernibility quotient.

In any structure, `Ind x y` (same members, same memberships) is an equivalence that `mem`
respects, so `mem` descends to the quotient `IndQ mem`. There, literal equality is `Ind`, which
the equality-free formula `KEind222.Eind` defines; so a named formula holds in the quotient iff its
equality interpretation `th` holds upstairs (`sat_mk`). Hence a structure with the seed property for
every equality-free relation has a quotient with the seed property for **every** named relation,
literal equality included (`fullSeed_quotient`). This is the semantic counterpart of the
equality axioms `EqAx` in Elliot Glazer's `K0`.
-/

namespace SetTheory.BusyBeaver.ZFC.KIndisc222

open SetTheory.BusyBeaver.ZFC.Tarski
open SetTheory.BusyBeaver.ZFC.KSeed222
open NF

universe u
variable {V : Type u}

/-- The seed property for every named relation, with input name `0` and output name `1`. -/
structure FullSeed (mem : V → V → Prop) : Prop where
  irr : ∀ x, ¬ mem x x
  seed : ∀ (ψ : NF) (e : Nat → V),
    SeedProp mem (fun x y => Tarski.Sat mem (update (update e 0 x) 1 y) ψ) (e 0)

def Ind (mem : V → V → Prop) (x y : V) : Prop :=
  (∀ z, mem z x ↔ mem z y) ∧ (∀ z, mem x z ↔ mem y z)

def indSetoid (mem : V → V → Prop) : Setoid V where
  r := Ind mem
  iseqv := ⟨fun _ => ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩,
    fun h => ⟨fun z => (h.1 z).symm, fun z => (h.2 z).symm⟩,
    fun h1 h2 => ⟨fun z => (h1.1 z).trans (h2.1 z), fun z => (h1.2 z).trans (h2.2 z)⟩⟩

def IndQ (mem : V → V → Prop) : Type u := Quotient (indSetoid mem)

def mk (mem : V → V → Prop) (x : V) : IndQ mem := Quotient.mk (indSetoid mem) x

def qmem (mem : V → V → Prop) : IndQ mem → IndQ mem → Prop :=
  Quotient.lift₂ mem fun x y x' y' (hx : Ind mem x x') (hy : Ind mem y y') =>
    propext ((hx.2 y).trans (hy.1 x'))

theorem qmem_mk (mem : V → V → Prop) (x y : V) : qmem mem (mk mem x) (mk mem y) ↔ mem x y := Iff.rfl

theorem mk_eq (mem : V → V → Prop) (x y : V) : mk mem x = mk mem y ↔ Ind mem x y :=
  ⟨Quotient.exact, fun h => Quotient.sound (s := indSetoid mem) h⟩

theorem mk_surj (mem : V → V → Prop) (q : IndQ mem) : ∃ x, mk mem x = q := Quotient.exists_rep q

/-! ## Semantics of the equality interpretation -/

theorem sat_neg (mem : V → V → Prop) (e : Nat → V) (a : NF) :
    Tarski.Sat mem e (NF.neg a) ↔ ¬ Tarski.Sat mem e a := Iff.rfl

theorem sat_wa (mem : V → V → Prop) (e : Nat → V) (a b : NF) :
    Tarski.Sat mem e (KEind222.wa a b) ↔ Tarski.Sat mem e a ∧ Tarski.Sat mem e b := by
  simp only [KEind222.wa, NF.neg, Tarski.Sat]
  exact ⟨fun h => ⟨Classical.byContradiction fun ha => h fun h' _ => ha h',
    Classical.byContradiction fun hb => h fun _ h' => hb h'⟩, fun ⟨ha, hb⟩ h => h ha hb⟩

theorem sat_biff (mem : V → V → Prop) (e : Nat → V) (a b : NF) :
    Tarski.Sat mem e (KEind222.biff a b) ↔ (Tarski.Sat mem e a ↔ Tarski.Sat mem e b) := by
  rw [KEind222.biff, sat_wa]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem sat_Eind (mem : V → V → Prop) (e : Nat → V) (x y : Nat) :
    Tarski.Sat mem e (KEind222.Eind x y) ↔ Ind mem (e x) (e y) := by
  have hx : x ≠ KEind222.aux x y := KEind222.aux_ne_l x y
  have hy : y ≠ KEind222.aux x y := KEind222.aux_ne_r x y
  rw [KEind222.Eind, KEind222.Ev, sat_wa]
  simp only [Tarski.Sat, KEind222.Bin, KEind222.Bout, sat_biff, Tarski.Sat, update_same,
    update_other _ _ hx, update_other _ _ hy]
  rfl

theorem eqFree_th : ∀ f : NF, KThmK.EqFree (KEind222.th f)
  | rel _ _ => trivial
  | NF.eq i j => KEind222.ef_ev _ i j
  | NF.bot => trivial
  | imp a b => ⟨eqFree_th a, eqFree_th b⟩
  | all _ a => eqFree_th a

theorem update_mk (mem : V → V → Prop) (e : Nat → V) (i : Nat) (x : V) :
    update (fun n => mk mem (e n)) i (mk mem x) = fun n => mk mem (update e i x n) := by
  funext n; by_cases h : n = i
  · subst h; simp [update]
  · simp [update, h]

/-- **A named formula holds in the quotient iff its equality interpretation holds upstairs.** -/
theorem sat_mk (mem : V → V → Prop) : ∀ (f : NF) (e : Nat → V),
    Tarski.Sat (qmem mem) (fun n => mk mem (e n)) f ↔ Tarski.Sat mem e (KEind222.th f)
  | rel i j, e => Iff.rfl
  | NF.eq i j, e => (mk_eq mem _ _).trans (sat_Eind mem e i j).symm
  | NF.bot, _ => Iff.rfl
  | imp a b, e => imp_congr (sat_mk mem a e) (sat_mk mem b e)
  | all i a, e => by
      show (∀ q, Tarski.Sat (qmem mem) (update (fun n => mk mem (e n)) i q) a) ↔
        ∀ d, Tarski.Sat mem (update e i d) (KEind222.th a)
      constructor
      · intro h d
        have := h (mk mem d)
        rw [update_mk] at this
        exact (sat_mk mem a _).mp this
      · intro h q
        obtain ⟨d, rfl⟩ := mk_surj mem q
        rw [update_mk]
        exact (sat_mk mem a _).mpr (h d)

/-- **The quotient has the seed property for every named relation.** -/
theorem fullSeed_quotient (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hseed : ∀ ψ : NF, KThmK.EqFree ψ → ∀ e : Nat → V,
      SeedProp mem (fun x y => Tarski.Sat mem (update (update e 0 x) 1 y) ψ) (e 0)) :
    FullSeed (qmem mem) := by
  refine ⟨fun q => ?_, fun ψ e' => ?_⟩
  · obtain ⟨x, rfl⟩ := mk_surj mem q
    exact hirr x
  · -- representatives of the parameters
    let e : Nat → V := fun n => Classical.choose (Quotient.exists_rep (e' n))
    have he : (fun n => mk mem (e n)) = e' :=
      funext fun n => Classical.choose_spec (Quotient.exists_rep (e' n))
    have hR : ∀ x y : V, Tarski.Sat (qmem mem) (update (update e' 0 (mk mem x)) 1 (mk mem y)) ψ ↔
        Tarski.Sat mem (update (update e 0 x) 1 y) (KEind222.th ψ) := by
      intro x y
      rw [← he, update_mk, update_mk]
      exact sat_mk mem ψ _
    obtain ⟨C, h1, h2⟩ := hseed (KEind222.th ψ) (eqFree_th ψ) e
    have h0 : e' 0 = mk mem (e 0) := by rw [← he]
    refine ⟨mk mem C, fun y hy => ?_, fun y hy => ?_⟩
    · obtain ⟨y, rfl⟩ := mk_surj mem y
      rw [h0] at hy ⊢
      obtain ⟨z, hz, hzC⟩ := h1 y ((hR _ _).mp hy)
      exact ⟨mk mem z, (hR _ _).mpr hz, hzC⟩
    · obtain ⟨y, rfl⟩ := mk_surj mem y
      obtain ⟨x, hx, hsub⟩ := h2 y hy
      refine ⟨mk mem x, (hR _ _).mpr hx, fun x' hx' y' hy' => ?_⟩
      obtain ⟨x', rfl⟩ := mk_surj mem x'
      obtain ⟨y', rfl⟩ := mk_surj mem y'
      obtain ⟨z, hz, hzC⟩ := hsub x' (fun w hw => hx' (mk mem w) hw) y' ((hR _ _).mp hy')
      exact ⟨mk mem z, (hR _ _).mpr hz, hzC⟩

/-- **A model of the derivable formulas yields a full seed model.** -/
theorem fullSeed_of_derivable (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f) : FullSeed (qmem mem) :=
  fullSeed_quotient mem hirr fun ψ hψ e => seed_eqFree mem hirr hT ψ hψ e

#print axioms fullSeed_of_derivable

end SetTheory.BusyBeaver.ZFC.KIndisc222
