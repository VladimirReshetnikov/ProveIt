import BusyBeaver.ZFC.KCode222

/-!
The merged equality row recovers reflexivity, the helper and rho7, at the level of codes.

Port of `k225-formal/rocq224/src/G222.v`. With `r = wel x x`, rho1 gives `∃r (r = x)` and
`G(x,x,r)` turns `r = x` into `∀r (x = x)`; existential monotonicity and rho6 then give
`x = x`. The helper `Eq(a,b) → ∀_{wel a b} Eq(a,b)` is `G(a,b,a)` with reflexivity.
Specialization of `∀_{wel a b} Eq(a,b)` goes through `∃r` (rho1), the helper (giving
`∃r ∀r`) and rho6, which yields rho7 from G. Only G, rho1, rho2, rho6, MP, GEN and
propositional logic are used.
-/

namespace SetTheory.BusyBeaver.ZFC.KEqCodes222

open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222 Kalmar

abbrev D := Der wim C222

theorem hC : Classical wim F C222 := c222_classical

theorem d0 {G : List Nat} {a : Nat} : D (a :: G) a := .hyp (List.mem_cons_self ..)
theorem d1 {G : List Nat} {a b : Nat} : D (b :: a :: G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem thm0 {a : Nat} (d : D [] a) : C222 a :=
  d.sound hC (fun _ hx => absurd hx List.not_mem_nil)

theorem ded1 {a c : Nat} (d : D [a] c) : C222 (wim a c) := thm0 (deduction hC d)

theorem ded2 {a b c : Nat} (d : D [b, a] c) : C222 (wim a (wim b c)) :=
  thm0 (deduction hC (deduction hC d))

/-- `(a → b) → (¬b → ¬a)` on codes. -/
theorem contra_thm (a b : Nat) : C222 (wim (wim a b) (wim (wn b) (wn a))) := by
  apply thm0
  apply deduction hC; apply deduction hC; apply deduction hC
  -- hypotheses (innermost first): a, ¬b, a → b
  have hb : D [a, wn b, wim a b] (wim b F) := .hyp (by simp [wn])
  have hab : D [a, wn b, wim a b] (wim a b) := .hyp (by simp)
  exact .mp hb (.mp hab d0)

/-- `∀r (a → b) → (∃r a → ∃r b)` -/
theorem all_ex (r a b : Nat) : C222 (wim (wal r (wim a b)) (wim (wex r a) (wex r b))) := by
  have H1 : C222 (wim (wal r (wim a b)) (wal r (wim (wn b) (wn a)))) :=
    C222.mp (C222.gen r (contra_thm a b)) (C222.r2 r (wim a b) (wim (wn b) (wn a)))
  apply ded1
  -- goal: ∃r a → ∃r b, i.e. ¬∀r¬a → ¬∀r¬b, from ∀r¬b → ∀r¬a
  have h2 : D [wal r (wim a b)] (wim (wal r (wn b)) (wal r (wn a))) :=
    .mp (.ax (C222.r2 r (wn b) (wn a))) (.mp (.ax H1) d0)
  exact .mp (.ax (contra_thm (wal r (wn b)) (wal r (wn a)))) h2

theorem ex_mono (r : Nat) {a b : Nat} (h : C222 (wim a b)) : C222 (wim (wex r a) (wex r b)) :=
  C222.mp (C222.gen r h) (all_ex r a b)

/-- **Reflexivity** of equality, from the merged row. -/
theorem refl222 (x : Nat) : C222 (weq x x) := by
  have H1 : C222 (wim (weq (wel x x) x) (wal (wel x x) (weq x x))) :=
    ded1 (.mp (.mp (.ax (C222.rG x x (wel x x))) d0) d0)
  have H2 : C222 (wex (wel x x) (wal (wel x x) (weq x x))) :=
    C222.mp (C222.r1 (wel x x) x) (ex_mono (wel x x) H1)
  exact C222.mp H2 (C222.r6 (wel x x) (weq x x))

/-- **The helper** `Eq(a,b) → ∀_{wel a b} Eq(a,b)`. -/
theorem helper222 (a b : Nat) : C222 (wim (weq a b) (wal (wel a b) (weq a b))) :=
  C222.mp (refl222 a) (C222.rG a b a)

/-- Specialization at the helper binder. -/
theorem spec_eq (a b : Nat) : C222 (wim (wal (wel a b) (weq a b)) (weq a b)) := by
  have K1 : C222 (wim (wal (wel a b) (weq a b)) (wal (wel a b) (wim (weq (wel a b) a) (weq a b)))) :=
    C222.mp (C222.gen (wel a b) (c222_k (weq a b) (weq (wel a b) a)))
      (C222.r2 (wel a b) (weq a b) (wim (weq (wel a b) a) (weq a b)))
  apply ded1
  have e1 : D [wal (wel a b) (weq a b)] (wex (wel a b) (weq a b)) :=
    .mp (.mp (.ax (all_ex (wel a b) _ _)) (.mp (.ax K1) d0)) (.ax (C222.r1 (wel a b) a))
  have e2 : D [wal (wel a b) (weq a b)] (wex (wel a b) (wal (wel a b) (weq a b))) :=
    .mp (.ax (ex_mono (wel a b) (helper222 a b))) e1
  exact .mp (.ax (C222.r6 (wel a b) (weq a b))) e2

/-- **rho7** from the merged row. -/
theorem rho7_222 (a b c : Nat) : C222 (rho7 a b c) :=
  ded2 (.mp (.ax (spec_eq a b)) (.mp (.mp (.ax (C222.rG a b c)) d1) d0))

/-- Membership vacuity, projected from the bundle `¬(RV → ¬K_s)`. -/
theorem vrel_of_bundle (a b c : Nat) (h1 : c ≠ a) (h2 : c ≠ b) : C222 (vrel a b c) := by
  have hb := C222.bundle a b c h1 h2
  simp only [bundle222] at hb
  -- ¬(A → B) → A
  have t : C222 (wim (wn (wim (vrel a b c) (nks a b c))) (vrel a b c)) := by
    apply ded1
    have inner : D [wim (vrel a b c) F, wn (wim (vrel a b c) (nks a b c))] (wim (vrel a b c) (nks a b c)) :=
      deduction hC (.mp (.ax (c222_efq _)) (.mp d1 d0))
    have hbot : D [wim (vrel a b c) F, wn (wim (vrel a b c) (nks a b c))] F := .mp d1 inner
    exact .mp (.ax (hC.peirce (vrel a b c) F)) (deduction hC (.mp (.ax (c222_efq _)) hbot))
  exact C222.mp hb t

#print axioms rho7_222
#print axioms vrel_of_bundle

end SetTheory.BusyBeaver.ZFC.KEqCodes222
