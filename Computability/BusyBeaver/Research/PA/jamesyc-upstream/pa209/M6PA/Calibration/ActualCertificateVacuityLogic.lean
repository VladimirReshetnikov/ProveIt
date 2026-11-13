module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateVacuityMembership
@[expose] public section

/-! Finite modal vacuity certificate recipes, using closed GEN only. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint ActualHeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def negationVacuity (x a : V) (hv : Certificate (wim a (wal x a))) :
    Certificate (wim (wn a) (wal x (wn a))) := by
  let hc := contrapose hv
  let hg := Certificate.all x hc
  let hl := Certificate.mp hg (r2 x (wn (wal x a)) (wn a))
  let hr := contrapose (r6 x a)
  let hf := implicationCompose hr (doubleNegationElimination (wal x (wn (wal x a))))
  exact implicationCompose hf hl


noncomputable def r4 (a b c : V) : Certificate (wim (wal a (wal b c)) (wal b (wal a c))) :=
  ⟨leafCertificate 5 (pack3Value a b c),by
    simpa [wim,wal,implicationValue,universalValue,rho4Expr,ActualArithmeticGraph.eval,im,al,implicationExpr,universalExpr]
      using verify_r4 a b c⟩

noncomputable def Context.casesOnFormula {Γ : List V} (a : V) {c : V}
    (p : Context (a :: Γ) c) (q : Context (wn a :: Γ) c) : Context Γ c := by
  let hn : Context (wn c :: Γ) (wn c) := .assumption (by simp)
  let hp : Context (wn c :: Γ) (wim a c) := p.deduction.up (wn c)
  let hna : Context (wn c :: Γ) (wn a) :=
    .mp hn (.mp hp (.closed (contraposition a c)))
  let hc : Context (wn c :: Γ) c := .mp hna (q.deduction.up (wn c))
  exact (Context.mp hc hn).deduction.dne

noncomputable def implicationVacuity (x a b : V)
    (ha : Certificate (wim a (wal x a))) (hb : Certificate (wim b (wal x b))) :
    Certificate (wim (wim a b) (wal x (wim a b))) := by
  let c := wal x (wim a b)
  let hbLift : Certificate (wim b c) := implicationCompose hb
    (.mp (.all x (Dominated.k b a)) (r2 x b (wim a b)))
  let hn : Context [a, wn a] (wn a) := .assumption (by simp)
  let hp : Context [a, wn a] a := .assumption (by simp)
  let hnot : Certificate (wim (wn a) (wim a b)) :=
    ((Context.mp hp hn).explosion b).deduction.deduction.empty
  let haLift : Certificate (wim (wn a) c) := implicationCompose (negationVacuity x a ha)
    (.mp (.all x hnot) (r2 x (wn a) (wim a b)))
  let pa : Context [a, wim a b] a := .assumption (by simp)
  let pab : Context [a, wim a b] (wim a b) := .assumption (by simp)
  let pc : Context [a, wim a b] c := .mp (.mp pa pab) (.closed hbLift)
  let pna : Context [wn a, wim a b] (wn a) := .assumption (by simp)
  let pnc : Context [wn a, wim a b] c := .mp pna (.closed haLift)
  exact (Context.casesOnFormula a pc pnc).deduction.empty

noncomputable def universalVacuity (x y a : V) (h : Certificate (wim a (wal x a))) :
    Certificate (wim (wal y a) (wal x (wal y a))) :=
  implicationCompose (.mp (.all y h) (r2 y a (wal x a))) (r4 y x a)


noncomputable def conjunctionVacuity (x a b : V)
    (ha : Certificate (wim a (wal x a))) (hb : Certificate (wim b (wal x b))) :
    Certificate (wim (wa a b) (wal x (wa a b))) :=
  negationVacuity x (wim a (wn b))
    (implicationVacuity x a (wn b) ha (negationVacuity x b hb))


#print axioms negationVacuity
#print axioms r4
#print axioms Context.casesOnFormula
#print axioms implicationVacuity
#print axioms universalVacuity
#print axioms conjunctionVacuity
end M6.PA.ActualCertificateEquivalence

