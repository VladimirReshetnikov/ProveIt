module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateNeighborhoodEquivalence
@[expose] public section

/-! Numeric R1/R3/R5/R7 and noncircular primitive equality recovery.
The only equality-vacuity used here is the special actual-R7 label. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint ActualHeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]


noncomputable abbrev weq (a b : V) : V := wim a b + 3
noncomputable abbrev wex (x a : V) : V := wn (wal x (wn a))

noncomputable def r1 (a b : V) : Certificate (wex a (weq a b)) :=
  ⟨leafCertificate 2 (pack2Value a b),by
    simpa [wex,weq,wn,wim,wal,implicationValue,universalValue,rho1Expr,
      ActualArithmeticGraph.eval,im,al,eqn,ex,neg,implicationExpr,universalExpr]
      using verify_r1 a b⟩
noncomputable def r3 (a b c : V) : Certificate (wim (weq a b) (wim (wel c a) (wel c b))) :=
  ⟨leafCertificate 4 (pack3Value a b c),by
    simpa [weq,wel,wim,implicationValue,rho3Expr,ActualArithmeticGraph.eval,
      im,eqn,mem,implicationExpr] using verify_r3 a b c⟩
noncomputable def r5 (a b c : V) : Certificate (wim (weq c a) (wim (wel c b) (wel a b))) :=
  ⟨leafCertificate 6 (pack3Value a b c),by
    simpa [weq,wel,wim,implicationValue,rho5Expr,ActualArithmeticGraph.eval,
      im,eqn,mem,implicationExpr] using verify_r5 a b c⟩
noncomputable def r7 (a b c : V) :
    Certificate (wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b)))) :=
  ⟨leafCertificate 8 (pack3Value a b c),by
    simpa [weq,wel,wim,wal,implicationValue,universalValue,rho7Expr,
      ActualArithmeticGraph.eval,im,al,eqn,mem,implicationExpr,universalExpr]
      using verify_r7 a b c⟩
noncomputable def Context.existsElim {Γ : List V} (x : V) {a b : V}
    (hv : Certificate (wim b (wal x b)))
    (p : Context Γ (wal x (wim a b))) (q : Context Γ (wex x a)) : Context Γ b := by
  let hn : Context (wn b :: Γ) (wn b) := .assumption (by simp)
  let hnb : Context (wn b :: Γ) (wal x (wn b)) :=
    .mp hn (.closed (negationVacuity x b hv))
  let hc : Context (wn b :: Γ) (wal x (wim (wn b) (wn a))) :=
    (p.up (wn b)).forallMP x (.closed (.all x (contraposition a b)))
  let ha : Context (wn b :: Γ) (wal x (wn a)) := hnb.forallMP x hc
  exact (Context.mp ha (q.up (wn b))).deduction.dne

noncomputable def existentialMonotonicity (x : V) {a b : V} (p : Certificate (wim a b)) :
    Certificate (wim (wex x a) (wex x b)) :=
  contrapose (.mp (.all x (contrapose p)) (r2 x (wn b) (wn a)))

noncomputable def actualReflexivity (a : V) : Certificate (weq a a) := by
  let k := wel a a
  let h : Context [weq k a] (weq k a) := .assumption (by simp)
  let hp : Certificate (wim (weq k a) (wal k (weq a a))) :=
    (Context.mp h (.mp h (.closed (r7 a a k)))).deduction.empty
  let hex : Certificate (wex k (wal k (weq a a))) :=
    .mp (r1 k a) (existentialMonotonicity k hp)
  exact .mp hex (r6 k (weq a a))

/-- This is the special numeric label supplied by actualR7 itself, not an
assumed arbitrary fresh-label equality-vacuity schema. -/
noncomputable def actualSpecialVacuity (a b : V) :
    Certificate (wim (weq a b) (wal (wel a b) (weq a b))) :=
  .mp (actualReflexivity a) (r7 a b a)

/-- The quantifier stripping precondition is paid by an actual finite proof
of special-label vacuity. No historical Named universal-instance lemma. -/
noncomputable def actualEqualityStrip (a b : V) :
    Certificate (wim (wal (wel a b) (weq a b)) (weq a b)) := by
  let k := wel a b
  let h : Context [wal k (weq a b)] (wal k (weq a b)) := .assumption (by simp)
  let himp : Context [wal k (weq a b)] (wal k (wim (weq k a) (weq a b))) :=
    h.forallMP k (.closed (.all k (Dominated.k (weq a b) (weq k a))))
  exact (Context.existsElim k (actualSpecialVacuity a b) himp (.closed (r1 k a))).deduction.empty

noncomputable def actualPlainRho7 (a b c : V) : Certificate (wim (weq a b) (wim (weq a c) (weq b c))) := by
  let hab : Context [weq a c,weq a b] (weq a b) := .assumption (by simp)
  let hac : Context [weq a c,weq a b] (weq a c) := .assumption (by simp)
  let hall : Context [weq a c,weq a b] (wal (wel b c) (weq b c)) :=
    .mp hac (.mp hab (.closed (r7 b c a)))
  exact (Context.mp hall (.closed (actualEqualityStrip b c))).deduction.deduction.empty


#print axioms r1
#print axioms r3
#print axioms r5
#print axioms r7
#print axioms Context.existsElim
#print axioms existentialMonotonicity
#print axioms actualReflexivity
#print axioms actualSpecialVacuity
#print axioms actualEqualityStrip
#print axioms actualPlainRho7
end M6.PA.ActualCertificateEquivalence

