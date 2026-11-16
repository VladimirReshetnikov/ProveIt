module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentSingleton
public import PA196.Arithmetic.Transport.ActualCertificateEquivalenceInduction
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Actual numeric disjunction certificates and singleton-bottom extraction.
These finite recipes are prerequisites for the separate model-length scan induction. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence

universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable abbrev nativeOr (a b : V) : V := wim (wn a) b

theorem translationOr_eq (a b : V) :
    ActualArithmeticGraph.eval translationOr a b 0 0 = nativeOr a b := by
  simp [translationOr,nativeOr,wn,wim,implicationValue,ActualArithmeticGraph.eval,
    PA196.Arithmetic.HeadGraphs.im,PA196.Arithmetic.HeadGraphs.neg,PA196.Arithmetic.HeadGraphs.implicationExpr]

noncomputable def orLeft (a b : V) : Certificate (wim a (nativeOr a b)) := by
  let p : Context [wn a,a] a := .assumption (by simp)
  let q : Context [wn a,a] (wn a) := .assumption (by simp)
  exact ((Context.mp p q).explosion b).deduction.deduction.empty

noncomputable def orRight (a b : V) : Certificate (wim b (nativeOr a b)) :=
  Dominated.k b (wn a)

noncomputable def orEliminate {a b c : V} (p : Certificate (wim a c))
    (q : Certificate (wim b c)) : Certificate (wim (nativeOr a b) c) := by
  let hn : Context [wn c,nativeOr a b] (wn c) := .assumption (by simp)
  let hd : Context [wn c,nativeOr a b] (nativeOr a b) := .assumption (by simp)
  let na : Context [wn c,nativeOr a b] (wn a) := .mp hn (.closed (contrapose p))
  let cb : Context [wn c,nativeOr a b] c := .mp (.mp na hd) (.closed q)
  exact (Context.mp cb hn).deduction.dne.deduction.empty

/-- An accepted code for the singleton-bottom sequent yields an accepted code
for formula 1 via the actual R6-dependent double-negation elimination recipe. -/
theorem singleton_bottom_certificate (param code : V)
    (h : PA196.Arithmetic.Checker.verifyValue code = sequentCode param {qqFalsum}+1) :
    ∃ result : V, PA196.Arithmetic.Checker.verifyValue result = 1+1 := by
  have he : sequentCode param ({qqFalsum}:V) = wn (wn (1:V)) := by
    rw [sequent_singleton_falsum,translationOr_eq]
  have h' : PA196.Arithmetic.Checker.verifyValue code = wn (wn (1:V))+1 := by
    simpa only [he] using h
  let p : Certificate (wn (wn (1:V))) := ⟨code,h'⟩
  exact ⟨(p.mp (doubleNegationElimination (1:V))).code,
    (p.mp (doubleNegationElimination (1:V))).accepted⟩

#print axioms translationOr_eq
#print axioms orLeft
#print axioms orRight
#print axioms orEliminate
#print axioms singleton_bottom_certificate
end PA196.Arithmetic.Transport.RelationalSource.Numeric

