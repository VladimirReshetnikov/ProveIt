import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasLogQuotient
import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasDifferenceQuotientAlgebra
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalPositiveLogarithmCalculus

/-! Subtract the original Barnes logarithm and its three verified derivative names from
the supplied positive candidate and its logarithmic derivatives. The resulting names
carry adjacent divided-quotient rates on the same rational chart. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasQuotientJet

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "Q" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data
local notation "L" => GaussianBarnesCanonicalPositiveLogarithm.nameF
local notation "ld" => GaussianBarnesCanonicalPositiveLogarithm.data
local notation "L₁" => GaussianBarnesCanonicalPositiveFirstLogarithm.nameF
local notation "d₁" => GaussianBarnesCanonicalPositiveFirstLogarithm.data
local notation "L₂" => GaussianBarnesCanonicalPositiveSecondLogarithm.nameF
local notation "d₂" => GaussianBarnesCanonicalPositiveSecondLogarithm.data
local notation "L₃" => GaussianBarnesCanonicalThirdLogarithmCofinal.nameF
local notation "d₃" => GaussianBarnesCanonicalThirdLogarithmCofinal.data
local notation "Log" => GaussianNamedPositiveLogarithm.nameF
local notation "logd" => GaussianNamedPositiveLogarithm.data
local notation "J₀" => GaussianBarnesVignerasLogQuotient.nameF
local notation "data0" => GaussianBarnesVignerasLogQuotient.data
local notation "chart" => GaussianBarnesCanonicalPositiveLogarithmCalculus.source
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source

abbrev firstF (f : PR 2) : PR 2 := Diff f L₁
abbrev secondF (f : PR 2) : PR 2 := Diff f L₂
abbrev thirdF (f : PR 2) : PR 2 := Diff f L₃

def data1 (A B R x : PTm n) : PTm n := dd x (d₁ A B R)
def data2 (A B R x : PTm n) : PTm n := dd x (d₂ A B R)
def data3 (A B x : PTm n) : PTm n := dd x (d₃ A B)

@[simp] theorem subst_data1 {m : ℕ} (σ : Fin n → PTm m) (A B R x : PTm n) :
    Syn.subst σ (data1 A B R x) = data1 (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) (Syn.subst σ x) := by
  simp [data1]

@[simp] theorem subst_data2 {m : ℕ} (σ : Fin n → PTm m) (A B R x : PTm n) :
    Syn.subst σ (data2 A B R x) = data2 (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) (Syn.subst σ x) := by
  simp [data2]

@[simp] theorem subst_data3 {m : ℕ} (σ : Fin n → PTm m) (A B x : PTm n) :
    Syn.subst σ (data3 A B x) = data3 (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) := by simp [data3]

theorem first_regular (f : PR 2) (A B R x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x)
    (hd : Γ ⊢[PRAAx] disk (center A B) R B) : Γ ⊢[PRAAx] pointCN (firstF f) (data1 A B R x) :=
  GaussianNamedDifference.name_regular f L₁ x _ hx (GaussianBarnesCanonicalPositiveFirstLogarithm.regular A B R hd)

theorem second_regular (f : PR 2) (A B R x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x)
    (hd : Γ ⊢[PRAAx] disk (center A B) R B) : Γ ⊢[PRAAx] pointCN (secondF f) (data2 A B R x) :=
  GaussianNamedDifference.name_regular f L₂ x _ hx (GaussianBarnesCanonicalPositiveSecondLogarithm.regular A B R hd)

theorem third_regular (f : PR 2) (A B x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x)
    (hd : Γ ⊢[PRAAx] GaussianBarnesCanonicalThirdLogarithmCofinal.source A B) :
    Γ ⊢[PRAAx] pointCN (thirdF f) (data3 A B x) :=
  GaussianNamedDifference.name_regular f L₃ x _ hx (GaussianBarnesCanonicalThirdLogarithmCofinal.regular A B hd)

private theorem zero_radius (f : PR 2) (A B R x P T : PTm n)
    (ha : Γ ⊢[PRAAx] le one A) (hb : Γ ⊢[PRAAx] le one B) (hr : Γ ⊢[PRAAx] disk (center A B) R B)
    (hx : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f x P T) :
    Γ ⊢[PRAAx] crossEquivalent (J₀ f) (J₀ f) (data0 A B x P) (dd (logd x P) (ld A B R)) := by
  let F := GaussianBarnesCanonicalPositiveLogarithm.default_source A B ha hb
  have hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalPositiveLogarithm.source A B R := .andI ha hr
  have rx := GaussianNamedPositiveLogarithm.name_regular f x P T hx
  exact GaussianNamedDifferenceQuotientProperness.difference_proper (Log f) (Log f) L L
    (logd x P) (logd x P) (ld A B (A+B)) (ld A B R) rx rx
    (GaussianBarnesCanonicalPositiveLogarithm.regular A B (A+B) F)
    (GaussianBarnesCanonicalPositiveLogarithm.regular A B R hs) (cross_refl _ _ rx)
    (GaussianBarnesCanonicalPositiveLogarithmRealAxis.proper A B A B (A+B) R F hs (.eqRefl _))

theorem first_rate (f g : PR 2) (p A C B R K x y P T U V a : PTm n)
    (h : Γ ⊢[PRAAx] chart p A C B R K)
    (hx : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f x P T)
    (hy : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f y U V)
    (ha : Γ ⊢[PRAAx] pointCN g a)
    (hc : Γ ⊢[PRAAx] independentRate (Q (Log f) (Log f)) g
      (qd (Log f) (Log f) (logd y U) (logd x P) (step A C) B) a one (unit p)) : Γ ⊢[PRAAx]
    independentRate (Q (J₀ f) (J₀ f)) (firstF g)
      (qd (J₀ f) (J₀ f) (data0 C B y U) (data0 A B x P) (step A C) B) (data1 A B R a) two (unit p) := by
  let F := J₀ f
  let G := firstF g
  let s := step A C
  let d := data1 A B R a
  let u := data0 C B y U
  let v := data0 A B x P
  let uR := dd (logd y U) (ld C B R)
  let vR := dd (logd x P) (ld A B R)
  have margin := h.andE₁.andE₁
  have b := margin.andE₁
  have aPos := margin.andE₂.andE₁
  have cPos := margin.andE₂.andE₂.andE₁
  have aDisk := h.andE₁.andE₂.andE₁
  have cDisk := h.andE₁.andE₂.andE₂
  have xreg := GaussianNamedPositiveLogarithm.name_regular f x P T hx
  have yreg := GaussianNamedPositiveLogarithm.name_regular f y U V hy
  have areg := GaussianBarnesCanonicalPositiveLogarithm.regular A B R (.andI aPos aDisk)
  have creg := GaussianBarnesCanonicalPositiveLogarithm.regular C B R (.andI cPos cDisk)
  have greg := first_regular g A B R a ha aDisk
  have canonical := (GaussianBarnesCanonicalPositiveLogarithmCalculus.dyadic_rates p A C B R K h).andE₁
  have raw := GaussianBarnesVignerasDifferenceQuotientAlgebra.dyadic_rate (Log f) L g L₁
    (logd y U) (logd x P) (ld C B R) (ld A B R) a (d₁ A B R) s B p yreg xreg creg areg
    ha (GaussianBarnesCanonicalPositiveFirstLogarithm.regular A B R aDisk) (.andI b h.andE₂.andE₁) hc canonical
  have e := GaussianNamedDifferenceQuotientProperness.proper F F F F u uR v vR s B
    (GaussianBarnesVignerasLogQuotient.regular f C B y U V cPos b hy)
    (GaussianNamedDifference.name_regular (Log f) L _ _ yreg creg)
    (GaussianBarnesVignerasLogQuotient.regular f A B x P T aPos b hx)
    (GaussianNamedDifference.name_regular (Log f) L _ _ xreg areg)
    (zero_radius f C B R y U V cPos b cDisk hy) (zero_radius f A B R x P T aPos b aDisk hx)
  exact GaussianNamedRateTransport.transport (Q F F) G (Q F F) G (qd F F uR vR s B) d
    (qd F F u v s B) d two (unit p) (unit_positive p) raw e (cross_refl _ _ greg)

theorem second_rate (f g : PR 2) (p A C B R K x y a : PTm n)
    (h : Γ ⊢[PRAAx] chart p A C B R K) (hx : Γ ⊢[PRAAx] pointCN f x)
    (hy : Γ ⊢[PRAAx] pointCN f y) (ha : Γ ⊢[PRAAx] pointCN g a)
    (hc : Γ ⊢[PRAAx] independentRate (Q f f) g (qd f f y x (step A C) B) a one (unit p)) : Γ ⊢[PRAAx]
    independentRate (Q (firstF f) (firstF f)) (secondF g)
      (qd (firstF f) (firstF f) (data1 C B R y) (data1 A B R x) (step A C) B) (data2 A B R a) two (unit p) :=
  GaussianBarnesVignerasDifferenceQuotientAlgebra.dyadic_rate f L₁ g L₂ y x (d₁ C B R) (d₁ A B R) a (d₂ A B R)
    (step A C) B p hy hx
    (GaussianBarnesCanonicalPositiveFirstLogarithm.regular C B R h.andE₁.andE₂.andE₂)
    (GaussianBarnesCanonicalPositiveFirstLogarithm.regular A B R h.andE₁.andE₂.andE₁) ha
    (GaussianBarnesCanonicalPositiveSecondLogarithm.regular A B R h.andE₁.andE₂.andE₁)
    (.andI h.andE₁.andE₁.andE₁ h.andE₂.andE₁) hc
    (GaussianBarnesCanonicalPositiveLogarithmCalculus.dyadic_rates p A C B R K h).andE₂.andE₁

theorem third_rate (f g : PR 2) (p A C B R K x y a : PTm n)
    (h : Γ ⊢[PRAAx] chart p A C B R K) (hx : Γ ⊢[PRAAx] pointCN f x)
    (hy : Γ ⊢[PRAAx] pointCN f y) (ha : Γ ⊢[PRAAx] pointCN g a)
    (hc : Γ ⊢[PRAAx] independentRate (Q f f) g (qd f f y x (step A C) B) a one (unit p)) : Γ ⊢[PRAAx]
    independentRate (Q (secondF f) (secondF f)) (thirdF g)
      (qd (secondF f) (secondF f) (data2 C B R y) (data2 A B R x) (step A C) B) (data3 A B a) two (unit p) :=
  GaussianBarnesVignerasDifferenceQuotientAlgebra.dyadic_rate f L₂ g L₃ y x (d₂ C B R) (d₂ A B R) a (d₃ A B)
    (step A C) B p hy hx
    (GaussianBarnesCanonicalPositiveSecondLogarithm.regular C B R h.andE₁.andE₂.andE₂)
    (GaussianBarnesCanonicalPositiveSecondLogarithm.regular A B R h.andE₁.andE₂.andE₁) ha
    (GaussianBarnesCanonicalThirdLogarithmCofinal.regular A B
      (.andI h.andE₁.andE₁.andE₂.andE₁ h.andE₁.andE₁.andE₁))
    (.andI h.andE₁.andE₁.andE₁ h.andE₂.andE₁) hc
    (GaussianBarnesCanonicalPositiveLogarithmCalculus.dyadic_rates p A C B R K h).andE₂.andE₂

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasQuotientJet
