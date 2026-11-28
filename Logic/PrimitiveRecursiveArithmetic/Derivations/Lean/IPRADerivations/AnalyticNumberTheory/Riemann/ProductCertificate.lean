import IPRADerivations.AnalyticNumberTheory.Riemann.ObjectForms

/-! Imported from the packet `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`,
`ProductCertificate.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! A multiplicative certificate: the shifted excesses have product one
on every initial interval.  The equivalences are object-level derivations. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.ProductCertificate
open LeanProofs.ConciseIPRA Syn PacketLanguage
open PTm (app zero succ)
open scoped Fm
open LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PacketAudit renaming upShiftTerm → upShift
variable {n m k : Nat} {Γ : List (Fm PTm n)}

private def pair {α : Type} (x y : α) : Fin 2 → α := Fin.cases x (fun _ => y)
private def four {α : Type} (a b c d : α) : Fin 4 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))
private def five {α : Type} (a b c d e : α) : Fin 5 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (fun _ => e))))
private def one : PTm n := succ zero
private def mult (x y : PTm n) := app mulR (pair x y)
private theorem congrApp (f : PR k) {xs ys : Fin k → PTm n}
    (h : ∀ i, Prf PRAAx Γ (xs i ≐ ys i)) :
    Prf PRAAx Γ (app f xs ≐ app f ys) := by
  simpa using Prf.eqCongr (app f (var : Fin k → PTm k)) h
private theorem congrS {x y : PTm n} (h : Prf PRAAx Γ (x ≐ y)) :
    Prf PRAAx Γ (succ x ≐ succ y) := congrApp .succ (fun _ => h)
private theorem congrM {a b c d : PTm n}
    (ha : Prf PRAAx Γ (a ≐ b)) (hc : Prf PRAAx Γ (c ≐ d)) :
    Prf PRAAx Γ (mult a c ≐ mult b d) := congrApp _ (Fin.cases ha (fun _ => hc))
private theorem cZero (xs : Fin k → PTm n) : Prf PRAAx Γ (app zeroR xs ≐ zero) :=
  Prf.eqTrans (PRA.comp _ _ xs) (congrApp .zero (fun i => i.elim0))
private theorem cOne (xs : Fin k → PTm n) : Prf PRAAx Γ (app (sucR zeroR) xs ≐ one) :=
  Prf.eqTrans (PRA.comp _ _ xs) (congrS (cZero xs))

private theorem multOne (a : PTm n) : Prf PRAAx Γ (mult one a ≐ a) := by
  let z := mult zero a
  have hz : Prf PRAAx Γ (z ≐ zero) := Prf.eqTrans (PRA.precZero _ _ (fun _ => a))
    (cZero (fun _ => a))
  let xs : Fin 3 → PTm n := Fin.cases zero (Fin.cases z (fun _ => a))
  apply Prf.eqTrans (PRA.precSucc _ _ zero (fun _ => a))
  apply Prf.eqTrans (PRA.comp _ _ xs)
  apply Prf.eqTrans (congrApp addR (ys := pair zero a) (Fin.cases (Prf.eqTrans (PRA.proj 1 xs) hz)
    (fun _ => PRA.proj 2 xs)))
  exact Prf.eqTrans (PRA.precZero _ _ (fun _ => a)) (PRA.proj 0 _)

private def takeSample (f : PR 5) : PR 6 := .comp f (fun i => .proj (five 2 3 4 5 0 i))
private def update (f : PR 5) : PR 6 :=
  .comp mulR (pair (.proj 1) (sucR (takeSample f)))

/-- Cutoff first, with the polynomial parameters following it. -/
def prefixCode (f : PR 5) : PR 5 := .prec (sucR zeroR) (update f)
def prefixAt (f : PR 5) (p : Fin 4 → PTm n) (t : PTm n) := app (prefixCode f) (Fin.cases t p)
private def dataAt (f : PR 5) (p : Fin 4 → PTm n) (i : PTm n) :=
  app f (five (p 0) (p 1) (p 2) (p 3) i)

private theorem atZero (f : PR 5) (p : Fin 4 → PTm n) :
    Prf PRAAx Γ (prefixAt f p zero ≐ one) := Prf.eqTrans (PRA.precZero _ _ p) (cOne p)
private theorem atSucc (f : PR 5) (p : Fin 4 → PTm n) (t : PTm n) :
    Prf PRAAx Γ (prefixAt f p (succ t) ≐ mult (prefixAt f p t) (succ (dataAt f p t))) := by
  let xs : Fin 6 → PTm n := Fin.cases t (Fin.cases (prefixAt f p t) p)
  apply Prf.eqTrans (PRA.precSucc _ _ t p)
  apply Prf.eqTrans (PRA.comp _ _ xs)
  apply congrApp mulR
  refine Fin.cases (PRA.proj 1 xs) (fun _ => ?_)
  apply Prf.eqTrans (PRA.comp _ _ xs)
  apply congrS
  apply Prf.eqTrans (PRA.comp _ _ xs)
  apply congrApp f
  exact Fin.cases (PRA.proj 2 xs) (fun i => Fin.cases (PRA.proj 3 xs) (fun j =>
    Fin.cases (PRA.proj 4 xs) (fun l => Fin.cases (PRA.proj 5 xs) (fun _ => PRA.proj 0 xs) l) j) i)

private def raised (p : Fin 4 → PTm n) : Fin 4 → PTm (n+1) := fun i => Syn.shift (p i)
@[simp] private theorem subPrefix (f : PR 5) (p : Fin 4 → PTm n) (t : PTm n)
    (σ : Fin n → PTm m) : subst σ (prefixAt f p t) =
      prefixAt f (fun i => subst σ (p i)) (subst σ t) := by
  apply congrArg (app _); exact funext (Fin.cases rfl (fun _ => rfl))
@[simp] private theorem subOne (σ : Fin n → PTm m) : subst σ (one : PTm n) = one := by
  simp [one]
private theorem replShift (t : PTm (n+1)) (a : PTm n) :
    subst (repl t) (Syn.shift a) = Syn.shift a := by rw [Syn.subst_shift]; rfl

private def point (f : PR 5) (p : Fin 4 → PTm n) : Fm PTm n :=
  .all (dataAt f (raised p) (var 0) ≐ zero)
def criterion (f : PR 5) (p : Fin 4 → PTm n) : Fm PTm n :=
  .all (prefixAt f (raised p) (var 0) ≐ one)

theorem equivalence (f : PR 5) (p : Fin 4 → PTm n) :
    Prf PRAAx [] (Fm.iff (point f p) (criterion f p)) := by
  apply Prf.iffI
  · apply Prf.impI
    let P : Fm PTm (n+1) := prefixAt f (raised p) (var 0) ≐ one
    apply PRA.qfInd P trivial
    · simpa [P,raised] using atZero (Γ := [point f p]) f p
    · have h := (Prf.allOpen (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := point f p))).wk (ψ := P)
      simp only [P,Fm.subst_eq,subPrefix,subOne,subst_var,repl_zero,raised,replShift]
      exact Prf.eqTrans (atSucc f (raised p) (var 0)) (Prf.eqTrans
        (congrM (Prf.hyp0 (φ := P)) (congrS h)) (multOne one))
  · apply Prf.impI
    apply Prf.allI
    have h := (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := criterion f p)).shift
    have hs : (criterion f p).shift = criterion f (raised p) := by
      unfold Fm.shift criterion raised
      simp only [Fm.subst_all,Fm.subst_eq,subPrefix,subOne,subst_var,up_zero,upShift]
      rfl
    rw [hs] at h
    have atTerm (t : PTm (n+1)) : Prf PRAAx [(criterion f p).shift] (prefixAt f (raised p) t ≐ one) := by
      have hh := Prf.allE t h
      simp only [criterion,Fm.subst_eq,subPrefix,subOne,subst_var,inst_zero,raised,subst_inst_shift] at hh
      exact hh
    let x := dataAt f (raised p) (var 0)
    have hsx : Prf PRAAx [(criterion f p).shift] (succ x ≐ succ zero) := Prf.eqTrans
      (Prf.eqSymm (multOne (succ x))) (Prf.eqTrans (congrM (Prf.eqSymm (atTerm (var 0))) (Prf.eqRefl _))
        (Prf.eqTrans (Prf.eqSymm (atSucc f (raised p) (var 0))) (atTerm (succ (var 0)))))
    have inj := Prf.ax (Γ := [(criterion f p).shift]) PRAAx.succInj (pair x zero)
    exact Prf.impE (by simpa [pair] using inj) hsx

private theorem liftAll {A B : Fm PTm (n+1)} (h : Prf PRAAx [] (Fm.iff A B)) :
    Prf PRAAx [] (Fm.iff (.all A) (.all B)) :=
  Prf.iffI (Prf.impI (Prf.allI (Prf.iffMp (Prf.ofNil h) (Prf.allOpen Prf.hyp0))))
    (Prf.impI (Prf.allI (Prf.iffMpr (Prf.ofNil h) (Prf.allOpen Prf.hyp0))))

def RH := criterion excess (four (zero : PTm 0) zero zero (succ zero))
def GRH : Fm PTm 0 := .all (criterion excess (four (var 0) zero zero (succ zero)))
def ERH : Fm PTm 0 := .all (.all (.all (.all
    (criterion excess (four (var 3) (var 2) (var 1) (var 0))))))

theorem rh_iff : Prf PRAAx [] (Fm.iff RiemannIPRA.RH RH) := by
  have e : RiemannIPRA.RH = point excess (four (zero : PTm 0) zero zero (succ zero)) := by
    simp [RiemannIPRA.RH,RHHierarchy.RHOf,RHHierarchy.atom,point,dataAt,raised,four]
    rfl
  rw [e]
  exact equivalence _ _

theorem grh_iff : Prf PRAAx [] (Fm.iff RiemannIPRA.GRH GRH) := by
  have e : RiemannIPRA.GRH = .all (point excess (four (var 0) zero zero (succ zero))) := by
    simp [RiemannIPRA.GRH,RHHierarchy.GRHOf,RHHierarchy.atom,point,dataAt,raised,four]
    rfl
  rw [e]
  exact liftAll (equivalence _ _)

theorem erh_iff : Prf PRAAx [] (Fm.iff RiemannIPRA.ERH ERH) := by
  have e : RiemannIPRA.ERH = .all (.all (.all (.all
      (point excess (four (var 3) (var 2) (var 1) (var 0)))))) := by
    simp [RiemannIPRA.ERH,RHHierarchy.ERHOf,RHHierarchy.atom,point,dataAt,raised,four]
    rfl
  rw [e]
  exact liftAll (liftAll (liftAll (liftAll (equivalence _ _))))

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.ProductCertificate
