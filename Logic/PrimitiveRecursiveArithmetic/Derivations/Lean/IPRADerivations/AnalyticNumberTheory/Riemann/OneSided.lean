import IPRADerivations.AnalyticNumberTheory.Riemann.UniversalCriteria
import IPRADerivations.AnalyticNumberTheory.Riemann.GridInterpolation

/-! Imported from the packet `analytic-number-theory/riemann_ipra_formalization_2026-11-20`,
`OneSided.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Nonnegative and nonpositive excursions of the polynomial prime-product
discrepancy. All three splitting theorems are internal iPRA derivations. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.OneSided
open LeanProofs.ConciseIPRA Syn PacketLanguage Discrete
open scoped Fm
open PTm (app zero succ)

def positivePart : PR 5 := program ["d","H","u","v","t"] <|
  let n := v "t"+100
  let logAt := fun x => call logProduct [v "d"+1,v "H",v "u",v "v",x]
  logAt (2*n) - 2*logAt n

private def choose : PR 3 := .prec (.proj 0) (.proj 3)
private def triple {α : Type} (z a b : α) : Fin 3 → α :=
  Fin.cases z (Fin.cases a (fun _ => b))

/-- At positive D keep the full excess in the upper row. At D ≤ 0 keep it in
the lower row. This partitions exact ties without duplicating positive failures. -/
def matrix (upper : Bool) : PR 5 :=
  .comp choose (if upper then triple positivePart zeroR excess
                else triple positivePart excess zeroR)

def statement (f : Family) (upper : Bool) : Fm PTm 0 := f.close (matrix upper)

private def pick {n} (z a b : PTm n) := app choose (triple z a b)
private def pairLaw {n} (z a b : PTm n) : Fm PTm n :=
  Fm.iff (a ≐ zero) ((pick z b a ≐ zero) ⋏ (pick z a b ≐ zero))

variable {n m : Nat} {Γ : List (Fm PTm n)}

@[simp] private theorem subPick (σ : Fin n → PTm m) (z a b : PTm n) :
    subst σ (pick z a b) = pick (subst σ z) (subst σ a) (subst σ b) := by
  apply congrArg (app _)
  exact funext (Fin.cases rfl (fun i => Fin.cases rfl (fun _ => rfl) i))

@[simp] private theorem subLaw (σ : Fin n → PTm m) (z a b : PTm n) :
    (pairLaw z a b).subst σ = pairLaw (subst σ z) (subst σ a) (subst σ b) := by
  simp [pairLaw,Fm.iff]

private theorem atZero (a b : PTm n) : Prf PRAAx Γ (pick zero a b ≐ a) :=
  Prf.eqTrans (PRA.precZero _ _ (Fin.cases a (fun _ => b))) (PRA.proj 0 _)

private theorem atSucc (z a b : PTm n) : Prf PRAAx Γ (pick (succ z) a b ≐ b) :=
  Prf.eqTrans (PRA.precSucc _ _ z (Fin.cases a (fun _ => b))) (PRA.proj 3 _)

private theorem base (a : PTm n) : Prf PRAAx Γ (pairLaw zero a zero) := by
  apply Prf.iffI
  · exact Prf.impI (Prf.andI (atZero _ _) (Prf.eqTrans (atZero _ _) Prf.hyp0))
  · exact Prf.impI (Prf.eqTrans (Prf.eqSymm (atZero _ _)) (Prf.andE₂ Prf.hyp0))

private theorem step (z a : PTm n) : Prf PRAAx Γ (pairLaw (succ z) a zero) := by
  apply Prf.iffI
  · exact Prf.impI (Prf.andI (Prf.eqTrans (atSucc _ _ _) Prf.hyp0) (atSucc _ _ _))
  · exact Prf.impI (Prf.eqTrans (Prf.eqSymm (atSucc _ _ _)) (Prf.andE₁ Prf.hyp0))

@[simp] private theorem replShift (s : PTm (n+1)) (a : PTm n) :
    subst (repl s) (Syn.shift a) = Syn.shift a := by
  rw [Syn.subst_shift]; rfl

private theorem law (z a : PTm n) : Prf PRAAx Γ (pairLaw z a zero) := by
  let P := pairLaw (var 0) (Syn.shift a) zero
  have h : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P
    · exact ⟨⟨trivial,trivial,trivial⟩,⟨⟨trivial,trivial⟩,trivial⟩⟩
    · simpa [P] using base (Γ := Γ) a
    · simpa [P] using
        step (Γ := P :: Γ.map Fm.shift) (var 0) (Syn.shift a)
  simpa [P] using Prf.allE z h

private theorem congrApp (f : PR m) {xs ys : Fin m → PTm n}
    (h : ∀ i, Prf PRAAx Γ (xs i ≐ ys i)) : Prf PRAAx Γ (app f xs ≐ app f ys) := by
  simpa using Prf.eqCongr (app f (var : Fin m → PTm m)) h

private theorem zeroAt (s : Fin 5 → PTm n) : Prf PRAAx Γ (app zeroR s ≐ zero) :=
  Prf.eqTrans (PRA.comp _ _ _) (congrApp .zero (fun i => i.elim0))

private theorem upperAt (s : Fin 5 → PTm n) :
    Prf PRAAx Γ (app (matrix true) s ≐ pick (app positivePart s) zero (app excess s)) := by
  apply Prf.eqTrans (PRA.comp _ _ _)
  exact congrApp _ (Fin.cases (Prf.eqRefl _) (fun i => Fin.cases (zeroAt _) (fun _ => Prf.eqRefl _) i))

private theorem lowerAt (s : Fin 5 → PTm n) :
    Prf PRAAx Γ (app (matrix false) s ≐ pick (app positivePart s) (app excess s) zero) := by
  apply Prf.eqTrans (PRA.comp _ _ _)
  exact congrApp _ (Fin.cases (Prf.eqRefl _) (fun i => Fin.cases (Prf.eqRefl _) (fun _ => zeroAt _) i))

private theorem atomPair (s : Fin 5 → PTm n) :
    Prf PRAAx [] (Fm.iff (app excess s ≐ zero)
      ((app (matrix true) s ≐ zero) ⋏ (app (matrix false) s ≐ zero))) := by
  apply Prf.iffI
  · apply Prf.impI
    have h := Prf.iffMp (law (app positivePart s) (app excess s)) (Prf.hyp0 (Γ := []))
    exact Prf.andI (Prf.eqTrans (upperAt s) (Prf.andE₁ h)) (Prf.eqTrans (lowerAt s) (Prf.andE₂ h))
  · apply Prf.impI
    apply Prf.iffMpr (law (app positivePart s) (app excess s))
    exact Prf.andI (Prf.eqTrans (Prf.eqSymm (upperAt s)) (Prf.andE₁ Prf.hyp0))
      (Prf.eqTrans (Prf.eqSymm (lowerAt s)) (Prf.andE₂ Prf.hyp0))

private theorem allPair {a u l : Fm PTm (n+1)}
    (h : Prf PRAAx [] (Fm.iff a (u ⋏ l))) :
    Prf PRAAx [] (Fm.iff (.all a) ((.all u) ⋏ (.all l))) := by
  apply Prf.iffI
  · apply Prf.impI
    have p := Prf.iffMp (Prf.ofNil h) (Prf.allOpen (Prf.hyp0 (Γ := []) (φ := Fm.all a)))
    exact Prf.andI (Prf.allI (Prf.andE₁ p)) (Prf.allI (Prf.andE₂ p))
  · apply Prf.impI
    apply Prf.allI
    exact Prf.iffMpr (Prf.ofNil h) (Prf.andI (Prf.allOpen (Prf.andE₁ Prf.hyp0))
      (Prf.allOpen (Prf.andE₂ Prf.hyp0)))

/-- Combining the two arithmetic signs recovers the exact original packet
in the first-order calculus. The individual analytic converses are in the paper. -/
theorem split (f : Family) : Prf PRAAx [] (Fm.iff (f.close excess)
    (statement f true ⋏ statement f false)) := by
  cases f with
  | riemann => exact allPair (atomPair _)
  | dirichlet => exact allPair (allPair (atomPair _))
  | dedekind => exact allPair (allPair (allPair (allPair (allPair (atomPair _)))))

def sideSize (p : Data) (upper : Bool) (n : Nat) : Nat :=
  if upper then p.logP (2*n) - 2*p.logP n else 2*p.logP n - p.logP (2*n)

private theorem runPick (z a b : Nat) :
    value choose (triple z a b) = if z = 0 then a else b := by cases z <;> rfl

private theorem selectRead (x a b : PR 5) (e : Fin 5 → Nat) :
    value (.comp choose (triple x a b)) e =
      if value x e = 0 then value a e else value b e := by
  rw [value]
  have h : (fun i => value (triple x a b i) e) = triple (value x e) (value a e) (value b e) := by
    exact funext (Fin.cases rfl (fun i => Fin.cases rfl (fun _ => rfl) i))
  rw [h, runPick]

private theorem posRead (p : Data) (t : Nat) :
    value positivePart (p.args t) = sideSize p true (t+100) := by
  unfold positivePart
  rw [value_program]
  simp only [minus,times,apply5,plus]
  rfl

theorem sideRead (p : Data) (t : Nat) (upper : Bool) :
    value (matrix upper) (p.args t) = 0 ↔ sideSize p upper (t+100)^2 ≤ p.cost (t+100) := by
  let n := t + 100
  have full := read_test p t
  change value excess (p.args t) = 0 ↔
    ((p.logP (2*n)-2*p.logP n)+(2*p.logP n-p.logP (2*n)))^2 ≤ p.cost n at full
  have selected (u : Bool) : value (matrix u) (p.args t) =
      if sideSize p true n = 0 then (if u then 0 else value excess (p.args t)) else
        (if u then value excess (p.args t) else 0) := by
    cases u <;> simp only [matrix, Bool.false_eq_true, if_false, if_true, selectRead, posRead, value_zeroR, n]
  rw [selected]
  change (if p.logP (2*n)-2*p.logP n = 0 then _ else _) = 0 ↔ _
  rcases Nat.le_total (p.logP (2*n)) (2*p.logP n) with h | h
  · have hz := Nat.sub_eq_zero_of_le h
    cases upper <;> simp_all [sideSize,n]
  · have hz := Nat.sub_eq_zero_of_le h
    by_cases he : p.logP (2*n) = 2*p.logP n
    · cases upper <;> simp_all [sideSize,n]
    · have hn : p.logP (2*n)-2*p.logP n ≠ 0 := by omega
      cases upper <;> simp_all [sideSize,n]

theorem reading (f : Family) (upper : Bool) :
    naturalTerms.Holds (statement f upper) Fin.elim0 ↔
      f.allData fun p => ∀ t, sideSize p upper (t+100)^2 ≤ p.cost (t+100) :=
  (f.holds_matrix _).trans (f.lift_iff fun p => forall_congr' fun t => sideRead p t upper)

inductive Grid where | all | squares | logSquares

def steps : PR 1 := program ["j"] <| sumTo "i" (v "j") (1+call logCode [v "i"+1])

/-- Offset above 100 for the selected sample. -/
def offset : Grid → PR 1
  | .all => .proj 0
  | .squares => program ["j"] <| v "j"*v "j"+20*v "j"
  | .logSquares => program ["j"] <|
      let q := call steps [v "j"]
      q*q+20*q

def sampled (f : Family) (u : Bool) (g : Grid) : Fm PTm 0 :=
  f.close (.comp (matrix u) (Fin.cases (.proj 0) (Fin.cases (.proj 1)
    (Fin.cases (.proj 2) (Fin.cases (.proj 3) (fun _ => .comp (offset g) (fun _ => .proj 4)))))))

theorem sampled_reading (f : Family) (u : Bool) (g : Grid) :
    naturalTerms.Holds (sampled f u g) Fin.elim0 ↔
      f.allData fun p => ∀ j, sideSize p u (value (offset g) (fun _ => j)+100)^2 ≤
        p.cost (value (offset g) (fun _ => j)+100) := by
  apply (f.holds_matrix _).trans
  apply f.lift_iff
  intro p
  apply forall_congr'
  intro j
  rw [value]
  convert sideRead p (value (offset g) (fun _ => j)) u using 3
  funext i
  obtain ⟨i,hi⟩ := i
  match i with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | k+5 => omega

theorem sampled_first_failure (f : Family) (u : Bool) (g : Grid) :
    Prf PRAAx [] (Fm.iff (RHCounterexamples.counter (sampled f u g))
      (UniversalCriteria.block (sampled f u g)).firstRadius) :=
  UniversalCriteria.firstFailure (UniversalCriteria.five f _)


/-- Each new cutoff visits a single polynomial, selected by the valuations of
j+1. The four primes guarantee periodic return to every code. -/
private def valTerm (p : Nat) : PTm 1 :=
  app ((program ["j"] (call DivisorMatrices.valuation [E.num p,v "j"+1]))) (fun _ => var 0)

private def timeTerm (g : Grid) : PTm 1 := app (offset g) (fun _ => var 0)

private def fieldTerms (f : Family) : Fin 4 → PTm 1 := match f with
  | .riemann => Fin.cases zero (Fin.cases zero (Fin.cases zero (fun _ => succ zero)))
  | .dirichlet => Fin.cases (valTerm 2) (Fin.cases zero (Fin.cases zero (fun _ => succ zero)))
  | .dedekind => Fin.cases (valTerm 2) (Fin.cases (valTerm 3) (Fin.cases (valTerm 5) (fun _ => valTerm 7)))

def rotating (f : Family) (u : Bool) (g : Grid) : Fm PTm 0 :=
  let x := fieldTerms f
  .all (RHHierarchy.atom (matrix u) (x 0) (x 1) (x 2) (x 3) (timeTerm g))

private theorem subAtom {m n : Nat} (σ : Fin n → PTm m) (k : PR 5) (a b c d t : PTm n) :
    (RHHierarchy.atom k a b c d t).subst σ =
      RHHierarchy.atom k (subst σ a) (subst σ b) (subst σ c) (subst σ d) (subst σ t) := by
  simp only [RHHierarchy.atom, Fm.subst_eq, PTm.subst_app, PTm.subst_zero]
  congr 2
  funext i
  refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i =>
    Fin.cases rfl (fun _ => rfl) i) i) i) i

@[simp] private theorem subsUpShift (σ : Fin n → PTm m) (t : PTm n) :
    subst (up σ) (Syn.shift t) = Syn.shift (subst σ t) := by
  simp [Syn.subst_shift, Syn.shift_subst]

private theorem justOpen {q} {Γ : List (Fm PTm q)} {A : Fm PTm (q+1)}
    (t : PTm q) (h : Prf PRAAx Γ (.all A)) : Prf PRAAx Γ (A.subst (inst t)) := Prf.allE t h

theorem to_rotating (f : Family) (u : Bool) (g : Grid) :
    Prf PRAAx [] (.imp (statement f u) (rotating f u g)) := by
  apply Prf.impI
  apply Prf.allI
  let t := timeTerm g
  let x := valTerm
  have start := Prf.shift (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := statement f u))
  cases f with
  | riemann =>
    have h := justOpen t start
    simpa [t,statement,Family.close,RHHierarchy.RHOf, Fm.shift, subAtom,
      Fm.subst_all,Syn.up,Syn.inst,fieldTerms] using h
  | dirichlet =>
    have h := justOpen t (justOpen (x 2) start)
    simpa [x,t,statement,Family.close,RHHierarchy.GRHOf, Fm.shift, subAtom,
      Fm.subst_all,Syn.up,Syn.inst,fieldTerms] using h
  | dedekind =>
    have h := justOpen t (justOpen (x 7) (justOpen (x 5) (justOpen (x 3) (justOpen (x 2) start))))
    simpa [x,t,statement,Family.close,RHHierarchy.ERHOf, Fm.shift, subAtom,
      Fm.subst_all,Syn.up,Syn.inst,fieldTerms] using h

def valuationAt (p j : Nat) : Nat :=
  value DivisorMatrices.valuation (Fin.cases p (fun _ => j+1))

def selectedData (f : Family) (j : Nat) : Data := match f with
  | .riemann => ⟨0,0,0,1⟩
  | .dirichlet => ⟨valuationAt 2 j,0,0,1⟩
  | .dedekind => ⟨valuationAt 2 j,valuationAt 3 j,valuationAt 5 j,valuationAt 7 j⟩

private theorem valRead (p j : Nat) : termValue (valTerm p) (fun _ => j) = valuationAt p j := by
  change value (program _ _) _ = _
  rw [value_program]
  unfold valuationAt
  apply congrArg (value _)
  funext i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun h => h.elim0) k) i
  · rfl
  · exact plus _ _ _

/-- Number of bits in the concatenated ordinary binary representations of 1..j. -/
def lengths : Nat → Nat
  | 0 => 0
  | j+1 => lengths j + (1+(j+1).log2)

private theorem readLog {ctx} (a : E ctx) (e) :
    denote (call logCode [a]) e = (denote a e).log2 := by
  change value logCode _ = _
  rw [value_logCode]
  rfl

theorem steps_read (j : Nat) : value steps (fun _ => j) = lengths j := by
  unfold steps
  rw [value_program]
  change overRange 0 (fun i a => a + denote _ _) j = _
  simp only [plus,readLog]
  change overRange 0 (fun i a => a+(1+(i+1).log2)) j = _
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (·+(1+(j+1).log2)) ih

private theorem run1 {ctx} (f : PR 1) (a : E ctx) (e) :
    denote (call f [a]) e = value f (fun _ => denote a e) := by
  apply congrArg (value f)
  exact funext (Fin.cases rfl (fun i => i.elim0))

theorem grid_reading (g : Grid) (j : Nat) : value (offset g) (fun _ => j)+100 =
    match g with
    | .all => j+100
    | .squares => (10+j)^2
    | .logSquares => (10+lengths j)^2 := by
  cases g with
  | all => rfl
  | squares =>
    simp only [offset,value_program,plus,times]
    change j*j+20*j+100 = (10+j)^2
    simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add]
    omega
  | logSquares =>
    simp only [offset,value_program,plus,times,run1,steps_read]
    change lengths j*lengths j+20*lengths j+100 = (10+lengths j)^2
    simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add]
    omega

/-- The actual PR cutoff is the same square used in the interpolation estimates. -/
theorem compiled_log_grid (j : Nat) :
    value (offset .logSquares) (fun _ => j)+100 = GridInterpolation.grid j := by
  have hr (n : Nat) : 10+lengths n = GridInterpolation.root n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [lengths, ← Nat.add_assoc, ih, GridInterpolation.root]
  exact (grid_reading .logSquares j).trans (congrArg (·^2) (hr j))

/-- At every scheduled return, the compiled selector chooses the requested
four polynomial parameters, in their original order. -/
theorem selectedData_return (a b c d h : Nat) :
    selectedData .dedekind (GridInterpolation.returnTime a b c d h - 1) = ⟨a,b,c,d⟩ := by
  let N := GridInterpolation.returnTime a b c d h
  have hn : 0 < N := by unfold N GridInterpolation.returnTime GridInterpolation.mass; positivity
  have hs : N-1+1=N := by omega
  unfold selectedData valuationAt
  change Data.mk _ _ _ _ = _
  simp only [show GridInterpolation.returnTime a b c d h-1+1 = N from hs]
  exact congrArg (fun z : Nat × Nat × Nat × Nat => Data.mk z.1 z.2.1 z.2.2.1 z.2.2.2)
    (GridInterpolation.clock_return a b c d h)

theorem rotating_reading (f : Family) (u : Bool) (g : Grid) :
    naturalTerms.Holds (rotating f u g) Fin.elim0 ↔ ∀ j,
      let p := selectedData f j
      let n := value (offset g) (fun _ => j)+100
      sideSize p u n ^ 2 ≤ p.cost n := by
  apply forall_congr'; intro j
  let p := selectedData f j
  let n := value (offset g) (fun _ => j)
  apply Iff.trans _ (sideRead p n u)
  change value (matrix u) _ = 0 ↔ value (matrix u) (p.args n) = 0
  suffices h : (fun i => termValue
        (Fin.cases (fieldTerms f 0) (Fin.cases (fieldTerms f 1) (Fin.cases (fieldTerms f 2)
        (Fin.cases (fieldTerms f 3) (fun _ => timeTerm g)))) i)
        (Fin.cases j Fin.elim0)) = p.args n by rw [h]
  have env : (Fin.cases j Fin.elim0 : Fin 1 → Nat) = fun _ => j :=
    funext (Fin.cases rfl (fun i => i.elim0))
  rw [env]
  funext i
  obtain ⟨i,hi⟩ := i
  cases f <;> match i with
    | 0 | 1 | 2 | 3 | 4 => first | rfl | exact valRead _ _
    | k+5 => omega

theorem rotating_no_counterexample (f : Family) (u : Bool) (g : Grid) :
    Prf PRAAx [] (Fm.iff (rotating f u g) (RHCounterexamples.neg
      (RHCounterexamples.counter (rotating f u g)))) :=
  RHCounterexamples.no_counterexample (.binder (.matrix _))

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.OneSided
