import DiscreteForms

/-! Closed formulas for every finite numerical test in DiscreteForms. -/
namespace RiemannIPRA.Discrete
open LeanProofs.ConciseIPRA PacketLanguage

private def vec8 {α : Type} (a b c d s k x w : α) : Fin 8 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d
    (Fin.cases s (Fin.cases k (Fin.cases x (fun _ => w)))))))

private theorem env8 {α : Type} (e : Fin 8 → α) :
    e = vec8 (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) := by
  funext ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | n+8 => omega

private def Data.work (p : Data) (s k b w : Nat) : Fin 8 → Nat :=
  vec8 p.degreeOffset p.height p.pos p.neg s k b w

private abbrev workCtx := ["d","H","u","v","s","k","b","w"]
private abbrev baseCtx := ["d","H","u","v","t"]
private abbrev auxCtx := ["j","acc","d","H","u","v","n","q"]

/-- Read a code whose fifth argument is a zero-based cutoff. -/
private def at5 {ctx : List String} (f : PR 5) (d H u v n : E ctx) :=
  call f [d,H,u,v,n]

private def workAt (f : PR 5) (t : E workCtx) :=
  at5 f (v "d") (v "H") (v "u") (v "v") t

private def rawCost {ctx : List String} (d H n : E ctx) :=
  n * powE (call allowance [d+1,H,n]) 2

private def rawLog (n : E workCtx) :=
  call logProduct [v "d"+1,v "H",v "u",v "v",n]

private def sides {ctx : List String} (a b r : E ctx) :=
  (a-(b+r))+(b-(a+r))

private def weights (f : PR 5) : PR 8 := program workCtx <|
  sumTo "i" (v "k") (digitE (v "w") (v "b") (v "i") *
    at5 f (v "d") (v "H") (v "u") (v "v") (v "s"+v "i"))

private def plain (f : PR 5) : PR 5 := program baseCtx <|
  sumTo "i" (v "t") (at5 f (v "d") (v "H") (v "u") (v "v") (v "i"))

private def chainAux : PR 7 := .prec zeroR (program auxCtx <|
  2 * v "acc" + (v "q"*v "q" + rawCost (v "d") (v "H") (powE 2 (v "j") * v "n")))

private def thisWork (f : PR 8) : E workCtx :=
  call f [v "d",v "H",v "u",v "v",v "s",v "k",v "b",v "w"]

/-- Four extra universally quantified variables suffice for every comparison.
The variables unused by a particular matrix are harmless. -/
def Form.matrix : Form → PR 8
  | .localTest => program workCtx (workAt excess (v "s"))
  | .radixPrefix => program workCtx (workAt packedMatrix (v "s"))
  | .linearProbe => program workCtx <|
    let n := v "s"+100
    let q := v "b"
    sides (2*q*rawLog (2*n)) (2*(2*q*rawLog n)) (q*q + rawCost (v "d") (v "H") n)
  | .dyadicChain => program workCtx <|
    let n := v "s"+100
    let q := v "b"
    let z := powE 2 (v "k")
    sides (2*q*rawLog (z*n)) (z*(2*q*rawLog n))
      (call chainAux [v "k",v "d",v "H",v "u",v "v",n,q])
  | .weightedWindow => program workCtx (thisWork (weights energyCode) - thisWork (weights budgetCode))
  | .prefixIncrement => program workCtx <|
    (workAt (plain energyCode) (v "s"+v "k") + workAt (plain budgetCode) (v "s")) -
      (workAt (plain budgetCode) (v "s"+v "k") + workAt (plain energyCode) (v "s"))

private def atom8 {n} (f : PR 8) (d H u v s k b w : PTm n) : Fm PTm n :=
  .eq (.app f (vec8 d H u v s k b w)) PTm.zero

def Family.close8 (s : Family) (m : PR 8) : Fm PTm 0 := match s with
  | .riemann => .all (.all (.all (.all (atom8 m PTm.zero PTm.zero PTm.zero (PTm.succ PTm.zero)
    (Syn.var 3) (Syn.var 2) (Syn.var 1) (Syn.var 0)))))
  | .dirichlet => .all (.all (.all (.all (.all (atom8 m (Syn.var 4) PTm.zero PTm.zero
    (PTm.succ PTm.zero) (Syn.var 3) (Syn.var 2) (Syn.var 1) (Syn.var 0))))))
  | .dedekind => .all (.all (.all (.all (.all (.all (.all (.all
    (atom8 m (Syn.var 7) (Syn.var 6) (Syn.var 5) (Syn.var 4)
      (Syn.var 3) (Syn.var 2) (Syn.var 1) (Syn.var 0)))))))))

/-- The eighteen closed sentences indexed by analytic family and finite test. -/
def statement (s : Family) (k : Form) : Fm PTm 0 := s.close8 k.matrix

private theorem atom8_ok {n} (f : PR 8) (d H u v s k b w : PTm n) (e : Fin n → Nat) :
    naturalTerms.Holds (atom8 f d H u v s k b w) e ↔ value f (vec8
      (termValue d e) (termValue H e) (termValue u e) (termValue v e)
      (termValue s e) (termValue k e) (termValue b e) (termValue w e)) = 0 := by
  change value f _ = 0 ↔ _
  rw [env8 (fun i => termValue (vec8 d H u v s k b w i) e)]
  rfl

private theorem holds8 (s : Family) (f : PR 8) : naturalTerms.Holds (s.close8 f) Fin.elim0 ↔
    s.allData (fun p => ∀ i k b w, value f (p.work i k b w) = 0) := by
  cases s <;> simp only [Family.close8, Family.allData, all_ok, atom8_ok] <;> rfl

private theorem addMonus (a b r : Nat) :
    (a-(b+r))+(b-(a+r)) = 0 ↔ TwoSided a b r := by unfold TwoSided; omega

private theorem denSides {ctx} (a b r : E ctx) (e) : denote (sides a b r) e = 0 ↔
    TwoSided (denote a e) (denote b e) (denote r e) := by
  simp only [sides, plus, minus, addMonus]

private theorem denCost {ctx} (d H n : E ctx) (e) : denote (rawCost d H n) e =
    denote n e * (value allowance (args3 (denote d e+1) (denote H e) (denote n e)))^2 := by
  simp only [rawCost, times, power, apply3, plus]; rfl

private theorem denLog (n : E workCtx) (p : Data) (s k b w : Nat) :
    denote (rawLog n) (p.work s k b w) = p.logP (denote n (p.work s k b w)) := by
  simp only [rawLog, apply5, plus]; rfl

private theorem overTotal (f : Nat → Nat) (k : Nat) :
    overRange 0 (fun i a => a+f i) k = total f k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (·+f k) ih

private theorem denPower {ctx} (a b : E ctx) (e) : denote (a^b) e = denote a e ^ denote b e := power a b e

private theorem weight_ok (f : PR 5) (p : Data) (s k b w : Nat) :
    value (weights f) (p.work s k b w) = total (fun j => weightDigit b w j * value f (p.args (s+j))) k := by
  unfold weights; rw [value_program]
  change overRange 0 (fun j a => a + @denote ("i"::workCtx) _ (Fin.cases j (p.work s k b w))) k = _
  simp only [times, digitE, denote_modE, denote_divE, denPower, at5, apply5, plus]
  exact overTotal _ _

private theorem plain_ok (f : PR 5) (p : Data) (s : Nat) :
    value (plain f) (p.args s) = total (fun j => value f (p.args j)) s := by
  unfold plain; rw [value_program]
  change overRange 0 (fun j a => a + @denote ("i"::baseCtx) _ (Fin.cases j (p.args s))) s = _
  simp only [at5, apply5]
  exact overTotal _ _

private def auxArgs (p : Data) (k n q : Nat) : Fin 7 → Nat :=
  Fin.cases k (Fin.cases p.degreeOffset (Fin.cases p.height (Fin.cases p.pos
    (Fin.cases p.neg (Fin.cases n (fun _ => q))))))

private theorem aux_ok (p : Data) (n q k : Nat) :
    value chainAux (auxArgs p k n q) = p.chainBudget n q k := by
  unfold chainAux
  rw [value]
  simp only [value_zeroR, value_program, plus, times, denCost, power]
  induction k with
  | zero => rfl
  | succ k ih =>
    change 2 * Nat.rec (motive := fun _ => Nat) 0 (fun j a => 2*a+(q*q+p.cost (2^j*n))) k + (q*q + p.cost (2^k*n)) = 2*p.chainBudget n q k + _
    rw [← doubleAt_eq n k]
    exact congrArg (fun a => 2*a + (q*q+p.cost (doubleAt n k))) ih


private def Form.check : Form → Data → Nat → Nat → Nat → Nat → Prop
  | .localTest, p,s,_,_,_ => p.test s
  | .radixPrefix, p,s,_,_,_ =>
      total (fun i => radix p.budget i * p.energy i) s ≤ total (fun i => radix p.budget i * p.budget i) s
  | .linearProbe, p,s,_,q,_ => TwoSided (2*q*p.logP (2*(s+100))) (2*(2*q*p.logP (s+100)))
      (q*q+p.cost (s+100))
  | .dyadicChain, p,s,k,q,_ => TwoSided (2*q*p.logP (doubleAt (s+100) k))
      (doubleAt (2*q*p.logP (s+100)) k) (p.chainBudget (s+100) q k)
  | .weightedWindow, p,s,k,b,w =>
      total (fun j => weightDigit b w j * p.energy (s+j)) k ≤ total (fun j => weightDigit b w j * p.budget (s+j)) k
  | .prefixIncrement, p,s,k,_,_ =>
      total p.energy (s+k) + total p.budget s ≤ total p.budget (s+k) + total p.energy s

private theorem atWork (f : PR 5) (x : E workCtx) (p : Data) (s k b w : Nat) :
    denote (workAt f x) (p.work s k b w) = value f (p.args (denote x (p.work s k b w))) := by
  simp only [workAt, at5, apply5]; rfl

private theorem workEval (f : PR 8) (p : Data) (s k b w : Nat) :
    denote (thisWork f) (p.work s k b w) = value f (p.work s k b w) :=
  congrArg (value f) (env8 _)

private theorem env7 {α : Type} (e : Fin 7 → α) :
    e = Fin.cases (e 0) (Fin.cases (e 1) (Fin.cases (e 2) (Fin.cases (e 3)
      (Fin.cases (e 4) (Fin.cases (e 5) (fun _ => e 6)))))) := by
  funext ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rfl
  | n+7 => omega

private def vec7 (a b c d e f g : Nat) : Fin 7 → Nat :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (Fin.cases e (Fin.cases f (fun _ => g))))))

private theorem apply7 {ctx : List String} (f : PR 7) (a b c d u v w : E ctx) (e) :
    denote (call f [a,b,c,d,u,v,w]) e = value f (vec7 (denote a e) (denote b e)
      (denote c e) (denote d e) (denote u e) (denote v e) (denote w e)) :=
  congrArg (value f) (env7 _)

private theorem chainCall (p : Data) (s k b w : Nat) :
    denote (call chainAux [v "k",v "d",v "H",v "u",v "v",v "s"+100,v "b"] : E workCtx)
      (p.work s k b w) = p.chainBudget (s+100) b k := by
  simp only [apply7, plus]
  exact aux_ok p (s+100) b k

private theorem mat_ok (m : Form) (p : Data) (s k b w : Nat) :
    value m.matrix (p.work s k b w) = 0 ↔ m.check p s k b w := by
  cases m with
  | localTest =>
    simp only [Form.matrix, value_program, atWork]
    exact read_test p s
  | radixPrefix =>
    simp only [Form.matrix, value_program, atWork]
    exact packedMatrix_ok p s
  | linearProbe =>
    simp only [Form.matrix, value_program, denSides, times, denLog, plus, denCost]
    rfl
  | dyadicChain =>
    simp only [Form.matrix, value_program, denSides, times, denLog, plus, power, chainCall,
      Form.check, doubleAt_eq]
    rfl
  | weightedWindow =>
    simp only [Form.matrix, value_program, minus, workEval, Nat.sub_eq_zero_iff_le, weight_ok, energy_ok, budget_ok]
    rfl
  | prefixIncrement =>
    simp only [Form.matrix, value_program, minus, plus, atWork, plain_ok, budget_ok, energy_ok,
      Nat.sub_eq_zero_iff_le]
    rfl

private theorem allChecks (m : Form) (p : Data) :
    (∀ s k b w : Nat, m.check p s k b w) ↔ m.meaning p := by
  cases m with
  | localTest => exact ⟨fun h s => h s 0 0 0, fun h s _ _ _ => h s⟩
  | radixPrefix => exact ⟨fun h s => h s 0 0 0, fun h s _ _ _ => h s⟩
  | linearProbe => exact ⟨fun h s b => h s 0 b 0, fun h s _ b _ => h s b⟩
  | dyadicChain => exact ⟨fun h s k b => h s k b 0, fun h s k b _ => h s k b⟩
  | weightedWindow => rfl
  | prefixIncrement => exact ⟨fun h s k => h s k 0 0, fun h s k _ _ => h s k⟩

/-- Denotational correctness for every new object sentence. -/
theorem statement_reading (s : Family) (m : Form) :
    naturalTerms.Holds (statement s m) Fin.elim0 ↔ s.allData m.meaning := by
  apply (holds8 s m.matrix).trans
  apply s.lift_iff
  intro p
  exact (forall_congr' (fun i => forall_congr' (fun k => forall_congr'
    (fun b => forall_congr' (fun w => mat_ok m p i k b w))))).trans (allChecks m p)

/-- Equality of truth values in the standard interpretation of the original
formula and every explicitly coded test. -/
theorem statement_equivalent (s : Family) (m : Form) :
    naturalTerms.Holds (s.close excess) Fin.elim0 ↔ naturalTerms.Holds (statement s m) Fin.elim0 :=
  (hypothesis_iff s m).trans (statement_reading s m).symm

end RiemannIPRA.Discrete
