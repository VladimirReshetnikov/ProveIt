import Surreal.Algebra.RingTermCodeComputability

/-!
# Primitive-recursive structural folds on native ring terms

The term-analysis prerequisite of `odg:def:thm:saturation`. A prefix-stack
implementation realizes a native structural fold whenever its variable and
operation handlers are primitive recursive.
-/

namespace Surreal.RingTermFold
open FirstOrder FirstOrder.Language
open RingTermCode

variable {A : Type*}

/-- Structural recursion on a native ring term with supplied node handlers. -/
def fold (v : ℕ → A) (z o : A) (neg : A → A) (add mul : A → A → A) :
    Language.ring.Term ℕ → A
  | .var n => v n
  | .func .zero _ => z
  | .func .one _ => o
  | .func .neg ts => neg (fold v z o neg add mul (ts 0))
  | .func .add ts => add (fold v z o neg add mul (ts 0)) (fold v z o neg add mul (ts 1))
  | .func .mul ts => mul (fold v z o neg add mul (ts 0)) (fold v z o neg add mul (ts 1))

/-- A total stack step; the default is never used while scanning an encoded term. -/
def step (d : A) (v : ℕ → A) (z o : A) (neg : A → A) (add mul : A → A → A) :
    Token → List A → List A
  | .inl n, s => v n :: s
  | .inr 0, s => z :: s
  | .inr 1, s => o :: s
  | .inr 2, s => neg (s.getD 0 d) :: s.tail
  | .inr 3, s => add (s.getD 0 d) (s.getD 1 d) :: s.drop 2
  | .inr 4, s => mul (s.getD 0 d) (s.getD 1 d) :: s.drop 2

/-- Scan a prefix stream into the stack of fold results. -/
def scan (d : A) (v : ℕ → A) (z o : A) (neg : A → A) (add mul : A → A → A)
    (l : List Token) (s : List A) : List A := l.foldr (step d v z o neg add mul) s

/-- The stack algorithm computes the native fold without consuming the initial stack. -/
theorem scan_encode (d : A) (v : ℕ → A) (z o : A) (neg : A → A) (add mul : A → A → A)
    (t : Language.ring.Term ℕ) (s : List A) :
    scan d v z o neg add mul (encode t) s = fold v z o neg add mul t :: s := by
  induction t generalizing s with
  | var n => rfl
  | func f ts ih =>
    have ha (l r : List Token) (s : List A) :
        scan d v z o neg add mul (l ++ r) s =
          scan d v z o neg add mul l (scan d v z o neg add mul r s) := List.foldr_append
    have hc (a : Token) (l : List Token) (s : List A) :
        scan d v z o neg add mul (a :: l) s =
          step d v z o neg add mul a (scan d v z o neg add mul l s) := rfl
    have hz (s : List A) : scan d v z o neg add mul [] s = s := rfl
    cases f <;> simp [encode, fold, hc, ha, ih, step, hz]

section Computability
variable [Primcodable A]
local instance : Primcodable (Language.ring.Term ℕ) := RingTermCode.termPrimcodable

/-- The total stack step is primitive recursive when its node handlers are. -/
theorem step_primrec (d : A) (v : ℕ → A) (z o : A) (neg : A → A) (add mul : A → A → A)
    (hv : Primrec v) (hn : Primrec neg) (ha : Primrec₂ add) (hm : Primrec₂ mul) :
    Primrec₂ (step d v z o neg add mul) := by
  have hf : Primrec₂ (fun (i : Fin 5) (s : List A) =>
      if i.val = 0 then z :: s else if i.val = 1 then o :: s else if i.val = 2 then
        neg (s.getD 0 d) :: s.tail else if i.val = 3 then
        add (s.getD 0 d) (s.getD 1 d) :: s.drop 2 else
        mul (s.getD 0 d) (s.getD 1 d) :: s.drop 2) := by
    have h0 : Primrec (fun p : Fin 5 × List A => p.2.getD 0 d) :=
      (Primrec.list_getD d).comp Primrec.snd (Primrec.const 0)
    have h1 : Primrec (fun p : Fin 5 × List A => p.2.getD 1 d) :=
      (Primrec.list_getD d).comp Primrec.snd (Primrec.const 1)
    exact (Primrec.ite (Primrec.eq.comp (Primrec.fin_val.comp Primrec.fst) (Primrec.const 0))
      (Primrec.list_cons.comp (Primrec.const z) Primrec.snd)
      (Primrec.ite (Primrec.eq.comp (Primrec.fin_val.comp Primrec.fst) (Primrec.const 1))
        (Primrec.list_cons.comp (Primrec.const o) Primrec.snd)
        (Primrec.ite (Primrec.eq.comp (Primrec.fin_val.comp Primrec.fst) (Primrec.const 2))
          (Primrec.list_cons.comp (hn.comp h0) (Primrec.list_tail.comp Primrec.snd))
          (Primrec.ite (Primrec.eq.comp (Primrec.fin_val.comp Primrec.fst) (Primrec.const 3))
            (Primrec.list_cons.comp (ha.comp h0 h1) (Primrec.list_drop.comp (Primrec.const 2) Primrec.snd))
            (Primrec.list_cons.comp (hm.comp h0 h1)
              (Primrec.list_drop.comp (Primrec.const 2) Primrec.snd)))))).to₂
  have h : Primrec (fun p : Token × List A =>
      (Sum.casesOn p.1 (fun n => v n :: p.2)
        (fun i => if i.val = 0 then z :: p.2 else if i.val = 1 then o :: p.2 else if i.val = 2 then
          neg (p.2.getD 0 d) :: p.2.tail else if i.val = 3 then
          add (p.2.getD 0 d) (p.2.getD 1 d) :: p.2.drop 2 else
          mul (p.2.getD 0 d) (p.2.getD 1 d) :: p.2.drop 2) : List A)) :=
    Primrec.sumCasesOn Primrec.fst
      (Primrec.list_cons.comp (hv.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).to₂
      (hf.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
  exact h.to₂.of_eq (fun t s => by rcases t with n | i; rfl; fin_cases i <;> rfl)

/-- Scanning term codes is primitive recursive under the same handler hypotheses. -/
theorem scan_primrec (d : A) (v : ℕ → A) (z o : A) (neg : A → A) (add mul : A → A → A)
    (hv : Primrec v) (hn : Primrec neg) (ha : Primrec₂ add) (hm : Primrec₂ mul) :
    Primrec₂ (scan d v z o neg add mul) :=
  (Primrec.list_foldr Primrec.fst Primrec.snd
    ((step_primrec d v z o neg add mul hv hn ha hm).comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).to₂

/-- Structural folds on native ring terms preserve primitive recursiveness. -/
theorem fold_primrec (d : A) (v : ℕ → A) (z o : A) (neg : A → A) (add mul : A → A → A)
    (hv : Primrec v) (hn : Primrec neg) (ha : Primrec₂ add) (hm : Primrec₂ mul) :
    Primrec (fold v z o neg add mul) := by
  have h := (Primrec.list_getD d).comp
    ((scan_primrec d v z o neg add mul hv hn ha hm).comp encode_primrec (Primrec.const []))
    (Primrec.const 0)
  exact h.of_eq (fun t => by simp [scan_encode])

end Computability
end Surreal.RingTermFold
