import DiophantineConsistency.PRAInductionCounterexample
/-! The open coded χ matrix for the four-witness, three-challenge interface. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStageCodedChi
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation PRAMultiplication
  PRAPrimitiveRecursionInduction PRAInductionCounterexample

private def params8 (n : ℕ) : Fin n → Semiterm language ℕ 8 := fun i => .fvar i.val
private def predTerm {n : ℕ} (pred : Code (n+3))
    (x y c : Semiterm language ℕ 8) : Semiterm language ℕ 8 :=
  .func pred (Fin.cases x (Fin.cases y (Fin.cases c (params8 n))))
private def zeroTerm : Semiterm language ℕ 8 := .func (Code.zero 0) Fin.elim0
private def oneTerm : Semiterm language ℕ 8 := .func oneCode Fin.elim0

/-- Bound slots are `[q,w,y,x,y₀,z,c,v]`. The final outer v is unused. -/
def chiMatrix {n : ℕ} (pred : Code (n+3)) : Semiproposition language 8 :=
  (Semiformula.rel Language.ORing.Rel.eq ![predTerm pred zeroTerm (.bvar 4) (.bvar 6), oneTerm]) ⋏
    ((Semiformula.rel Language.ORing.Rel.eq ![predTerm pred (.bvar 3) (.bvar 2) (.bvar 6), oneTerm]) 🡒
      (Semiformula.rel Language.ORing.Rel.eq
        ![predTerm pred (.func Code.succ ![.bvar 3]) (.bvar 0) (.bvar 6), oneTerm])) ⋏
    (Semiformula.nrel Language.ORing.Rel.eq ![predTerm pred (.bvar 5) (.bvar 1) (.bvar 6), oneTerm])

theorem chiMatrix_open {n : ℕ} (pred : Code (n+3)) : (chiMatrix pred).Open := by
  simp [chiMatrix, Semiformula.Open]

/-- Fix the c-argument of a ternary coded predicate using a PR parameter term. -/
def fixPredicate {n : ℕ} (pred : Code (n+3)) (c : Code n) : Code (n+2) :=
  .comp pred (.cons (.proj 0) (.cons (.proj 1) (.cons
    (.comp c (pack n (fun i => .proj i.succ.succ)))
    (pack n (fun i => .proj i.succ.succ)))))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelFixPredicate {n : ℕ} (pred : Code (n+3)) (c : Code n)
    (x y : M) (params : Fin n → M) :
    Structure.func (L := language) (fixPredicate pred c) (Fin.cases x (Fin.cases y params)) =
      Structure.func (L := language) pred (Fin.cases x (Fin.cases y
        (Fin.cases (Structure.func (L := language) c params) params))) := by
  rw [fixPredicate, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 _
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact modelProjection 1 _
    · refine Fin.cases ?_ (fun l => ?_) k
      · change Structure.func (L := language) (.comp c (pack n (fun i => .proj i.succ.succ)))
            (Fin.cases x (Fin.cases y params)) = Structure.func (L := language) c params
        rw [modelComposition]
        congr 1
        funext i
        simp only [getCode_pack]
        exact modelProjection i.succ.succ _
      · simp only [getCode, getCode_pack]
        exact modelProjection l.succ.succ _

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelChiMatrix {n : ℕ} (pred : Code (n+3)) (e : ℕ → M)
    (q w y x y₀ z c v : M) :
    (chiMatrix pred).Eval ![q,w,y,x,y₀,z,c,v] e ↔
      let ps := fun i : Fin n => e i.val
      let zero := Structure.func (L := language) (Code.zero 0) Fin.elim0
      let one := Structure.func (L := language) oneCode Fin.elim0
      let p := fun x y => Structure.func (L := language) pred (Fin.cases x (Fin.cases y (Fin.cases c ps))) = one
      p zero y₀ ∧ (p x y → p (Structure.func (L := language) Code.succ (fun _ => x)) q) ∧ ¬p z w := by
  have hp (u1 u2 u3 : Semiterm language ℕ 8) :
      (Semiterm.val ![q,w,y,x,y₀,z,c,v] e ∘ Fin.cases u1 (Fin.cases u2 (Fin.cases u3 (params8 n)))) =
        Fin.cases (Semiterm.val ![q,w,y,x,y₀,z,c,v] e u1)
          (Fin.cases (Semiterm.val ![q,w,y,x,y₀,z,c,v] e u2)
            (Fin.cases (Semiterm.val ![q,w,y,x,y₀,z,c,v] e u3) (fun i : Fin n => e i.val))) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) j) i
  have hz : (Semiterm.val (L := language) ![q,w,y,x,y₀,z,c,v] e ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hs : (Semiterm.val (L := language) ![q,w,y,x,y₀,z,c,v] e ∘ ![(.bvar 3 : Semiterm language ℕ 8)]) = (fun _ => x) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  classical
  simp [chiMatrix, Semiformula.imp_eq, Semiformula.eval_rel, Semiformula.eval_nrel,
    eqRel, predTerm, zeroTerm, oneTerm, Semiterm.val_func, hp, hz, hs]
  tauto

/-- Fixing c, y₀, z and a PR update q yields three values defeating
the concrete open χ matrix in every candidate-PRA model. -/
theorem modelChiDefeat {n : ℕ} (pred : Code (n+3)) (c base stop : Code n)
    (qCode : Code (n+3)) (e : ℕ → M) (v : M) :
    let params := fun i : Fin n => e i.val
    let cv := Structure.func (L := language) c params
    let y₀ := Structure.func (L := language) base params
    let z := Structure.func (L := language) stop params
    ∃ x y w, ¬(chiMatrix pred).Eval
      ![Structure.func (L := language) qCode (Fin.cases x (Fin.cases y (Fin.cases w params))),
        w,y,x,y₀,z,cv,v] e := by
  dsimp
  obtain ⟨x,y,w,h⟩ := modelCounterexampleDefeat (fixPredicate pred c) base stop qCode e
  refine ⟨x,y,w,?_⟩
  intro hh
  apply h
  have hv := (modelChiMatrix pred e
    (Structure.func (L := language) qCode (Fin.cases x (Fin.cases y (Fin.cases w (fun i : Fin n => e i.val)))))
    w y x (Structure.func (L := language) base (fun i : Fin n => e i.val))
    (Structure.func (L := language) stop (fun i : Fin n => e i.val))
    (Structure.func (L := language) c (fun i : Fin n => e i.val)) v).mp hh
  simpa only [modelFixPredicate] using hv

end models
end DiophantineConsistency.PRAStageCodedChi
