module
public import PA196.Arithmetic.Certificates.Logic
@[expose] public section

/-! Extraction of the new guarded gate and finite modal proof recipes.
Every construction returns a concrete code accepted by the new PA196 checker.
-/
open M6.PA
namespace PA196.Arithmetic.Certificates.Logic

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open Checker HeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable abbrev wel (a b : V) : V := wim a b + 1
noncomputable abbrev weq (a b : V) : V := wim a b + 3
noncomputable abbrev wex (a b : V) : V := wn (wal a (wn b))
noncomputable abbrev iffCode (a b : V) : V := wa (wim a b) (wim b a)
noncomputable def eqVac (a b c : V) : V := wim (weq a b) (wal c (weq a b))
noncomputable def memVac (a b c : V) : V := wim (wel a b) (wal c (wel a b))
noncomputable def point (_a b c : V) : V := wim c (wel c b)
noncomputable def separation (a b c : V) : V :=
  wal b (wa (wim (wel a b) (point a b c)) (wim (wel c b) c))
noncomputable def qGate (a b c : V) : V := wal c (wim (separation a b c) (wn (point a b c)))
noncomputable def oldGate (a b c : V) : V := wn (wim (memVac a b c) (qGate a b c))
noncomputable def bundle (a b c : V) : V := wn (wim (eqVac a b c) (wim (memVac a b c) (qGate a b c)))

noncomputable def gate (a b c : V) (ha : c ≠ a) (hb : c ≠ b) : Certificate (bundle a b c) :=
  ⟨leafCertificate 9 (pack3Value a b c),by
    simpa [bundle,eqVac,memVac,qGate,separation,point,wn,wim,wal,wel,weq,wa,
      implicationValue,universalValue,bundleExpr,eqVacExpr,memVacExpr,separationExpr,pointExpr,
      M6.PA.ActualArithmeticGraph.eval,im,al,eqn,mem,conj,neg,implicationExpr,universalExpr]
      using verify_bundle a b c ha hb⟩

noncomputable def r4 (d a h : V) : Certificate (wim (wal d (wal a h)) (wal a (wal d h))) :=
  ⟨leafCertificate 3 (pack3Value d a h),by
    simpa [wim,wal,implicationValue,universalValue,head2Expr,
      M6.PA.ActualArithmeticGraph.eval,im,al,implicationExpr,universalExpr]
      using verify_head2 d a h⟩

noncomputable def r1 (d h : V) : Certificate (wex d (weq h d)) :=
  ⟨leafCertificate 6 (pack2Value d h),by
    simpa [wex,weq,wn,wim,wal,implicationValue,universalValue,head5Expr,
      M6.PA.ActualArithmeticGraph.eval,im,al,eqn,ex,neg,implicationExpr,universalExpr]
      using verify_head5 d h⟩

noncomputable def memRight (a b c : V) : Certificate (wim (weq a b) (wim (wel c a) (wel c b))) :=
  ⟨leafCertificate 5 (pack3Value b c a),by
    simpa [weq,wel,wim,implicationValue,head4Expr,M6.PA.ActualArithmeticGraph.eval,
      im,eqn,mem,implicationExpr] using verify_head4 b c a⟩

noncomputable def memLeft (a b c : V) : Certificate (wim (weq a b) (wim (wel a c) (wel b c))) := by
  let raw : Certificate (wim (wel a c) (wim (weq a b) (wel b c))) :=
    ⟨leafCertificate 4 (pack3Value c b a),by
      simpa [weq,wel,wim,implicationValue,head3Expr,M6.PA.ActualArithmeticGraph.eval,
        im,eqn,mem,implicationExpr] using verify_head3 c b a⟩
  exact .mp raw (Dominated.exchange (wel a c) (weq a b) (wel b c))

noncomputable def Context.forallMP {Γ : List V} (x : V) {a b : V}
    (p : Context Γ (wal x a)) (q : Context Γ (wal x (wim a b))) : Context Γ (wal x b) :=
  .mp p (.mp q (.closed (r2 x a b)))

noncomputable def Context.generalize {Γ : List V} {a : V} (p : Context Γ a) (x : V)
    (vacuity : ∀ h, h ∈ Γ → Certificate (wim h (wal x h))) : Context Γ (wal x a) :=
  match p with
  | .assumption h => .mp (.assumption h) (.closed (vacuity _ h))
  | .closed d => .closed (.all x d)
  | .mp p q => (p.generalize x vacuity).forallMP x (q.generalize x vacuity)

theorem wel_bounds (a b : V) : a < wel a b ∧ b < wel a b :=
  ⟨lt_of_le_of_lt (Dominated.le_l b le_rfl) (lt_add_one _),
   lt_of_le_of_lt (Dominated.le_r a le_rfl) (lt_add_one _)⟩

theorem wn_strict (a : V) : a < wn a := by
  have hp := M6.PA.SourceCantorInternal.pairValue_bounds a 1
  have hpos : 0 < M6.PA.SourceCantorInternal.pairValue a 1 :=
    lt_of_lt_of_le (by norm_num : (0:V)<1) hp.2
  change a < 4 * M6.PA.SourceCantorInternal.pairValue a 1
  exact lt_of_le_of_lt hp.1 (Arithmetic.lt_mul_of_pos_of_one_lt_left hpos (by norm_num))


noncomputable def negImpLeft {a b : V} (g : Certificate (wn (wim a b))) : Certificate a := by
  let ha : Context [a,wn a] a := .assumption (by simp)
  let hn : Context [a,wn a] (wn a) := .assumption (by simp)
  let hi : Context [wn a] (wim a b) := ((Context.mp ha hn).explosion b).deduction
  exact (Context.mp hi (.closed g)).deduction.dne.empty

noncomputable def negImpRight {a b : V} (g : Certificate (wn (wim a b))) : Certificate (wn b) := by
  let hb : Context [b] b := .assumption (by simp)
  exact (Context.mp (hb.lift a) (.closed g)).deduction.empty

noncomputable def gateOld (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) : Certificate (oldGate a b c) :=
  negImpRight (gate a b c hca hcb)

noncomputable def equalityVacuity (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Certificate (wim (weq a b) (wal c (weq a b))) :=
  negImpLeft (gate a b c hca hcb)

noncomputable def membershipVacuity (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Certificate (wim (wel a b) (wal c (wel a b))) :=
  negImpLeft (gateOld a b c hca hcb)

noncomputable def pointedSeparation (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Certificate (wn (qGate a b c)) :=
  negImpRight (gateOld a b c hca hcb)

noncomputable def negationVacuity (x a : V) (hv : Certificate (wim a (wal x a))) :
    Certificate (wim (wn a) (wal x (wn a))) := by
  let hc := contrapose hv
  let hg := Certificate.all x hc
  let hl := Certificate.mp hg (r2 x (wn (wal x a)) (wn a))
  let hr := contrapose (r6 x a)
  let hf := implicationCompose hr (doubleNegationElimination (wal x (wn (wal x a))))
  exact implicationCompose hf hl

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
  let hn : Context [a,wn a] (wn a) := .assumption (by simp)
  let hp : Context [a,wn a] a := .assumption (by simp)
  let hnot : Certificate (wim (wn a) (wim a b)) :=
    ((Context.mp hp hn).explosion b).deduction.deduction.empty
  let haLift : Certificate (wim (wn a) c) := implicationCompose (negationVacuity x a ha)
    (.mp (.all x hnot) (r2 x (wn a) (wim a b)))
  let pa : Context [a,wim a b] a := .assumption (by simp)
  let pab : Context [a,wim a b] (wim a b) := .assumption (by simp)
  let pc : Context [a,wim a b] c := .mp (.mp pa pab) (.closed hbLift)
  let pna : Context [wn a,wim a b] (wn a) := .assumption (by simp)
  let pnc : Context [wn a,wim a b] c := .mp pna (.closed haLift)
  exact (Context.casesOnFormula a pc pnc).deduction.empty

noncomputable def universalVacuity (x y a : V) (h : Certificate (wim a (wal x a))) :
    Certificate (wim (wal y a) (wal x (wal y a))) :=
  implicationCompose (.mp (.all y h) (r2 y a (wal x a))) (r4 y x a)

noncomputable def conjunctionVacuity (x a b : V)
    (ha : Certificate (wim a (wal x a))) (hb : Certificate (wim b (wal x b))) :
    Certificate (wim (wa a b) (wal x (wa a b))) :=
  negationVacuity x (wim a (wn b))
    (implicationVacuity x a (wn b) ha (negationVacuity x b hb))

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

noncomputable def liftImp (x : V) {a b : V} (p : Certificate (wim a b)) :
    Certificate (wim (wal x a) (wal x b)) := .mp (.all x p) (r2 x a b)

noncomputable def Context.arrowCompose {Γ : List V} {a b c : V}
    (p : Context Γ (wim a b)) (q : Context Γ (wim b c)) : Context Γ (wim a c) :=
  .mp q (.mp p (.closed (Dominated.composition a b c)))

#print axioms gateOld
#print axioms equalityVacuity
#print axioms membershipVacuity
#print axioms pointedSeparation
#print axioms Context.existsElim
end PA196.Arithmetic.Certificates.Logic
