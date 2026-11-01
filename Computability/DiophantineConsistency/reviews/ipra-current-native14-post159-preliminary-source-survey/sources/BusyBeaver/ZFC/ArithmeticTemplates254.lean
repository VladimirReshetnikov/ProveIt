import BusyBeaver.ZFC.ArithmeticCode254

/-! Fixed parameter-free bounded graphs for finite base4 constructor templates.
This module does not represent the gated twelve-row evaluator or histories. -/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCode254

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- Only the four literal tags used by the original numerical calculus. -/
inductive Tag where
  | imp | rel | all | eq

noncomputable def Tag.value : Tag → V
  | .imp => 0 | .rel => 1 | .all => 2 | .eq => 3

/-- Four inputs suffice for all eight logical rows and the full bundle. -/
inductive Circuit where
  | input0 | input1 | input2 | input3 | one
  | node (tag : Tag) (left right : Circuit)

noncomputable def Circuit.eval : Circuit → V → V → V → V → V
  | .input0, a, _, _, _ => a
  | .input1, _, b, _, _ => b
  | .input2, _, _, c, _ => c
  | .input3, _, _, _, u => u
  | .one, _, _, _, _ => 1
  | .node k x y, a, b, c, u => tagged k.value (x.eval a b c u) (y.eval a b c u)

/-- Compilation produces a literal ring-language Sigma0 sentence. Both child
outputs are bounded by their parent output; no semantic model parameters occur. -/
def Circuit.graph : Circuit → 𝚺₀.Semisentence 5
  | .input0 => .mkSigma “r a b c u. r = a”
  | .input1 => .mkSigma “r a b c u. r = b”
  | .input2 => .mkSigma “r a b c u. r = c”
  | .input3 => .mkSigma “r a b c u. r = u”
  | .one => .mkSigma “r a b c u. r = 1”
  | .node .imp x y => .mkSigma
      “r a b c u. ∃ s <⁺ r, ∃ t <⁺ r,
        !(graph x) s a b c u ∧ !(graph y) t a b c u ∧ !taggedDef r 0 s t”
  | .node .rel x y => .mkSigma
      “r a b c u. ∃ s <⁺ r, ∃ t <⁺ r,
        !(graph x) s a b c u ∧ !(graph y) t a b c u ∧ !taggedDef r 1 s t”
  | .node .all x y => .mkSigma
      “r a b c u. ∃ s <⁺ r, ∃ t <⁺ r,
        !(graph x) s a b c u ∧ !(graph y) t a b c u ∧ !taggedDef r 2 s t”
  | .node .eq x y => .mkSigma
      “r a b c u. ∃ s <⁺ r, ∃ t <⁺ r,
        !(graph x) s a b c u ∧ !(graph y) t a b c u ∧ !taggedDef r 3 s t”

lemma bounded_tagged_iff (k a b r : V) :
    (a ≤ r ∧ b ≤ r ∧ r = tagged k a b) ↔ r = tagged k a b := by
  constructor
  · exact fun h => h.2.2
  · intro h
    rw [h]
    exact ⟨(tagged_components k a b).1, (tagged_components k a b).2, rfl⟩

instance Circuit.defined (e : Circuit) :
    𝚺₀-Function₄[V] e.eval via e.graph := by
  induction e with
  | input0 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | input1 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | input2 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | input3 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | one => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | node k x y ihx ihy =>
    cases k <;> refine .mk fun v => ?_ <;>
      simp [Circuit.graph, Circuit.eval, Tag.value, ihx.iff, ihy.iff, bounded_tagged_iff]


namespace Circuit

def im := node Tag.imp
def el := node Tag.rel
def al := node Tag.all
def eq := node Tag.eq
/-- Relative falsity remains the live code1, not a new syntactic Bottom. -/
def neg (x : Circuit) := im x one
def conj (x y : Circuit) := neg (im x (neg y))
def ex (x y : Circuit) := neg (al x (neg y))

@[simp] theorem eval_im (x y : Circuit) (a b c u : V) :
    (im x y).eval a b c u = wim (x.eval a b c u) (y.eval a b c u) := rfl
@[simp] theorem eval_el (x y : Circuit) (a b c u : V) :
    (el x y).eval a b c u = wel (x.eval a b c u) (y.eval a b c u) := rfl
@[simp] theorem eval_al (x y : Circuit) (a b c u : V) :
    (al x y).eval a b c u = wal (x.eval a b c u) (y.eval a b c u) := rfl
@[simp] theorem eval_eq (x y : Circuit) (a b c u : V) :
    (eq x y).eval a b c u = weq (x.eval a b c u) (y.eval a b c u) := rfl
@[simp] theorem eval_input0 (a b c u : V) : input0.eval a b c u = a := rfl
@[simp] theorem eval_input1 (a b c u : V) : input1.eval a b c u = b := rfl
@[simp] theorem eval_input2 (a b c u : V) : input2.eval a b c u = c := rfl
@[simp] theorem eval_input3 (a b c u : V) : input3.eval a b c u = u := rfl
@[simp] theorem eval_one (a b c u : V) : one.eval a b c u = 1 := rfl

def r8 (a b c u : Circuit) := im (im (im c u) a) (im (im a c) (im b c))
def r7 (a b c : Circuit) := im (eq c a) (im (eq c b) (eq a b))
def r6 (a b : Circuit) := im (ex a (al a b)) b
def r5 (a b c : Circuit) := im (eq c a) (im (el c b) (el a b))
def r4 (a b c : Circuit) := im (al a (al b c)) (al b (al a c))
def r3 (a b c : Circuit) := im (eq a b) (im (el c a) (el c b))
def r2 (a b c : Circuit) := im (al a (im b c)) (im (al a b) (al a c))

def container (a b c : Circuit) :=
  ex b (conj (al a (im (el a b)
                          (conj (ex c (conj (al b (im (al c (im (el c b) (el c a))) (el b c)))
                                         (el c b)))
                              (al c (im (el c a) (el c b))))))
            (el c b))
def collection (a b c : Circuit) :=
  ex c (conj (al a (im (el a b) (al b (im c (ex b (conj c (el b c)))))))
            (al b (im (el b c) (ex a c))))
def bundle (a b c : Circuit) :=
  conj (conj (container a b c) (collection a b c))
     (conj (im (el a b) (al c (el a b))) (im (eq a b) (al c (eq a b))))

end Circuit

def rho2Circuit : Circuit := Circuit.r2 Circuit.input0 Circuit.input1 Circuit.input2
noncomputable def rho2 (a b c : V) : V := rho2Circuit.eval a b c 0
def rho2Def : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(rho2Circuit.graph) r a b c 0”
instance rho2_defined : 𝚺₀-Function₃[V] rho2 via rho2Def := .mk fun v => by
  simp [rho2Def, rho2]
@[simp] theorem rho2_nat (a b c : Nat) : rho2 a b c = Code254.rho2 a b c := by
  simp [rho2, rho2Circuit, Circuit.r2, Code254.rho2]

def rho3Circuit : Circuit := Circuit.r3 Circuit.input0 Circuit.input1 Circuit.input2
noncomputable def rho3 (a b c : V) : V := rho3Circuit.eval a b c 0
def rho3Def : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(rho3Circuit.graph) r a b c 0”
instance rho3_defined : 𝚺₀-Function₃[V] rho3 via rho3Def := .mk fun v => by
  simp [rho3Def, rho3]
@[simp] theorem rho3_nat (a b c : Nat) : rho3 a b c = Code254.rho3 a b c := by
  simp [rho3, rho3Circuit, Circuit.r3, Code254.rho3]

def rho4Circuit : Circuit := Circuit.r4 Circuit.input0 Circuit.input1 Circuit.input2
noncomputable def rho4 (a b c : V) : V := rho4Circuit.eval a b c 0
def rho4Def : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(rho4Circuit.graph) r a b c 0”
instance rho4_defined : 𝚺₀-Function₃[V] rho4 via rho4Def := .mk fun v => by
  simp [rho4Def, rho4]
@[simp] theorem rho4_nat (a b c : Nat) : rho4 a b c = Code254.rho4 a b c := by
  simp [rho4, rho4Circuit, Circuit.r4, Code254.rho4]

def rho5Circuit : Circuit := Circuit.r5 Circuit.input0 Circuit.input1 Circuit.input2
noncomputable def rho5 (a b c : V) : V := rho5Circuit.eval a b c 0
def rho5Def : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(rho5Circuit.graph) r a b c 0”
instance rho5_defined : 𝚺₀-Function₃[V] rho5 via rho5Def := .mk fun v => by
  simp [rho5Def, rho5]
@[simp] theorem rho5_nat (a b c : Nat) : rho5 a b c = Code254.rho5 a b c := by
  simp [rho5, rho5Circuit, Circuit.r5, Code254.rho5]

def rho6Circuit : Circuit := Circuit.r6 Circuit.input0 Circuit.input1
noncomputable def rho6 (a b : V) : V := rho6Circuit.eval a b 0 0
def rho6Def : 𝚺₀.Semisentence 3 := .mkSigma
  “r a b. !(rho6Circuit.graph) r a b 0 0”
instance rho6_defined : 𝚺₀-Function₂[V] rho6 via rho6Def := .mk fun v => by
  simp [rho6Def, rho6]
@[simp] theorem rho6_nat (a b : Nat) : rho6 a b = Code254.rho6 a b := by
  simp [rho6, rho6Circuit, Circuit.r6, Circuit.ex, Circuit.neg,
    Code254.rho6, Code254.wex, Code254.wn, Code254.F]

def rho7Circuit : Circuit := Circuit.r7 Circuit.input0 Circuit.input1 Circuit.input2
noncomputable def rho7 (a b c : V) : V := rho7Circuit.eval a b c 0
def rho7Def : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(rho7Circuit.graph) r a b c 0”
instance rho7_defined : 𝚺₀-Function₃[V] rho7 via rho7Def := .mk fun v => by
  simp [rho7Def, rho7]
@[simp] theorem rho7_nat (a b c : Nat) : rho7 a b c = Code254.rho7 a b c := by
  simp [rho7, rho7Circuit, Circuit.r7, Code254.rho7]

def rho8Circuit : Circuit := Circuit.r8 Circuit.input0 Circuit.input1 Circuit.input2 Circuit.input3
noncomputable def rho8 (a b c u : V) : V := rho8Circuit.eval a b c u
def rho8Def : 𝚺₀.Semisentence 5 := .mkSigma
  “r a b c u. !(rho8Circuit.graph) r a b c u”
instance rho8_defined : 𝚺₀-Function₄[V] rho8 via rho8Def := .mk fun v => by
  simp [rho8Def, rho8]
@[simp] theorem rho8_nat (a b c u : Nat) : rho8 a b c u = Code254.rho8 a b c u := by
  simp [rho8, rho8Circuit, Circuit.r8, Code254.rho8]

def bundleCCircuit : Circuit := Circuit.container Circuit.input0 Circuit.input1 Circuit.input2
noncomputable def bundleC (a b c : V) : V := bundleCCircuit.eval a b c 0
def bundleCDef : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(bundleCCircuit.graph) r a b c 0”
instance bundleC_defined : 𝚺₀-Function₃[V] bundleC via bundleCDef := .mk fun v => by
  simp [bundleCDef, bundleC]
@[simp] theorem bundleC_nat (a b c : Nat) : bundleC a b c = Code254.bundleC a b c := by
  simp [bundleC, bundleCCircuit, Circuit.container, Circuit.ex, Circuit.neg,
    Circuit.conj, Code254.bundleC, Code254.wex, Code254.wn, Code254.wa, Code254.F]

def bundleGCircuit : Circuit := Circuit.collection Circuit.input0 Circuit.input1 Circuit.input2
noncomputable def bundleG (a b c : V) : V := bundleGCircuit.eval a b c 0
def bundleGDef : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(bundleGCircuit.graph) r a b c 0”
instance bundleG_defined : 𝚺₀-Function₃[V] bundleG via bundleGDef := .mk fun v => by
  simp [bundleGDef, bundleG]
@[simp] theorem bundleG_nat (a b c : Nat) : bundleG a b c = Code254.bundleG a b c := by
  simp [bundleG, bundleGCircuit, Circuit.collection, Circuit.ex, Circuit.neg,
    Circuit.conj, Code254.bundleG, Code254.wex, Code254.wn, Code254.wa, Code254.F]

def bundleCircuit : Circuit := Circuit.bundle Circuit.input0 Circuit.input1 Circuit.input2
noncomputable def bundle (a b c : V) : V := bundleCircuit.eval a b c 0
def bundleDef : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(bundleCircuit.graph) r a b c 0”
instance bundle_defined : 𝚺₀-Function₃[V] bundle via bundleDef := .mk fun v => by
  simp [bundleDef, bundle]
@[simp] theorem bundle_nat (a b c : Nat) : bundle a b c = Code254.bundle a b c := by
  simp [bundle, bundleCircuit, Circuit.bundle, Circuit.container, Circuit.collection,
    Circuit.ex, Circuit.neg, Circuit.conj, Code254.bundle, Code254.bundleC,
    Code254.bundleG, Code254.wex, Code254.wn, Code254.wa, Code254.F]

/-! The fixed graph formulas also directly define the live standard-Nat functions.
The input indices and bundle gates are not changed or baked into these graphs. -/
instance codeRho2_defined :
    HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.rho2 rho2Def := by
  have he : (rho2 : Nat → Nat → Nat → Nat) = Code254.rho2 :=
    funext fun a => funext fun b => funext fun c => rho2_nat a b c
  rw [← he]; exact rho2_defined
instance codeRho3_defined :
    HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.rho3 rho3Def := by
  have he : (rho3 : Nat → Nat → Nat → Nat) = Code254.rho3 :=
    funext fun a => funext fun b => funext fun c => rho3_nat a b c
  rw [← he]; exact rho3_defined
instance codeRho4_defined :
    HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.rho4 rho4Def := by
  have he : (rho4 : Nat → Nat → Nat → Nat) = Code254.rho4 :=
    funext fun a => funext fun b => funext fun c => rho4_nat a b c
  rw [← he]; exact rho4_defined
instance codeRho5_defined :
    HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.rho5 rho5Def := by
  have he : (rho5 : Nat → Nat → Nat → Nat) = Code254.rho5 :=
    funext fun a => funext fun b => funext fun c => rho5_nat a b c
  rw [← he]; exact rho5_defined
instance codeRho6_defined :
    HierarchySymbol.DefinedFunction₂ (V := Nat) 𝚺₀ Code254.rho6 rho6Def := by
  have he : (rho6 : Nat → Nat → Nat) = Code254.rho6 :=
    funext fun a => funext fun b => rho6_nat a b
  rw [← he]; exact rho6_defined
instance codeRho7_defined :
    HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.rho7 rho7Def := by
  have he : (rho7 : Nat → Nat → Nat → Nat) = Code254.rho7 :=
    funext fun a => funext fun b => funext fun c => rho7_nat a b c
  rw [← he]; exact rho7_defined
instance codeRho8_defined :
    HierarchySymbol.DefinedFunction₄ (V := Nat) 𝚺₀ Code254.rho8 rho8Def := by
  have he : (rho8 : Nat → Nat → Nat → Nat → Nat) = Code254.rho8 :=
    funext fun a => funext fun b => funext fun c => funext fun u => rho8_nat a b c u
  rw [← he]; exact rho8_defined
instance codeBundleC_defined :
    HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.bundleC bundleCDef := by
  have he : (bundleC : Nat → Nat → Nat → Nat) = Code254.bundleC :=
    funext fun a => funext fun b => funext fun c => bundleC_nat a b c
  rw [← he]; exact bundleC_defined
instance codeBundleG_defined :
    HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.bundleG bundleGDef := by
  have he : (bundleG : Nat → Nat → Nat → Nat) = Code254.bundleG :=
    funext fun a => funext fun b => funext fun c => bundleG_nat a b c
  rw [← he]; exact bundleG_defined
instance codeBundle_defined :
    HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀ Code254.bundle bundleDef := by
  have he : (bundle : Nat → Nat → Nat → Nat) = Code254.bundle :=
    funext fun a => funext fun b => funext fun c => bundle_nat a b c
  rw [← he]; exact bundle_defined

end SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254
