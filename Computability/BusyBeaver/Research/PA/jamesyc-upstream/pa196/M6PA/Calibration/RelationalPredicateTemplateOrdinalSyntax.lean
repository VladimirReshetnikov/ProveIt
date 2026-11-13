module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSyntax
@[expose] public section
/-! Literal five-clause ordinal syntax in the predicate-template language.
This only adds syntax; no induction proof or extensionality is assumed. -/
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder
open RelationalPredicateTemplate

def mem (a x : Term n) : Formula n := .rel .mem ![x,a]
def eq (x y : Term n) : Formula n := .rel .eq ![x,y]
def sourceIff (p q : Formula n) : Formula n := (p 🡒 q) ⋏ (q 🡒 p)

def zero (a : Term n) : Formula n :=
  ∀¹ (∼mem (Rew.bShift a) (.bvar 0))

def successor (a b : Term n) : Formula n :=
  ∀¹ sourceIff (mem (Rew.bShift b) (.bvar 0))
    (mem (Rew.bShift a) (.bvar 0) ⋎ eq (.bvar 0) (Rew.bShift a))

def subset (a b : Term n) : Formula n :=
  ∀¹ (mem (Rew.bShift a) (.bvar 0) 🡒 mem (Rew.bShift b) (.bvar 0))

def transitive (a : Term n) : Formula n :=
  ∀¹ ∀¹ ((mem (Rew.bShift (Rew.bShift a)) (.bvar 1) ⋏
    mem (.bvar 1) (.bvar 0)) 🡒 mem (Rew.bShift (Rew.bShift a)) (.bvar 0))

def memberTransitive (a : Term n) : Formula n :=
  ∀¹ (mem (Rew.bShift a) (.bvar 0) 🡒 transitive (.bvar 0))

def memberLinear (a : Term n) : Formula n :=
  ∀¹ ∀¹ ((mem (Rew.bShift (Rew.bShift a)) (.bvar 1) ⋏
    mem (Rew.bShift (Rew.bShift a)) (.bvar 0)) 🡒
    (eq (.bvar 1) (.bvar 0) ⋎
      (mem (.bvar 0) (.bvar 1) ⋎ mem (.bvar 1) (.bvar 0))))

def nonempty (a : Term n) : Formula n := ∃¹ mem (Rew.bShift a) (.bvar 0)

def least (s m : Term n) : Formula n :=
  mem s m ⋏ (∀¹ (mem (Rew.bShift s) (.bvar 0) 🡒
    (eq (Rew.bShift m) (.bvar 0) ⋎ mem (.bvar 0) (Rew.bShift m))))

def greatest (s m : Term n) : Formula n :=
  mem s m ⋏ (∀¹ (mem (Rew.bShift s) (.bvar 0) 🡒
    (eq (.bvar 0) (Rew.bShift m) ⋎ mem (Rew.bShift m) (.bvar 0))))

def internalExtrema (a : Term n) : Formula n :=
  ∀¹ ((subset (.bvar 0) (Rew.bShift a) ⋏ nonempty (.bvar 0)) 🡒
    ((∃¹ least (.bvar 1) (.bvar 0)) ⋏ (∃¹ greatest (.bvar 1) (.bvar 0))))

def representative (a : Term n) : Formula n :=
  transitive a ⋏ (memberTransitive a ⋏ (memberLinear a ⋏ internalExtrema a))

def memberIr (a : Term n) : Formula n :=
  ∀¹ (mem (Rew.bShift a) (.bvar 0) 🡒 ∼mem (.bvar 0) (.bvar 0))

def domain (a : Term n) : Formula n := representative a ⋏ memberIr a

def inhabited : Formula 0 := ∃¹ domain (.bvar 0)

end M6.PA.RelationalPredicateTemplate.Ordinal
