import PA194SourceIntersection
import PA194FoundationND
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder
open ND (mem eq)


def zero (a : Term n) : Formula n :=
  ∀⁰ (∼mem (Rew.bShift a) (.bvar 0))

def successor (a b : Term n) : Formula n :=
  ∀⁰ sourceIff (mem (Rew.bShift b) (.bvar 0))
    (mem (Rew.bShift a) (.bvar 0) ⋎ eq (.bvar 0) (Rew.bShift a))

def subset (a b : Term n) : Formula n :=
  ∀⁰ (mem (Rew.bShift a) (.bvar 0) 🡒 mem (Rew.bShift b) (.bvar 0))

def transitive (a : Term n) : Formula n :=
  ∀⁰ ∀⁰ ((mem (Rew.bShift (Rew.bShift a)) (.bvar 1) ⋏
    mem (.bvar 1) (.bvar 0)) 🡒 mem (Rew.bShift (Rew.bShift a)) (.bvar 0))

def memberTransitive (a : Term n) : Formula n :=
  ∀⁰ (mem (Rew.bShift a) (.bvar 0) 🡒 transitive (.bvar 0))

def memberLinear (a : Term n) : Formula n :=
  ∀⁰ ∀⁰ ((mem (Rew.bShift (Rew.bShift a)) (.bvar 1) ⋏
    mem (Rew.bShift (Rew.bShift a)) (.bvar 0)) 🡒
    (eq (.bvar 1) (.bvar 0) ⋎
      (mem (.bvar 0) (.bvar 1) ⋎ mem (.bvar 1) (.bvar 0))))

def nonempty (a : Term n) : Formula n := ∃⁰ mem (Rew.bShift a) (.bvar 0)

def least (s m : Term n) : Formula n :=
  mem s m ⋏ (∀⁰ (mem (Rew.bShift s) (.bvar 0) 🡒
    (eq (Rew.bShift m) (.bvar 0) ⋎ mem (.bvar 0) (Rew.bShift m))))

def greatest (s m : Term n) : Formula n :=
  mem s m ⋏ (∀⁰ (mem (Rew.bShift s) (.bvar 0) 🡒
    (eq (.bvar 0) (Rew.bShift m) ⋎ mem (Rew.bShift m) (.bvar 0))))

def internalExtrema (a : Term n) : Formula n :=
  ∀⁰ ((subset (.bvar 0) (Rew.bShift a) ⋏ nonempty (.bvar 0)) 🡒
    ((∃⁰ least (.bvar 1) (.bvar 0)) ⋏ (∃⁰ greatest (.bvar 1) (.bvar 0))))

def representative (a : Term n) : Formula n :=
  transitive a ⋏ (memberTransitive a ⋏ (memberLinear a ⋏ internalExtrema a))

def memberIr (a : Term n) : Formula n :=
  ∀⁰ (mem (Rew.bShift a) (.bvar 0) 🡒 ∼mem (.bvar 0) (.bvar 0))

def domain (a : Term n) : Formula n := representative a ⋏ memberIr a

def inhabited : Formula 0 := ∃⁰ domain (.bvar 0)

end M6.PA.RelationalSource.Ordinal

