module
public import M6.Source.Cantor
@[expose] public section

/-! Pure arithmetic specification for the exact PA135 AX output. These are
numeric constructors, not a second proof calculus or an assumed AX theorem.
The existing metamathematics calculus is connected separately by equalities. -/
namespace M6.Source.AXCode
open Cantor

def wim := implication
def wal := universal
def wel (a b : Nat) := 4 * pair a b + 1
def weq (a b : Nat) := 4 * pair a b + 3
def wn (a : Nat) := wim a 1
def wa (a b : Nat) := wn (wim a (wn b))
def wex (a b : Nat) := wn (wal a (wn b))

def rho1 a b := wex a (weq a b)
def rho2 a b c := wim (wal a (wim b c)) (wim (wal a b) (wal a c))
def rho3 a b c := wim (wel a b) (wim (weq b c) (wel a c))
def rho4 a b c := wim (wal a (wal b c)) (wal b (wal a c))
def rho5 a b c := wim (weq a b) (wim (wel a c) (wel b c))
def rho6 a b := wim (wex a (wal a b)) b
def rho7 a b c := wim (weq a b) (wim (weq a c) (weq b c))
def rho8 a b c u := wim (wim (wim c u) a) (wim (wim a c) (wim b c))

def bundle a b c :=
  wa (wex c
        (wa (wal b (wa (wim (wel a b) (wim c (wel c b)))
                        (wim (wel c b) c)))
            (wim c (wel c b))))
     (wa (wim (weq a b) (wal c (weq a b)))
         (wim (wel a b) (wal c (wel a b))))

def gate (a b c : Nat) := if c = a ∨ c = b then 0 else bundle a b c

def pa135Heads (a b c u h : Nat) : List Nat :=
  [rho1 a b,rho2 a b c,rho3 a b c,rho4 a b c,rho5 a b c,
   rho6 a b,rho7 a b c,rho8 a b c u,wal u h]


def stackCode (heads : List Nat) (tail : Nat) : Nat := heads.foldr pair tail

def outputStack (a b c u h savedTop tail : Nat) : Nat :=
  stackCode (pa135Heads a b c u h ++ [savedTop]) tail

@[simp] theorem heads_length (a b c u h : Nat) : (pa135Heads a b c u h).length = 9 := rfl

@[simp] theorem stack_cons (x : Nat) (xs : List Nat) (tail : Nat) :
    stackCode (x::xs) tail = pair x (stackCode xs tail) := rfl

end M6.Source.AXCode

