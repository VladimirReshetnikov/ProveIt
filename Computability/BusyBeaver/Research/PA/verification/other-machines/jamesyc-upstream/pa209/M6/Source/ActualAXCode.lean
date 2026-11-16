module
public import M6.Source.AXCode
@[expose] public section
/-! Additive arithmetic specification extracted from the exact AX macro program.
The historical AXCode specification is unchanged. Full source binding is separate. -/
namespace M6.Source.ActualAXCode
open AXCode (wim wal wel weq wn wa wex)
abbrev rho1 := AXCode.rho1
abbrev rho2 := AXCode.rho2
def rho3 a b c := wim (weq a b) (wim (wel c a) (wel c b))
abbrev rho4 := AXCode.rho4
def rho5 a b c := wim (weq c a) (wim (wel c b) (wel a b))
abbrev rho6 := AXCode.rho6
def rho7 a b c := wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b)))
abbrev rho8 := AXCode.rho8

def point (_a b c : Nat) := wim c (wel c b)
def separation a b c :=
  wal b (wa (wim (wel a b) (point a b c)) (wim (wel c b) c))
def memVac a b c := wim (wel a b) (wal c (wel a b))
/-- Raw numeric structure, without claiming literal equality to classical rewrites. -/
def bundle a b c := wn (wim (memVac a b c) (wal c (wim (separation a b c) (wn (point a b c)))))
def gate a b c := if c=a ∨ c=b then 0 else bundle a b c
def pa135Heads a b c u h :=
  [rho1 a b,rho2 a b c,rho3 a b c,rho4 a b c,rho5 a b c,
   rho6 a b,rho7 a b c,rho8 a b c u,wal u h]
end M6.Source.ActualAXCode

