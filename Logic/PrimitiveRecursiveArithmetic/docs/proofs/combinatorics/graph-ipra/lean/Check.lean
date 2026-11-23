import GraphCore
import CutParity
import ColorCert

#print axioms GraphIPRA.handshaking
#print axioms GraphIPRA.walks_pos
#print axioms GraphIPRA.reachableBy_iff
#print axioms GraphCutParity.even_iff_all_cuts
#print axioms GraphCutParity.euler_boundary
#print axioms GraphIPRA.differentCliqueColours
#print axioms GraphIPRA.noOddClosedWalk

namespace GraphIPRA.ArticleExample

/-- The seven edges 12, 15, 23, 25, 34, 45 and 46 in one-based article labels. -/
def edge := arc 6 8788157778

/-- Digits 0,1,0,1,2,0 in base three. -/
def colour := digit 3 192

example : properB 6 3 edge colour = true := by decide

/-- The triangle with zero-based indices 0,1,4, stored in base six. -/
example : cliqueB 6 3 edge (digit 6 150) = true := by decide

example : walks edge 6 0 2 3 = 1 := by decide

end GraphIPRA.ArticleExample
