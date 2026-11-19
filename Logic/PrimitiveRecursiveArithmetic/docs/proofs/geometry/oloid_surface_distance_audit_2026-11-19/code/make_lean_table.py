"""Generate the self-contained Lean replay of static decimal claims."""
import csv
from fractions import Fraction as Q
from pathlib import Path


root = Path(__file__).resolve().parents[1]
data = root/'data'


def scaled(string, digits):
    q = Q(string)*10**digits
    if q.denominator != 1:
        raise ValueError('decimal scaling error')
    return q.numerator


preamble = '''import Std

/-! Concrete integer consequences of the certified decimal intervals. The
geometric enclosure of a distance and the gradient estimate are supplied by
the analytic proof and separate interval replay. `by decide` kernel-checks
these finite table statements without native code or analytic axioms. -/
namespace Oloid.DecimalTable

/-- Old endpoints use 14 decimal places, refined endpoints 50, the published
rounding 40, and residual/contact radii 40. The old table uses 8 places. -/
structure Row where
  i : Nat
  j : Nat
  curved : Bool
  oldLo : Nat
  oldHi : Nat
  lo : Nat
  hi : Nat
  rounded : Nat
  oldRounded : Nat
  residual : Nat
  radius : Nat
  deriving DecidableEq, Repr

def roundedNat (n scale : Nat) : Nat := (2*n+scale)/(2*scale)

def valid (r : Row) : Bool :=
  decide (1 ≤ r.i ∧ r.i < r.j ∧ r.j ≤ 10 ∧
    r.oldLo * 10^36 < r.lo ∧ r.hi < r.oldHi * 10^36 ∧ r.hi = r.lo + 1 ∧
    roundedNat r.lo (10^10) = r.rounded ∧ roundedNat r.hi (10^10) = r.rounded ∧
    roundedNat r.lo (10^42) = r.oldRounded ∧ roundedNat r.hi (10^42) = r.oldRounded ∧
    r.residual ≤ 123065 ∧ r.radius ≤ 3938049 ∧ r.radius ≤ 32*r.residual ∧
    (r.curved = true ↔ 0 < r.residual))

/-- Row order is lexicographic on the 45 pairs 1 ≤ i < j ≤ 10. -/
def rows : List Row := [
'''
postscript = ''']

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem all_rows_valid : rows.all valid = true := by decide

/-- Check coverage of the intended pairs, including their order. -/
def pairs : List (Nat × Nat) :=
  (List.range 10).flatMap fun i =>
    ((List.range (9-i)).map fun d => (i+1,i+d+2))

theorem coverage : rows.map (fun r => (r.i,r.j)) = pairs := by decide

theorem counts : rows.length = 45 ∧ (rows.filter (fun r => r.curved)).length = 20 := by decide

end Oloid.DecimalTable
'''

def main():
    import re
    saved = {(a,b):v for a,b,v in re.findall(r'\$(\d+),(\d+)\$ & \$(\d+\.\d+)\$',
                  (data/'original_distance_rows.tex').read_text())}
    with (data/'distances.csv').open(newline='') as f:
        old = {(r['from'],r['to']):r for r in csv.DictReader(f)}
    lines=[]
    with (data/'refined_distances.csv').open(newline='') as f:
        for r in csv.DictReader(f):
            p,q = r['from'],r['to']
            r0 = old[(p,q)]
            i,j = p[1:],q[1:]
            flag = 'true' if r['gradient_norm_upper'] else 'false'
            parts = [i,j,flag,scaled(r0['lower'],14),scaled(r0['upper'],14),scaled(r['lower'],50),
                     scaled(r['upper'],50),scaled(r['rounded_40'],40),scaled(saved[i,j],8),
                     scaled(r['gradient_norm_upper'] or '0',40),scaled(r['contact_radius_upper'] or '0',40)]
            lines.append('  ⟨'+', '.join(map(str,parts))+'⟩')
    out = root/'lean'/'DecimalTable.lean'
    out.parent.mkdir(exist_ok=True)
    out.write_text(preamble + ',\n'.join(lines) + postscript)

if __name__=='__main__':
    main()
