"""Exact comparison of the new cached envelope with an interior two-stage one."""
from fractions import Fraction as F
from pathlib import Path
import json,sys
from verify_cache_schedule import sqrtlo,sqrthi,demand

def main():
    x0=F(89,5000); A=F(1577,50000); theta=F(279,1000)
    x1=(A-x0)*(1-theta)
    demand(7**89<2**250,'root packing')
    demand(9**1577<2**5000,'tail packing')
    demand(F(2,9)<F(1,4)<theta,'uniform taper bootstrap')
    omega_lo=F(2807,1000)
    demand(7**1000>2**2807,'Strassen log lower enclosure')
    root_new_upper=sqrthi(F(30,49)/x0)
    prefix_lower=sqrtlo(F(12,49)/x0)
    tail_strassen_sq=F(54,81)-(1-(omega_lo-2)**2)*F(18,81)
    old_lower=prefix_lower+F(2,7)*sqrtlo(tail_strassen_sq/x1)
    demand(root_new_upper<old_lower,'new coefficient is not below comparator')
    # Storage maxima: the two schedules have exactly the same root expression.
    root_memory_lower=sqrtlo(F(24,49)/x0)
    old_tail_memory_upper=F(2,7)*sqrthi(F(36,81)/x1)
    demand(old_tail_memory_upper<root_memory_lower,'comparator tail memory exceeds root')
    out={'status':'PASS','comparator_root_x':str(x0),'comparator_tail_total_A':str(A),
         'comparator_tail_theta':str(theta),'new_root_normalized_upper':str(root_new_upper),
         'comparator_descendant_normalized_lower':str(old_lower),
         'same_root_memory_expression':True,
         'scope':'Comparison of upper-bound envelopes, not actual algorithm running times; no global optimality claim.'}
    p=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'results/comparison_checks.json'
    p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
