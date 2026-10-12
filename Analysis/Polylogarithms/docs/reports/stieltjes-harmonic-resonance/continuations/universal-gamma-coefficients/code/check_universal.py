"""Compare universal beta formula with every Bell monomial through weight 30."""
from pathlib import Path
from fractions import Fraction as Q
import time,json
from normal_forms import hierarchy
from universal_coefficients import coefficient
ROOT=Path(__file__).resolve().parents[1]

def main():
    start=time.perf_counter();checks=nonzero=0;maximum_d=0
    for m,A,N,H in hierarchy(30):
        for mon in A:
            predicted=coefficient(mon)
            assert predicted==N.get(mon,Q(0)),(m,mon,predicted,N.get(mon,Q(0)))
            checks+=1
            if predicted:
                nonzero+=1;maximum_d=max(maximum_d,len(mon)-1)
                if len(mon)>1:assert (predicted>0)==((len(mon)-1)%2==0)
        assert all(mon in A for mon in N)
    report={'result':'PASS','maximum_weight':30,'coefficient_comparisons':checks,
            'nonzero_coefficients':nonzero,'maximum_derivative_index_checked':maximum_d,
            'elapsed_seconds':time.perf_counter()-start,
            'scope':'Every Bell monomial through weight 30, including all predicted zeros. Independent Fraction normalizer versus positive beta formula.'}
    (ROOT/'data'/'universal_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
