"""Exact-domain checks for the supported small build/export interface."""
import copy,json
from pathlib import Path
import example_emitter as e
import check_example as v
H=Path(__file__).resolve().parent
class IntSubclass(int):pass

def must_reject(action,description):
    try:action()
    except (ValueError,TypeError):return
    raise RuntimeError('Accepted '+description)
def main():
    bad_targets=[(),(1,),[1,2,3],(2,1),(1,1),(True,2),(0,False),(1.0,2),(0,2.0),(IntSubclass(0),2),'12',
        (float(2**60),2**60+10),(2**60,float(2**60+1))]
    for target in bad_targets:must_reject(lambda:e.build(target=target),repr(target))
    huge=10**300
    c,rounds,out=e.build(h=-huge,gap=5,T=1,K=2,target=(-huge+1,-huge+6))
    if c.score()!=0:raise RuntimeError('huge exact integers')
    for arg in [dict(h=True),dict(h=IntSubclass(0)),dict(gap=5.0),dict(T=True),dict(K=2.0)]:must_reject(lambda:e.build(**arg),repr(arg))
    data=json.loads((H/'example-polynomial.json').read_text());w=json.loads((H/'example-witness.json').read_text())
    v.check_artifact(data,w)
    mutated=0
    for replacement in (True,1.0,IntSubclass(1),float(2**60)):
        bad=copy.deepcopy(data);bad['residuals'][0][0][0]=replacement
        must_reject(lambda:v.check_artifact(bad,w),'noninteger residual coefficient');mutated+=1
    bad=copy.deepcopy(data);bad['expanded_quartic'][0][0]=float(bad['expanded_quartic'][0][0]);must_reject(lambda:v.check_artifact(bad,w),'float expanded coefficient');mutated+=1
    for mono in ([0,0,0],[True],[-1],[len(w)+3]):
        bad=copy.deepcopy(data);bad['residuals'][0][0][1]=mono
        must_reject(lambda:v.check_artifact(bad,w),'invalid residual monomial');mutated+=1
    bad=copy.deepcopy(data);bad['source']['class_cut']=False;must_reject(lambda:v.check_artifact(bad,w),'Boolean source integer');mutated+=1
    r=dict(status='passed',optimized=not __debug__,malformed_targets_rejected=len(bad_targets),other_interface_cases_rejected=5,
        malformed_serialized_polynomials_rejected=mutated,huge_coordinate_decimal_digits=301)
    (H/('interface-optimized-receipt.json' if not __debug__ else 'interface-receipt.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
