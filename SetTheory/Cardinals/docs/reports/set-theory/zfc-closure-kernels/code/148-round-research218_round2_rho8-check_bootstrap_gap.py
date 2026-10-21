"""Exact finite check supporting the source-level bootstrap-gap analysis.
It executes no received project code and is not a model search.
"""
from pathlib import Path
import itertools,json
J=((3,3,3,3),(3,3,1,3),(3,3,3,3),(0,0,0,3))
def i(x,y):return J[x][y]
def n(x):return i(x,0)
def l(a,b,c,u):return i(i(i(c,u),a),i(i(a,c),i(b,c)))
def B(p,q,r):return i(i(p,q),i(i(q,r),i(p,r)))
def S(p,q,r):return i(i(p,i(q,r)),i(i(p,q),i(p,r)))
def W(p,q):return i(i(p,i(p,q)),i(p,q))
assert all(i(x,x)==3 and i(0,x)==3 and i(n(n(x)),x)==3 for x in range(4))
assert all(i(x,i(y,x))==3 for x,y in itertools.product(range(4),repeat=2))
assert all(l(a,b,c,0)==3 for a,b,c in itertools.product(range(4),repeat=3))
assert B(1,0,2)==0 and S(1,0,2)==0 and W(1,2)==0
# Ordinary quantification has Boolean value and is top only when each body is
# top. These are exactly the possible value pairs of Q_i A and its current A.
ui_pairs=[(0,a) for a in range(4)]+[(3,3)]
assert all(i(q,a)==3 for q,a in ui_pairs)
def P(a,b):return (a+b)*(a+b+1)//2+b
def I(a,b):return 4*P(a,b)
def R(a,b):return I(a,b)+1
p,q,r=R(2,3),1,R(4,5)
bcode=I(I(p,q),I(I(q,r),I(p,r)))
scode=I(I(p,I(q,r)),I(I(p,q),I(p,r)))
report={'checked':{'I_instances':4,'EFQ_instances':4,'DNE_instances':4,'K_instances':16,
 'L_U_bottom_instances':64,'universal_instantiation_pairs':5},
 'countervaluations':{'B':{'p':1,'q':0,'r':2,'value':0},'S':{'p':1,'q':0,'r':2,'value':0},
 'contraction':{'p':1,'q':2,'value':0}},
 'literal_native_instances':{'p':p,'q':q,'r':r,'B_code':bcode,'S_code':scode},
 'scope':'Finite matrix facts; full retained-row and seed-K soundness is the previously proved HC construction, not this script.'}
Path(__file__).with_name('bootstrap_gap_receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
