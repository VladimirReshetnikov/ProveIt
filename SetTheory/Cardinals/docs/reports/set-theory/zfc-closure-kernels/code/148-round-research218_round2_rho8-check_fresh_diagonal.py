"""Small independent arithmetic/algebra receipt for the written theorem.
This finite check is not a substitute for the unbounded Heyting argument.
"""
from pathlib import Path
import itertools,json
H=(0,1,4,5,6,7); TOP=7
# Upsets of the poset with sole strict relation 1<2; implication is largest
# upset z satisfying x intersect z subset y, computed directly rather than
# copying a truth table from prior research.
def imp(x,y):
 candidates=[z for z in H if (x&z)&~y==0]
 return max(candidates,key=lambda z:sum((z>>i)&1 for i in range(3)))
def neg(x):return imp(x,0)
def L(a,b,c,u):return imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c)))
regular=[c for c in H if neg(neg(c))==c]
checks=0
for a,b,c,u in itertools.product(H,repeat=4):
 if c in regular:
  assert L(a,b,c,u)==TOP
  checks+=1
for c in H:assert L(0,TOP,c,0)==imp(neg(neg(c)),c)
def P(a,b):return (a+b)*(a+b+1)//2+b
def I(a,b):return 4*P(a,b)
def R(a,b):return 4*P(a,b)+1
def Q(a,b):return 4*P(a,b)+2
c=Q(3,I(R(1,2),1))
q={0:0,1:1,4:0,5:1,6:4,7:7}
x=q[neg(1)]
assert x==4 and L(0,TOP,x,0)==5
report={'heyting_values':H,'regular_values':regular,'regular_C_L_checks':checks,
 'diagonal_reduction_checks':len(H),
 'old_KS_model_rejected':{'A_code':1,'B_code':0,'C_code':c,'U_code':R(0,c),
  'C_value':x,'row_value':L(0,TOP,x,0),'designated':TOP,
  'C_formula':'Q_3(not R(1,2))','assignment':'s(1)=0, s(2)=1, s(0)=s(C_code)=0; s(3) arbitrary'}}
Path(__file__).with_name('fresh_diagonal_receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
