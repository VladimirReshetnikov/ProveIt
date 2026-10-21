"""Owned fixed numeric certificate replay. No formula enumeration or received code."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).parent
def P(a,b): return (a+b)*(a+b+1)//2+b
def I(a,b): return 4*P(a,b)
def U(e,b,c): return I(b,c)+e
def H(e,a,b,c): return I(I(I(c,U(e,b,c)),a),I(I(a,c),I(b,c)))
rows=[]
def ax(e,a,b,c):
    rows.append({'id':len(rows)+1,'rule':'H_'+str(e),'parameters':[a,b,c],'code':H(e,a,b,c)})
    return len(rows)
def mp(major,minor,conclusion):
    assert major<=len(rows) and minor<=len(rows)
    assert rows[major-1]['code']==I(rows[minor-1]['code'],conclusion)
    rows.append({'id':len(rows)+1,'rule':'MP','major':major,'minor':minor,'code':conclusion})
    return len(rows)
ax(0,1,0,0);ax(1,40,0,0);mp(2,1,21523360)
ax(0,4,0,0);ax(0,3280,1,0);mp(5,4,I(21523360,4));mp(6,3,4)
assert I(1,0)==4 and rows[-1]['code']==4
result={'status':'PASS_FIXED_NATIVE_CODE4_PROOF','axioms':4,'MP_steps':3,'nodes':rows,
        'formula_search':False,'received_code_executed':False,
        'scope':'This verifies the seven-node theorem4 certificate, not by itself the uniform consistency invariant.'}
(ROOT/'FIXED_CODE4_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='nodes'},indent=2))
