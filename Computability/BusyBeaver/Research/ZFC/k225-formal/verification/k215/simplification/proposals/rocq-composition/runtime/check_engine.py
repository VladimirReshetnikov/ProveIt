if not __debug__:
 raise RuntimeError('Assertions must be enabled')
from pathlib import Path
import json,re,hashlib
from check_decoder import table
D=Path(__file__).parent
src=(D/'KTape.reference.lean').read_text()
s=re.search(r'def boxStates : List Nat :=\s*\[([^]]+)\]',src)
states=list(map(int,re.findall(r'\d+',s[1])))
assert states==[0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198]
rows={(q,b)for q in states for b in(0,1)if b or q not in(113,198)}
T={n:table(D/'inputs'/f'{n}.tm') for n in ['K215_Formal','ST215','DR215']}
out={'reference_sha256':hashlib.sha256(src.encode()).hexdigest(),'protected_rows':sorted(rows),'row_count':len(rows),'tables':{}}
for n,t in T.items():
 diffs=[(q,b)for q,b in rows if t[q,b]!=T['K215_Formal'][q,b]]
 tail=t[198,0]
 out['tables'][n]={'protected_differences_from_certified_K215':diffs,'tail':tail,'maintained_IncTail_bypass':tail==(1,-1,40)}
 assert not diffs
assert T['ST215'][198,0]==T['DR215'][198,0]==(0,-1,40)
assert not({(199,1),(206,0)}&rows)
(D/'ENGINE_FOOTPRINT.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
