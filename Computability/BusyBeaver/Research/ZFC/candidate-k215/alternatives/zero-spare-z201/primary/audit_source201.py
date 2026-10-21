import sys
if not __debug__: raise SystemExit("Run without -O: assertions are required for verification.")
from pathlib import Path
import sys,json,hashlib
P=Path(__file__).resolve().parent;F=P/'inherited/research/command_family'
sys.path.insert(0,str(F));import audit_command_permutation as a
raw=(F/'201/sites.json').read_bytes();rows=json.loads(raw);t=a.parse(rows);g=a.counter_graph(rows);assert g==a.structured_graph(t)
selectors,fields,packed=a.selector_audit(t,(2,0,1));returns=a.return_audit(t,(2,0,1))
r=[2,0,2,0,0,0,0,0,0];pc=0;trace=[];roots=[]
for tick in range(436):
 if pc==0:roots.append(dict(steps=tick,registers=r.copy()))
 if tick==435:break
 _,op,k=rows[pc];assert op!='CH';trace.append([pc,r.copy()])
 if op=='CD':b=int(r[k]>0);r[k]-=b;pc=g[pc][2][b]
 elif op=='CI':r[k]+=1;pc=g[pc][2][0]
 else:pc=g[pc][2][0]
assert pc==0 and r==[5,0,0,0,1,0,0,0,0]
out=dict(status='PASS',source_sha256=hashlib.sha256(raw).hexdigest(),source_steps=435,roots=roots,trace=trace,selectors=selectors,fields=fields,returns=returns,commands=['NIP','NIP','DROP','MP(1)'],scope='Two independent inherited CFG readers agree; exact435 primitive execution contains no CH. Whole-source command-permutation finite premises verified. Calibration theorem is separate.')
assert json.loads((P/'audit_source201.json').read_text())==out;print(json.dumps({k:v for k,v in out.items()if k not in('trace','selectors','fields','returns')},indent=2))
