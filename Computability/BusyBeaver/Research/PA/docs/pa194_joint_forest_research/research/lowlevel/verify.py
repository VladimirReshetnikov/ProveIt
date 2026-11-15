"""Quick replay of source certificates and input identity; heavy searches are optional."""
from pathlib import Path
import json,hashlib,runpy
B=Path(__file__).resolve().parent
if(B/'SHA256.json').exists():
 for n,h in json.loads((B/'SHA256.json').read_text()).items():assert hashlib.sha256((B/n).read_bytes()).hexdigest()==h,n
import common as c
summary={}
for name,rows,cs in [('primary194',c.rows,c.cs)]:
 result=c.r.validate(rows,cs);assert result['ok'],result;summary[name]=result
p=c.rows;assert p[51,0]==(0,True,16) and p[16,1]==p[122,1]==(0,False,1)
def core(rows):
 out={k:(w,d,88 if n==301 else n)for k,(w,d,n)in rows.items()if k[0]!=301};out[88,0]=(0,False,51);out[51,0]=(0,True,122);return out
def table(path):
 out={}
 for line in path.read_text().splitlines():
  q,b,w,d,n=line.split();out[int(q),int(b)]=int(w),d=='R',int(n)
 return out
rr=table(B/'runtime193.native.tm');assert rr==core(p)and len(rr)==386
result=c.r.validate(rr,c.cs);assert result['ok'];summary['primary_runtime193']=result
import forest_common as f
assert f.rows[16,1]==f.rows[122,1]==(0,False,1)
result=f.r.validate(f.rows,f.cs);assert result['ok'];summary['forest194']=result
rr=table(B/'forest/runtime193.native.tm');assert rr==core(f.rows)and len(rr)==386
result=f.r.validate(rr,f.cs);assert result['ok'];summary['forest_runtime193']=result
runpy.run_path(str(B/'check_interval_certificate.py'),run_name='__main__')
summary['scope']='Symbolic source implementation with inherited register-block interface. No blank-start 193-state consistency result and no completed iPRA calibration is asserted.'
print(json.dumps(summary,indent=2))
