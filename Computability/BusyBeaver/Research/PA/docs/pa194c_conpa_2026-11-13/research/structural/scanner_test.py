import sys,json
from pathlib import Path
PACKAGE=Path(__file__).resolve().parents[2]
ROOT=PACKAGE/'reference/pa194'
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c
for tag,table,sp,ip in [('194',ROOT/'construction/tables/pa194.native.tm',ROOT/'construction/source/pa194.sites.json',ROOT/'construction/source/pa194.instructions.json'),('194C',PACKAGE/'tables/pa194C.native.tm',PACKAGE/'source/pa194C.sites.json',PACKAGE/'source/pa194C.instructions.json')]:
 rows={}
 for line in table.read_text().splitlines():
  q,b,w,d,n=line.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
 sites=json.loads(sp.read_text());instructions=json.loads(ip.read_text());cs=[]
 for i,code in enumerate(instructions):
  path=tuple(map(int,sites[i][0]));st=c.frame(path)
  target=lambda n,extra=0,effect=c.PLAIN:c.canonical(c.frame(tuple(map(int,sites[n][0])),extra,effect))
  if code[0]=='inc':
   _,r,n=code;cs.append((i,None,st,target(n,0,('x','inc',c.PHYSICAL[r]))))
  elif code[0]=='dec':
   _,r,z,p=code;cs.append((i,(c.PHYSICAL[r],True),st,target(z)));cs.append((i,(c.PHYSICAL[r],False),st,target(p,1,('x','dec',c.PHYSICAL[r]))))
  elif code[0]=='jump':cs.append((i,None,st,target(code[1])))
  else:cs.append((i,None,st,None))
 rows={k:v for k,v in rows.items()if k[0]!=34};rows[23,0]=0,True,75
 failed=[]
 for contract in cs:
  if c.run(rows,contract) is None:failed.append([contract[0],contract[1],sites[contract[0]]])
 print(tag,'failed',len(failed),'contracts',len(cs),'first',failed[:15],flush=True)
 Path(__file__).with_name(f'scanner_delete34_{tag}.json').write_text(json.dumps({'failed':failed,'contracts':len(cs)},indent=2))
