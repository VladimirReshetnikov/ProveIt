from pathlib import Path
import json, hashlib
root=Path(__file__).resolve().parents[1]/'portable'/'upstream'/'K230'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((root/'manifest.json').read_text())
checked={}
for name,expected in m['local_files'].items():
 actual=sha(root/name)
 if actual!=expected:raise ValueError(('hash',name,actual,expected))
 checked[name]=actual
table={}
for row in (root/'machine/k230.tm').read_text().splitlines():
 if not row or row.startswith('#'):continue
 q,b,w,d,z=row.split();key=int(q),int(b)
 if key in table:raise ValueError(('duplicate',key))
 table[key]=(int(w),1 if d=='R' else -1,int(z))
if set(table)!={(q,b) for q in range(230) for b in range(2)}:raise ValueError('domain')
if sha(root/'machine/k230.tm')!=m['machine_sha256']:raise ValueError('table hash')
if sha(root/'machine/sites230.json')!=m['sites_sha256']:raise ValueError('sites hash')
ones=set();q=h=0;lo=hi=0;visited=set()
for i in range(408419):
 b=int(h in ones);visited.add((q,b));w,d,q=table[q,b]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d;lo=min(lo,h);hi=max(hi,h)
# Whole tape expected from the explicitly stated zipper in Boot230.v.
regs=[0,0,0,3,0,0,3,0,0]+[1]*167
right=[0]*181+[1]
for n in regs:right += [0]+[1]*(n+1)
expected={h-1}|{h+i for i,b in enumerate(right) if b}
if q!=84 or ones!=expected:raise ValueError(('startup mismatch',q,h,len(ones),len(expected)))
# Independent dense execution: array bounds checked at every step.
a=[0]*2048;qd=0;hd=512
for i in range(408419):
 w,d,qd=table[qd,a[hd]];a[hd]=w;hd+=d
 if not 0<=hd<len(a):raise ValueError('dense bound')
if qd!=q or hd-512!=h or {j-512 for j,b in enumerate(a) if b}!=ones:raise ValueError('dense mismatch')
result={'status':'PASS_INPUT_HASHES_AND_TWO_ENGINE_EXACT_STARTUP','local_files':len(checked),'table_sha256':m['machine_sha256'],'sites_sha256':m['sites_sha256'],'states':230,'rows':460,'startup_steps':408419,'state':q,'head':h,'ones':len(ones),'head_range':[lo,hi],'physical_registers':regs[:9],'spares':167,'spare_value':1,'all_nonzero_tape_cells':sorted(ones),'visited_rows':len(visited),'fresh_rocq_build':False}
(Path.cwd()/'k230_input_startup_replay.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items() if k!='all_nonzero_tape_cells'})
