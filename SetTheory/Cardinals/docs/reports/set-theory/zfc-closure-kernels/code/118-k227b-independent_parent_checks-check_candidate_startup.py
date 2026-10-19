"""Independent exact sparse/dense startup replay for canonical candidates."""
from pathlib import Path
import argparse,json,hashlib
p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('--dispatcher',type=int,default=84);p.add_argument('--limit',type=int,default=2000000);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
t={};start=None
for line in a.table.read_text().splitlines():
 if line.startswith('#! start '):start=int(line.split()[-1])
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();key=int(q),int(b)
 if key in t or d not in ('L','R') or int(w) not in (0,1):raise ValueError('invalid table')
 t[key]=(int(w),1 if d=='R' else -1,int(z))
if start is None:raise ValueError('missing start')
base=json.loads(Path(__file__).with_name('input_startup_receipt.json').read_text());expected=set(base['all_nonzero_tape_cells']);q=start;h=0;s=set();lo=hi=0
for steps in range(a.limit+1):
 if q==a.dispatcher and h==base['head'] and s==expected:break
 b=int(h in s);w,d,q=t[q,b]
 if w:s.add(h)
 else:s.discard(h)
 h+=d;lo=min(lo,h);hi=max(hi,h)
else:raise ValueError('exact initialized frame not found')
# Different representation; reject any out-of-range access.
dense=[0]*(hi-lo+3);offset=1-lo;hd=offset;qd=start
for _ in range(steps):
 w,d,qd=t[qd,dense[hd]];dense[hd]=w;hd+=d
 if not 0<=hd<len(dense):raise ValueError('dense bound')
if qd!=q or hd-offset!=h or {j-offset for j,b in enumerate(dense) if b}!=s:raise ValueError('dense mismatch')
result={'status':'PASS_TWO_ENGINE_EXACT_STARTUP','table_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'steps':steps,'state':q,'head':h,'ones':len(s),'head_range':[lo,hi],'exact_whole_tape_matches_k230':True,'baseline_steps':base['startup_steps']}
a.output.write_text(json.dumps(result,indent=2)+'\n');print(result)
