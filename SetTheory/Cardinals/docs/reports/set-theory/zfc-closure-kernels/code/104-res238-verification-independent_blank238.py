from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parents[1]
f=P/'combine/candidate238/zfc_combined238.tm'
rows={}
for line in f.read_text().splitlines():
 if not line.strip() or line.startswith('#'):continue
 q,b,w,d,t=line.split();k=int(q),int(b)
 assert k not in rows and d in ('L','R') and int(w) in (0,1)
 rows[k]=int(w),(-1 if d=='L' else 1),int(t)
assert set(rows)=={(q,b)for q in range(238)for b in(0,1)}
assert all(0<=r[2]<=238 for r in rows.values())
expected=json.loads((P/'combine/zfc239-research-20261019/candidate239/blank_prefix.json').read_text())
wanted=set(expected['all_one_positions']);s=set();q=h=0;minh=maxh=0
for n in range(1,1000001):
 w,d,q=rows[q,int(h in s)]
 if w:s.add(h)
 else:s.discard(h)
 h+=d;minh=min(minh,h);maxh=max(maxh,h)
 if q==84 and h==-5 and s==wanted:break
else:raise AssertionError('No intended initialized frame by bound')
assert n==409835
# Second implementation: dense array transition tables, fresh blank tape.
writes=[0]*476;moves=[0]*476;targets=[0]*476
for (a,b),(w,d,t) in rows.items():writes[2*a+b]=w;moves[2*a+b]=d;targets[2*a+b]=t
origin=10000;tape=bytearray(20001);a=0;x=origin
for _ in range(n):
 key=2*a+tape[x];tape[x]=writes[key];x+=moves[key];a=targets[key]
 assert 0<=x<len(tape)
assert a==q and x-origin==h and {i-origin for i,v in enumerate(tape)if v}==s
result={'status':'PASS','table_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'working_states':238,'rows':476,'start':0,'separate_halt':238,'steps':n,'state':q,'head':h,'head_range':[minh,maxh],'all_one_positions':sorted(s),'all_other_cells_zero':True,'independent_dense_sparse_agreement':True,'matches_predecessor_complete_initialized_frame':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='all_one_positions'},indent=2))
