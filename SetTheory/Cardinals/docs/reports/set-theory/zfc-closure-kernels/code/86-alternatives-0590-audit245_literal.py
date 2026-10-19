from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parents[1]/'audit245/extracted/zfc245-proof-20261018'
p=P/'machine/zfc245.tm'; raw=p.read_bytes(); rows={}
for line in raw.decode().splitlines():
 if not line.strip() or line.startswith('#'):continue
 q,b,w,d,t=line.split(); key=(int(q),int(b));assert key not in rows
 assert d in ['L','R'] and int(w) in (0,1)
 rows[key]=(int(w),1 if d=='R' else -1,int(t))
assert set(rows)=={(q,b)for q in range(245)for b in (0,1)}
assert all(0<=x[2]<=245 for x in rows.values())
s=set();q=h=0
for step in range(1,1000001):
 w,d,q=rows[q,int(h in s)]
 if w:s.add(h)
 else:s.discard(h)
 h+=d
 if step==407915:break
else:raise AssertionError('No dispatcher')
c=json.loads((P/'certificate/blank_boot.json').read_text())
assert step==407915 and h==-5 and sorted(s)==c['all_one_positions']
# Independent dense representation and run, including all touched zero cells.
tape=bytearray(2000001); off=1000000; h2=off;q2=0
for _ in range(step):
 w,d,q2=rows[q2,tape[h2]];tape[h2]=w;h2+=d
assert q2==q and h2-off==h and {i-off for i,b in enumerate(tape)if b}==s
result={'status':'PASS','sha256':hashlib.sha256(raw).hexdigest(),'working_states':245,'rows':len(rows),'start':0,'separate_halt':245,'certified_initialization_steps':step,'dispatcher':q,'head':h,'all_ones_match_certificate':True,'independent_sparse_dense_agreement':True,'ones':len(s),'minimum_one':min(s),'maximum_one':max(s)}
assert result['sha256']=='17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13'
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2))
