"""Fresh initialized-core replay. Only owned runtime code is imported."""
from pathlib import Path
import sys,json,hashlib,time,itertools
D=Path(__file__).resolve().parent;ROOT=D.parent
K=ROOT/'k223_merged_runtime_audit/runtime'
sys.path.insert(0,str(K));import symbolic_runtime as S
assert __debug__ and not sys.flags.optimize
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
P=ROOT/'research217_review/contextual/selected/machine'
tp=P/'k218.native.tm';p=tp;sp=P/'sites218.json';m=ROOT/'latest219_baseline/source132/portable/runtime/reference_results/legacy_mapping.json'
assert H(p)=='3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1'
assert H(sp)=='1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe'
assert H(m)=='26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'
native={}
for line in p.read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert d in ('L','R') and b in (0,1) and w in (0,1) and (q,b)not in native
 native[q,b]=(w,1 if d=='R'else -1,z)
Q={q for q,b in native};assert len(Q)==218 and len(native)==436 and set(native)==set(itertools.product(Q,(0,1)))
assert {z for w,d,z in native.values()}-Q=={254}
mp={int(q):int(z)for q,z in json.loads(m.read_text()).items()}
for q in Q|{254}:
 if q not in mp:mp[q]=q+1000
assert len(mp)==len(set(mp.values()))and(mp[0],mp[84],mp[254])==(95,96,254)
(D/'NATIVE_TO_RUNTIME.json').write_text(json.dumps({q:mp[q] for q in sorted(Q|{254})},indent=2)+'\n')
T={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in native.items()};ss=json.loads(sp.read_text())
leaves={p:(o,a)for p,o,a in ss};prefix={p[:i]for p in leaves for i in range(len(p))}
assert len(leaves)==len(ss)==4744 and len(prefix)==4743 and not leaves.keys()&prefix
assert all(p+b in leaves or p+b in prefix for p in prefix for b in '01')
assert [p for p,o,a in ss]==sorted(leaves)
assert all(p and set(p)<={'0','1'}and len(p)<=64 and o in ('CI','CD','CB','CC','CH')and(a is None if o=='CH'else type(a)is int and(0<=a<9 if o in('CI','CD')else a>=1))for p,o,a in ss)
ids={};paths={}
def intern(n):
 if n not in ids:ids[n]=len(ids)
 return ids[n]
for p,(o,a)in leaves.items():paths[p]=intern(('L',o,a))
for p in sorted(prefix,key=len,reverse=True):paths[p]=intern(('N',paths[p+'0'],paths[p+'1']))
metrics={'dag_nodes':len(ids),'leaves':len(ss),'max_depth':max(map(len,leaves)),'max_zero_run':max(len(r)for p in leaves for r in p.split('1'))};assert metrics=={'dag_nodes':205,'leaves':4744,'max_depth':38,'max_zero_run':6}
assert S.r.PHY==(6,2,0,4,3,7,8,5,1)
lemmas,blocks=S.prove_blocks(T);cases=[];rows=set();started=time.monotonic()
for i,site in enumerate(ss):
 for positive in((False,True)if site[1]=='CD'else(False,)):
  ans=S.case(T,lemmas,site,positive);rows.update(ans.pop('rows'));ans.pop('trace');cases.append(dict(index=i,positive=positive,**ans))
  if len(cases)%500==0:print('PROVED',len(cases),'seconds',round(time.monotonic()-started,2),flush=True)
assert len(cases)==6167 and rows==set(T)
assert sum(x['symbolic_steps']for x in cases)==1514325 and min(x['duration'][0]for x in cases)==13
res=dict(status='FRESH_OWNED_KERNEL_FULL_CONTEXTUAL_K218_RUNTIME_PASS',table_sha256=H(tp),source_sha256=H(sp),input_pins={str(f.relative_to(ROOT)):H(f)for f in[tp,sp,m,K/'symbolic_runtime.py',K/'independent_runtime.py',Path(__file__)]},cases=len(cases),rules=sum(x['symbolic_steps']for x in cases),minimum_duration=min(x['duration'][0]for x in cases),row_coverage=len(rows),metrics=metrics,block_schemas=blocks,seconds=time.monotonic()-started,physical_map=S.r.PHY,spare_append_value=1,blank_startup_checked_separately=True)
(D/'CASES.json').write_text(json.dumps(cases,indent=2,sort_keys=True)+'\n');res['cases_sha256']=H(D/'CASES.json')
(D/'RUNTIME_RESULT.json').write_text(json.dumps(res,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in res.items()if k!='block_schemas'},indent=2),flush=True)
