#!/usr/bin/env python3
"""Recheck AST transport, degree witness and coefficient files for external sign24."""
import gzip,hashlib,json,random,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
p=Path(__file__).resolve().parent;old=p.parent/'nine-sharing-sign25-octic-ell-candidate/seed.json';new=p/'seed.json';H=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert H(old)=='c95637ae24a57dba0ae1113a8256ed6f12d33f416f035f9cd4f92cffdbf59fc8' and H(new)=='24a6dcf05b96112cfa332aafe4790a367c44b9a0cc033a74197f92d3520ab865';a=json.loads(old.read_text());b=json.loads(new.read_text());assert a['witness_count']==25 and b['witness_count']==24 and b['total_coordinates']==25 and b['distinguished_input_coordinate']==0 and b['fixed_ports']==a['fixed_ports'] and b['coefficient_binding']==a['coefficient_binding'];ar=a['residuals'];br=b['residuals'];assert len(ar)==16 and len(br)==15
q=next(r for r in ar if r['gate']=='q3');assert q['kind']=='positive' and q['expr'][0:2]==['sub',['var',15]];rhs=q['expr'][2];assert rhs==['mul',['mul',['add',['mul',['port','beta'],['add',['var',1],['num',1]]],['num',1]],['add',['mul',['port','beta'],['add',['var',1],['num',1]]],['num',1]]],['add',['mul',['port','beta'],['add',['var',1],['num',1]]],['num',1]]]
def match(x,y):
 op=x[0]
 if op=='var':
  i=x[1];return y==b['lift_expression'] if i==15 else y==['var',i if i<15 else i-1]
 if op in ('num','port'):return x==y
 return op in ('add','sub','mul') and len(x)==len(y)==3 and op==y[0] and match(x[1],y[1]) and match(x[2],y[2])
assert match(rhs,b['lift_expression']) and [r['gate'] for r in br]==[r['gate'] for r in ar if r['gate']!='q3']
for x,y in zip((r for r in ar if r['gate']!='q3'),br):assert x['kind']==y['kind'] and match(x['expr'],y['expr'])
def degree(t,special=False):
 if t[0]=='var':assert 0<=t[1]<25;return int(t[1] in (16,17)) if special else 1
 if t[0] in ('num','port'):return 0
 assert t[0] in ('add','sub','mul');x,y=degree(t[1],special),degree(t[2],special);return x+y if t[0]=='mul' else max(x,y)
ds={r['gate']:degree(r['expr']) for r in br};ws={r['gate']:degree(r['expr'],True) for r in br};assert max(ds.values())==4 and ws['N0']==4 and all(d<=2 for n,d in ws.items() if n!='N0')
def eval_(t,v,ps):
 op=t[0]
 if op=='num':return t[1]
 if op=='var':return v[t[1]]
 if op=='port':return ps[t[1]]
 x,y=eval_(t[1],v,ps),eval_(t[2],v,ps);return x+y if op=='add' else x-y if op=='sub' else x*y
n0=next(r['expr'] for r in br if r['gate']=='N0')
for t in range(5):
 v=[0]*25;v[16]=v[17]=t;assert eval_(n0,v,{})==-t**4-2*t*t-1
coeff=p/b['coefficient_binding']['path'];assert coeff.resolve()==(old.parent/a['coefficient_binding']['path']).resolve();files={}
for name,rec in b['coefficient_binding']['ports'].items():
 file=coeff/rec['file'];assert H(file)==rec['gzip_sha256'];raw=gzip.decompress(file.read_bytes());assert hashlib.sha256(raw).hexdigest()==rec['raw_sha256'] and len(raw)==rec['raw_bytes'];files[name]=H(file)
 if name=='beta':assert any(raw)
rng=random.Random(2524)
for _ in range(16):
 v=[rng.randrange(4) for _ in range(25)];ps={k:rng.randrange(5) for k in b['fixed_ports']};z=eval_(b['lift_expression'],v,ps);lift=v[:15]+[z]+v[15:];assert z>=0 and len(lift)==26 and lift[0]==v[0] and eval_(q['expr'],lift,ps)==0;assert [eval_(r['expr'],lift,ps) for r in ar if r['gate']!='q3']==[eval_(r['expr'],v,ps) for r in br]
assert json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(p/'build.py'),'--check'],capture_output=True,text=True,check=True,timeout=120).stdout)['status']=='PASS'
print(json.dumps({'status':'PASS_EXTERNAL_CHECK','source_sha256':H(old),'candidate_sha256':H(new),'structural_transfers':15,'residual_syntactic_degrees':ds,'weighted_degrees_v16_v17':ws,'N0_specialization':'-t^4-2*t^2-1','square_sum_exact_total_degree':8,'coefficient_gzip_sha256':files,'finite_nonnegative_beta_lifts':16,'scope':'external fixed nonnegative-beta ports only; no Lean bridge or endpoint'},sort_keys=True,indent=2))
