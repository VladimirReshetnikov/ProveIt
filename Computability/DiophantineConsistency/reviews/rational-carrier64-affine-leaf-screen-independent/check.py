#!/usr/bin/env python3
"""Independent finite-domain and artifact checks; executes screen, never Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/rational-carrier64-affine-leaf-screen';g=r/'research/rational-carrier64-independent/polynomial.json';coef=r/'candidates/one-page-reversed-carrier65-2521/coefficients'
sha=lambda b:hashlib.sha256(b).hexdigest()
pins={p/'screen.py':'4a11bfec6db2a1cee0d87f71c02fe7cd04f27385001e906cf84616c05201f2fe',p/'result.json':'edd8cbe67b46296ee9b9ae91fd5bbab95a5f09810e5e3dd10ef195d591198638',p/'outer-terminal.json':'05ed6feb7b30c05634538a285b0722cbd5d2064944aea42bcbd8ddfbe82577b9',g:'8fd205a43c4045914d88f4117ba263cf7a232ac26c64dcf09a1c37a8d88e7b27'}
for f,h in pins.items():
 if sha(f.read_bytes())!=h:raise ValueError(('pin',str(f)))
graph=json.loads(g.read_bytes());ret=json.loads((p/'result.json').read_bytes());rows=graph['source'];witness=graph['witnesses'];leaves={'beta','K0','Urank','Wrank'}
if ret['coefficient_scope']!='reversed-carrier65-2521 ports; not current14 ports':raise ValueError('coefficient scope')
if len(rows)!=64 or len(witness)!=14 or len(set(witness))!=14:raise ValueError('graph inventory')
known=set(witness)|leaves|set(range(5));names=set()
for n,op,x,y in rows:
 if n in known or op not in ('+','-','*') or x not in known or y not in known:raise ValueError(('invalid source DAG',n))
 known.add(n);names.add(n)
if '__fresh__' in known or '__new_leaf__' in known:raise ValueError('reserved name collision')
edges={n:(x,y) for n,_,x,y in rows};todo=[graph['output']];live=set()
while todo:
 x=todo.pop()
 if x in edges and x not in live:live.add(x);todo.extend(edges[x])
if live!=names:raise ValueError('source not fully live')
ports={}
for name,meta in graph['coefficient_binding']['ports'].items():
 raw=(coef/meta['file']).read_bytes(); decoded=gzip.decompress(raw)
 if sha(raw)!=meta['gzip_sha256'] or sha(decoded)!=meta['raw_sha256'] or len(decoded)!=meta['raw_bytes']:raise ValueError(('port pin',name))
 ports[name]=int.from_bytes(decoded,'big')
primes=ret['primes'];prod=1
for p0 in primes:
 if p0<2 or any(p0%d==0 for d in range(2,int(p0**0.5)+1)):raise ValueError('prime')
 if ports['beta']%p0==0:raise ValueError('beta not invertible')
 prod*=p0
u=ports['MF']*pow(ports['beta'],-1,prod)%prod
for p0 in primes:
 if u%p0!=(ports['MF']%p0)*pow(ports['beta']%p0,-1,p0)%p0 or (ports['MC']-ports['MF'])%p0!=(ports['MC']%p0-ports['MF']%p0)%p0:raise ValueError('leaf residues')
# Independently reconstruct combinatorial query counts when only literal 0 is an all-sample zero multiplier.
num=[len(witness)+len(leaves)+5+i for i in range(64)];counts=ret['screen']['counts']
if counts['targets']!=64 or counts['constant_queries']!=64 or counts['alias_queries']!=sum(num) or counts['one_affine_queries']!=3*sum(num)-64 or counts['two_affine_queries']!=sum(2*n*(n-1) for n in num):raise ValueError('family counts')
if ret['screen']['original_live']!=64 or ret['screen']['candidates'] or counts['unresolved_zero_scale'] or counts['zero_scale_skips_nonliteral'] or counts['raw_survivors']!=124:raise ValueError('screen result')
ctrl=ret['positive_control'];good=[c for c in ctrl['candidates'] if c['target']=='t' and c['replacement']==['x+c','x'] and c['new_coefficient_mod_primes']==[3,3,3] and c['live']==2]
if ctrl['original_live']!=3 or not good:raise ValueError('positive control')
# Exact arithmetic for the constructed positive control, independent of finite samples.
for x in (-9,0,1,12):
 for y in (-3,0,5):
  if (x+1+2)*y!=(x+3)*y:raise ValueError('positive-control identity')
outer=json.loads((p/'outer-terminal.json').read_bytes())
if outer['session_id']!=67386 or outer['terminal_exit_code']!=0 or outer['returned_session_id'] is not None:raise ValueError('outer observation')
run=subprocess.run([sys.executable,'-I','-S','-B',str(p/'screen.py')],capture_output=True,timeout=120)
if run.returncode!=0 or run.stdout!=(p/'result.json').read_bytes() or run.stderr:raise ValueError(('screen rerun',run.returncode,run.stderr[:300]))
print(json.dumps({'status':'PASS_FINITE_SCREEN_AUDIT','source_rows':64,'source_live_rows':len(live),'runtime_fixed_leaves_before_new':4,'sample_primes':primes,'sample_points_per_prime':ret['samples_per_prime'],'query_counts':counts,'screen_rerun_exit':run.returncode,'coefficient_source':'one-page-reversed-carrier65-2521','scope':'Target-row modular agreement only; no characteristic-zero identity or global lower bound.'},sort_keys=True,indent=2))
