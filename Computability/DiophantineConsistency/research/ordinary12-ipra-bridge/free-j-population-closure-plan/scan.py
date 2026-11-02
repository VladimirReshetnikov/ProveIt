import hashlib,json,re,os,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent
root=HERE.parents[2];pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');freej=Path('/tmp/ipra-freej-power-finish-pair-01');succ=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01')
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
sources={}
for loc in (root/'Lean/DiophantineConsistency',root/'research/ordinary12-ipra-bridge'):
 for p in loc.rglob('*.lean'):sources.setdefault(p.stem,[]).append(p)
def scan(base,targets):
 seen=set();bad=[];out=[]
 def go(n):
  if n in seen:return
  seen.add(n);rel=Path(*n.split('.')).with_suffix('.olean')
  if (base/rel).is_file() or (pkg/rel).is_file():return
  cand=sources.get(n.split('.')[-1],[])
  if len(cand)!=1:bad.append({'module':n,'candidates':[str(x) for x in cand]});return
  p=cand[0];imports=[]
  for line in p.read_text().splitlines():
   if line.startswith('import '):imports.extend(line[7:].split())
  for x in imports:go(x)
  out.append({'module':n,'source':str(p),'source_sha256':h(p),'imports':imports})
 for t in targets:go(t)
 if bad:raise ValueError(bad)
 return out
for side in ('author','peer'):
 if scan(freej/side/'lib',['DiophantineConsistency.ArithmeticHalfBinomialCompat'])!=scan(freej/'author/lib',['DiophantineConsistency.ArithmeticHalfBinomialCompat']):raise ValueError('freej closure differs')
 if scan(succ/side/'lib',['DiophantineConsistency.FreeJPowerFinish'])!=scan(succ/'author/lib',['DiophantineConsistency.FreeJPowerFinish']):raise ValueError('successor closure differs')
a=freej/'author/lib';b=freej/'peer/lib';filesA={p.relative_to(a):p for p in a.rglob('*.olean')};filesB={p.relative_to(b):p for p in b.rglob('*.olean')}
if filesA.keys()!=filesB.keys():raise ValueError('inherited path sets differ')
rows=[]
for rel in sorted(filesA):
 ha,hb=h(filesA[rel]),h(filesB[rel])
 if ha!=hb:raise ValueError(('inherited object differs',str(rel)))
 rows.append({'module_path':str(rel),'sha256':ha,'author_resolved_path':str(filesA[rel].resolve()),'peer_resolved_path':str(filesB[rel].resolve())})
audit=root/'reviews/ordinary12-freej-power-finish-independent-audit/CHECK.json';ah=h(audit)
review=json.loads(audit.read_text())
if ah!='1f0357d7cb23f09fe6079e5ee744f7cf8cab6bd06d96b6e80b3167fbc9c86d7b' or review.get('status')!='PASS_INDEPENDENT_FREEJ_POWER_FINISH_AUDIT' or review.get('recorded_outer_exit')!=0:raise ValueError('power audit mismatch')
seed={}
for side in ('author','peer'):
 p=freej/side/'FreeJPowerFinish.olean'; digest=h(p);row=next(x for x in review['runs'] if x['side']==side)
 if digest!=row['object_sha256']:raise ValueError(('power seed drift',side))
 seed[side]={'path':str(p),'sha256':digest}

result={'status':'PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD','freej_power_provider_audit':str(audit),'freej_power_provider_audit_sha256':ah,'freej_power_seed':seed,'freej_base_object_count':len(rows),'freej_base_objects':rows,'preferred_rebuild':scan(a,['DiophantineConsistency.ArithmeticHalfBinomialCompat']),'alternative_rebuild':scan(succ/'author/lib',['DiophantineConsistency.FreeJPowerFinish']),'qualifications':'Source-declared import scan and current-byte observation only; no compilation, complete package/dynamic ancestry, simultaneous freeze, or internal PRA proof.'}
print(json.dumps(result,indent=2,sort_keys=True))
