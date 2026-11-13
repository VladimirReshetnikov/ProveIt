#!/usr/bin/env python3
"""Point-in-time source/import closure for graph-derived symbolic radix."""
import hashlib,json,os,subprocess
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];BASE=ROOT/'research/ordinary12-ipra-bridge'
PREFIX=Path('/tmp/ipra-compact-fixed-graph-digits-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
AUDIT=ROOT/'reviews/compact44-fixed-graph-independent-audit/CHECK.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
if H(AUDIT)!='3d380723c818d4f16dc78e5c942b5e3cab8f7a01cf8a5bfad47ad3af3941abc1':raise ValueError('parent audit drift')
check=json.loads(AUDIT.read_text())
if check.get('status')!='PASS_INDEPENDENT_COMPACT44_FIXED_GRAPH_DIGITS_AUDIT' or check.get('recorded_outer_exit')!=0:raise ValueError('invalid fixed graph audit')
sources={}
for loc in (ROOT/'Lean/DiophantineConsistency',BASE):
 for p in loc.rglob('*.lean'):sources.setdefault(p.stem,[]).append(p)
selected={k:BASE/v for k,v in {
 'FreeJPowerCancel':'free-j-power-cancel-prototype/FreeJPowerCancel.lean',
 'FreeJRadixAlignment':'free-j-radix-align-prototype/FreeJRadixAlignment.lean',
 'CompactGraphDerivedRadix':'compact44-graph-derived-radix-prototype/CompactGraphDerivedRadix.lean'}.items()}
def scan(lib):
 seen=set();order=[]
 def go(name):
  if name in seen:return
  seen.add(name);rel=Path(*name.split('.')).with_suffix('.olean')
  if (lib/rel).is_file():return
  if not name.startswith('DiophantineConsistency.') and (PACKAGE/rel).is_file():return
  stem=name.split('.')[-1];matches=[selected[stem]] if stem in selected else sources.get(stem,[])
  if len(matches)!=1 or not matches[0].is_file():raise ValueError(('missing or ambiguous source',name,[str(p) for p in matches]))
  p=matches[0];imports=[v for line in p.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()]
  for v in imports:go(v)
  order.append({'module':name,'source':str(p),'source_sha256':H(p),'imports':imports})
 go('DiophantineConsistency.CompactGraphDerivedRadix')
 return order
a=PREFIX/'author/lib';b=PREFIX/'peer/lib';aa={p.relative_to(a):p for p in a.rglob('*.olean')};bb={p.relative_to(b):p for p in b.rglob('*.olean')}
if aa.keys()!=bb.keys():raise ValueError('provider object sets differ')
objects=[]
for rel in sorted(aa):
 h=H(aa[rel])
 if H(bb[rel])!=h:raise ValueError(('provider object drift',str(rel)))
 objects.append({'module_path':str(rel),'sha256':h,'author_resolved_path':str(aa[rel].resolve()),'peer_resolved_path':str(bb[rel].resolve())})
x,y=scan(a),scan(b)
if x!=y:raise ValueError('side closure differs')
expected_sources={
 'FreeJPowerCancel':'8bf1b748ebe2486089d5af53dd2c6cc83744e6f8e371e364eb0e9aa2ee97ced8',
 'FreeJRadixAlignment':'5def0e56555cdac09d101f59b61c470220c3c14ea9e858bf288e258c43d90f56',
 'CompactGraphDerivedRadix':'b25f3d22b9bf5a6c67825eabfba264b3f395248a3af3ed9418793d142afbb153'}
if {r['module'].split('.')[-1]:r['source_sha256'] for r in x}!=expected_sources:raise ValueError('unexpected closure or selected source drift')
prior={
 'FreeJPowerCancel':('ordinary12-freej-power-cancel-independent-audit','3ca8ec87488143974e542c82edc6d2a544c1f0bc4b55fe18fec2fb5dd3601a01','PASS_INDEPENDENT_FREEJ_POWER_CANCEL_AUDIT'),
 'FreeJRadixAlignment':('ordinary12-freej-radix-align-independent-audit','d05bf1383612a124b5b119dbdd6902823ebb69bb577282f1c1c842d2e02a9f53','PASS_INDEPENDENT_FREEJ_RADIX_ALIGN_AUDIT')}
for stem,(directory,digest,status) in prior.items():
 audit=ROOT/'reviews'/directory/'CHECK.json'
 if H(audit)!=digest:raise ValueError(('prior audit drift',stem))
 receipt=json.loads(audit.read_text())
 if receipt.get('status')!=status or receipt.get('recorded_outer_exit')!=0:raise ValueError(('invalid prior audit',stem))
 repo=Path(subprocess.run(['git','rev-parse','--show-toplevel'],cwd=ROOT,check=True,capture_output=True,text=True).stdout.strip())
 path=selected[stem].relative_to(repo).as_posix()
 blob=subprocess.run(['git','show',receipt['source_commit']+':'+path],cwd=repo,check=True,capture_output=True).stdout
 if hashlib.sha256(blob).hexdigest()!=expected_sources[stem]:raise ValueError(('audited source mismatch',stem))

choices={k:{'selected':str(p),'selected_sha256':H(p),'all_candidates':[{'path':str(q),'sha256':H(q)} for q in sorted(sources.get(k,[]))]} for k,p in selected.items()}
result={'status':'PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD','parent_audit_path':str(AUDIT),'parent_audit_sha256':H(AUDIT),'prior_audits':{k:{'directory':v[0],'sha256':v[1]} for k,v in prior.items()},'inherited_objects':objects,'explicit_choices':choices,'modules':x,'scope':'Point-in-time source/import and object scan; no simultaneous freeze, paired build, retained-port calibration, checker, machine or PRA proof.'}
print(json.dumps(result,indent=2,sort_keys=True))
