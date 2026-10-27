"""Read-only planning audit: authenticate the narrow graph imports only.
No compiler, project Python import, object copy, or source mutation.
Later wide counts are module-name inventories, explicitly not authentication.
"""
from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
DC=ROOT/'Computability/DiophantineConsistency'
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(r):
 x=pin(r['path']);assert x['sha256']==r['sha256'],r['path'];return x
def imports(p):
 s=Path(p).read_text();o=[];i=0;d=0
 while i<len(s):
  a=s[i:i+2]
  if d:
   if a=='/-':d+=1;i+=2
   elif a=='-/':d-=1;i+=2
   else:o.append('\n' if s[i]=='\n' else ' ');i+=1
  elif a=='/-':d=1;o.append(' ');i+=2
  elif a=='--':
   while i<len(s) and s[i]!='\n':i+=1
  else:o.append(s[i]);i+=1
 assert d==0
 return list(dict.fromkeys(['Init']+[n for l in re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(o),re.M) for n in l.split()]))
parent=Path('/tmp/native-adaptive-source-restoration-j5s7732x/inputs.json')
rp=DC/'reviews/native-adaptive-source-restoration-root-replay/ROOT.json'
up=DC/'reviews/native-adaptive-unit-factors-peer-replay.json'
sp=DC/'reviews/native-shifted-source-adapter-root-replay/ROOT.json'
op=DC/'reviews/native-ordinary-source-construction-root-replay/ROOT.json'
base=json.loads(parent.read_text());rest=json.loads(rp.read_text());units=json.loads(up.read_text())
assert rest['status']==units['status']=='PASS'
selected=list(base['selected_custom'])
for packet,name in [(rest,'DiophantineConsistency.NativeAdaptiveSourceRestoration'),(units,'DiophantineConsistency.NativeAdaptiveUnitFactors')]:
 r=next(x for x in packet['records'] if x['module']==name)
 assert r['exit_code']==0
 selected.append(dict(module=name,source=r['source'],object=r['object'],actual_imports=imports(r['source']['path'])))
observations=[]
for r in selected:
 observations += [check(r[k]) for k in ['source','object']]
 assert imports(r['source']['path'])==r['actual_imports']
external=base['external_boundary']
for r in external:
 observations.append(check(r['source']))
 observations += [check(x) for x in r['artifacts']]
mods={r['module']:r for r in selected};edges={r['module'] for r in external};seen=set();bounds=set()
def walk(n):
 if n not in mods:bounds.add(n);return
 if n in seen:return
 seen.add(n)
 for q in mods[n]['actual_imports']:walk(q)
for n in ['DiophantineConsistency.NativeAdaptiveSourceRestoration','DiophantineConsistency.NativeAdaptiveUnitFactors']:walk(n)
assert seen==set(mods) and bounds==edges
assert len(mods)==35 and len(external)==22
wide=json.loads(sp.read_text());ordinary=json.loads(op.read_text())
def mains(p):
 return {r['module'] for r in p['selected_custom']} | {r['module'] for r in p['completed'] if not r['module'].endswith('Checks')}
narrow=set(mods);wn=mains(wide);on=mains(ordinary)
sources=['Carrier66','Carrier66Source','Carrier65Witness','NativePellFirstIndex','NativeAdaptivePowerProjection','NativeOrdinarySourceConstruction','NativeShiftedSourceAdapter','NativeSourceMask','CurrentCarrierArithmetic2011','CurrentPositiveZero2011','CurrentWindowCarry2011','CurrentMaskData2011','CurrentKernel2011','SplitCertificate59']
pins=[pin(DC/'Lean/DiophantineConsistency'/f'{n}.lean') for n in sources]
pins += [pin(DC/'candidates/free-j-polarized-positive/source/positive'/n) for n in ['p13_free_J.json','PROOF.md']]
result=dict(status='READ_ONLY_NARROW_AUTHENTICATED',scope='Only the 35-module narrow graph dependency closure is authenticated. Wider module-name unions are inventories, not source/object replays or authorization to build.',
 providers=[pin(p) for p in [parent,rp,up]],compiler=check(base['compiler']),
 selected_custom=selected,external_boundary=external,observations=observations,
 counts=dict(custom=len(selected),external=len(external),companions=sum(len(r['artifacts']) for r in external),observations=len(observations)),
 wider_inventory_only=dict(ordinary_provider=pin(op),canonical_provider=pin(sp),
   ordinary_existing_union=len(narrow|on),canonical_existing_union=len(narrow|wn),
   ordinary_new_adaptive_modules=sorted(narrow-on),canonical_new_adaptive_modules=sorted(narrow-wn),
   note='Future new Graph/Canonical leaves are not included in these existing-module counts. All selected wide source/object/boundary pins must be reauthenticated before compilation.'),
 additional_source_pins=pins,audit_script=pin(__file__))
out=DC/'research/adaptive-graph-converse2011-cache-plan.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(counts=result['counts'],ordinary_existing_union=len(narrow|on),canonical_existing_union=len(narrow|wn),output=pin(out)),indent=2))
