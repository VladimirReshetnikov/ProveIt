import json, hashlib, re, subprocess
from pathlib import Path
from datetime import datetime,timezone
base=Path.cwd(); D=base/'Computability/DiophantineConsistency'; R=D/'reviews'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
refs={}; observations=0

def observe(path, sha256=None, **metadata):
    global observations
    p=str(Path(path).absolute()); actual=sha(p); observations+=1
    if sha256 is not None and actual!=sha256: raise RuntimeError(('pin mismatch',p,sha256,actual))
    if p in refs and refs[p]!=actual: raise RuntimeError(('reference conflict',p))
    refs[p]=actual
    return {'path':p,'sha256':actual}

def bundle(path):
    observe(path)
    for x in json.loads(Path(path).read_text())['files']:
        observe(Path(path).parent/x.get('path',x.get('saved','')), x['sha256'])

def load(name):
    p=R/name; ref=observe(p); s=json.loads(p.read_text())
    for k in ['inputs','result','driver','bundle_files']:observe(**s[k])
    d=json.loads(Path(s['inputs']['path']).read_text())
    for x in d['pins']:observe(**x)
    bundle(s['bundle_files']['path'])
    return ref,s,d
pa,sa,a=load('foundation-ha-zfc-validator-replay.json')
pb,sb,b=load('foundation-ha-sigma-one-gg-replay.json')
rp=R/'foundation-ha-sigma-one-gg-root-replay/ROOT.json'
pr=observe(rp,'1b078703886c29a6932bc5645b3a477d5494ab5694c4da4464067da3316e239c')
root=json.loads(rp.read_text())
for x in root['pins']:observe(**x)
bundle(rp.parent/'FILES.json')
u={m['module']:m for m in a['modules']}; alternatives=[]; added=[]
for m in b['modules']:
    if m['module'] not in u:u[m['module']]=m;added.append(m['module'])
    else:
        old=u[m['module']]
        if old['source_sha256']!=m['source_sha256']:raise RuntimeError(('source conflict',m['module']))
        if old['objects']!=m['objects']:alternatives.append({'module':m['module'],'selected':old['objects'],'alternative':m['objects'],'source_sha256':m['source_sha256']})
r=root['records'][0]; author=sb['records'][0]
for rec in [r,author]:observe(**rec['source']);observe(**rec['object'])
u[r['module']]={'module':r['module'],'source':r['source']['path'],'source_sha256':r['source']['sha256'],'objects':[r['object']],'imports':['Init']+re.findall(r'^import\s+(\S+)',Path(r['source']['path']).read_text(),re.M),'origin':'accepted root replay 39242517d6'}
alternatives.append({'module':r['module'],'selected':[r['object']],'alternative':[author['object']],'source_sha256':r['source']['sha256']})
ex={x['module']:x for x in a['external']}
for x in b['external']:
    ex.setdefault(x['module'],x)
    for z in [x.get('source'),*x['objects']]:
        if z:observe(**z)
for m in u.values():
    observe(m['source'],m['source_sha256'])
    for o in m['objects']:observe(**o)
    actual=set(re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(\S+)',Path(m['source']).read_text(),re.M))-{'Init'}
    if actual!=set(m['imports'])-{'Init'}:raise RuntimeError(('imports mismatch',m['module']))
for x in ex.values():
    if x.get('source'):observe(**x['source'])
    for o in x['objects']:observe(**o)
observe(**a['compiler'])
if a['compiler']!=b['compiler']:raise RuntimeError('compiler mismatch')
def closure(roots):
    seen=set(); external=set(); order=[]
    def visit(n):
        if n in seen or n in external:return
        if n in ex:external.add(n);return
        if n not in u:raise RuntimeError(('missing',n))
        seen.add(n)
        for i in u[n]['imports']:visit(i)
        order.append(n)
    for n in roots:visit(n)
    return {'roots':roots,'count':len(seen),'foundation_count':sum(n.startswith('Foundation.')for n in seen),'artifact_count':sum(len(u[n]['objects'])for n in seen),'external_count':len(external),'dependency_order':order,'external_modules':sorted(external)}
fixed=closure(['DiophantineConsistency.FoundationHASigmaOneGG','DiophantineConsistency.FoundationHACurrentTransfer','DiophantineConsistency.FoundationZFCConsistencyNat'])
if fixed['count']!=455 or set(fixed['dependency_order'])!=set(u):raise RuntimeError('union mismatch')
narrow=closure(['DiophantineConsistency.FoundationHASigmaOneGG','DiophantineConsistency.FoundationHACurrentTransfer'])
sigma=closure(['DiophantineConsistency.FoundationHASigmaOneGG'])
anchors=[D/'Lean/DiophantineConsistency'/f'{n}.lean' for n in ['FoundationHASigmaOneGG','FoundationHASigmaOneGGChecks','FoundationZFCConsistencyNat','FoundationHACurrentTransfer','FoundationPAHFSyntax','FoundationPAHFNatSemantics','FoundationHADeltaZero']]
anchors += [base/p for p in ['Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/Instances.lean','Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ZFDelta1.lean','Logic/Interpretability/PAHF/Lean/PAHF/PASyntax.lean']]
v=Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation')
anchors += [v/p for p in ['Foundation/FirstOrder/Incompleteness/Consistency.lean','Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean','Foundation/FirstOrder/Bootstrapping/Syntax/Theory.lean','Foundation/FirstOrder/Arithmetic/Definability/Hierarchy.lean','Foundation/FirstOrder/SetTheory/Basic/Misc.lean','Foundation/FirstOrder/SetTheory/Basic/Axioms.lean','Foundation/Syntax/Predicate/Rew.lean','Foundation/FirstOrder/NegationTranslation/GoedelGentzen.lean']]
anchor_refs=[observe(p)for p in anchors]
note=observe(D/'research/ha-fixed-consistency-normalization-proposal.md')
driver=observe(__file__)
out={'status':'READ_ONLY_PLAN_AUTHENTICATED_NO_COMPILER_RUN','checked_utc':datetime.now(timezone.utc).isoformat(),'git_snapshot':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'note':note,'audit_driver':driver,'parents':[pa,pb,pr],'source_anchors':anchor_refs,'compiler':a['compiler'],'fixed_closure':fixed,'generic_with_existing_translated_neg':narrow,'already_available_sigma_generic':sigma,'added_to_448_parent':added+[r['module']],'modules':[u[n]for n in fixed['dependency_order']],'external':[ex[n]for n in fixed['external_modules']],'same_source_alternatives':alternatives,'pin_observation_count':observations,'unique_pin_count':len(refs),'pins':[{'path':p,'sha256':h}for p,h in sorted(refs.items())],'preflight_metadata_correction':'First in-memory audit stopped before output/Lean because observe(**root-pin) did not accept prior_hash_in_selected_record. The final audit accepts ancillary metadata without changing or relaxing path/hash checks. No source or compiler failure.','scope':'Read-only source/import/object/companion/inherited-trace and external-boundary reauthentication; no Lean import, build, copy, or proof-source edit.'}
p=D/'research/ha-fixed-consistency-normalization-proposal-pins.json'
if p.exists():raise RuntimeError('refuse overwrite')
p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'note':note,'pins':{'path':str(p),'sha256':sha(p)},'counts':{k:v for k,v in fixed.items()if k not in ['dependency_order','external_modules','roots']},'observations':observations,'unique':len(refs)},indent=2))
