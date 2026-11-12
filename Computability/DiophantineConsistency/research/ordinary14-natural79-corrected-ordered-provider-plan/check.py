#!/usr/bin/env python3
"""Read-only lexical candidate order and bounded source/object observations."""
import hashlib,json,os,re,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];ROOT=D.parents[1]
OVERLAY=D/'research/ordinary14-natural79-corrected-reflection-overlay'
CUT=D/'research/ordinary14-natural79-corrected-reflection-provider-cut/observation.json'
PRIOR=D/'research/ordinary14-natural79-qualified-provider-cut/observation.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p,h):
    b=p.read_bytes();assert sha(b)==h,(str(p),sha(b));return b
inv=json.loads(pin(OVERLAY/'inventory.json','fc9da87f4178c7f3b06c549a792f7e80baac2217a6735bcb38e49b280a90d434'))
cut=json.loads(pin(CUT,'5e191072e4760cf91e97524e0d26f9805ef6a7c0b35b2b63e684222e40d5bff7'))
prior=json.loads(pin(PRIOR,'c978df77d6a2c68947f827a31e45ede8070b5b76cd26c7eab2306811d6b2610c'))
front=cut['projected_project_frontier']; external=cut['projected_external']; missing=cut['projected_source_candidates']
assert len(front)==41 and len(external)==6 and len(missing)==5 and len(inv['drafts_topological'])==196
def evidence(path):
    if not os.path.lexists(path):return None
    if not path.is_file():return {'path':str(path),'file':False,'symlink':path.is_symlink()}
    return {'path':str(path),'realpath':str(path.resolve(strict=True)),'sha256':sha(path.read_bytes()),'symlink':path.is_symlink()}
def imports(path):
    out=[]
    for line in path.read_text().splitlines():
        if not line.strip():continue
        m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
        if not m:break
        out.extend(m.group(1).split())
    return out
project_records={}
for n,row in sorted(front.items()):
    sp=D/'Lean'/(n.replace('.','/')+'.lean'); source=evidence(sp)
    obj=evidence(Path(row['object_path']))
    assert source and source['sha256']==row['source_sha256'] and obj and obj['sha256']==row['object_sha256']
    recorded=prior['selected_project_frontier'][n]
    assert source['sha256']==recorded['current_source_sha256'] and obj==recorded['object'],n
    project_records[n]={'source':source,'object':obj,'p72_snapshot_source_sha256':recorded['p72_snapshot_source_sha256'],
      'base_record_source_sha256':recorded['base_record_source_sha256'],'base_record_object_sha256':recorded['base_record_object_sha256']}
external_records={}
for n,row in sorted(external.items()):
    obj=evidence(Path(row['path']));assert row['present'] and obj and obj['sha256']==row['sha256']
    if n.startswith('Foundation.'):
        sp=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/lib/FormalizedFormalLogic-Foundation')/(n.replace('.','/')+'.lean')
    else:
        assert n.startswith('Mathlib.')
        sp=ROOT/'.lake/packages/mathlib'/(n.replace('.','/')+'.lean')
    source=evidence(sp);assert source and 'sha256' in source,n
    if n.startswith('Foundation.'):assert source==cut['foundation_source']
    external_records[n]={'source':source,'object':obj}
first=['DiophantineConsistency.DiscreteOrderedRingFacts','DiophantineConsistency.Compact44.FreeJ13',
 'DiophantineConsistency.Compact44.FreeJ13Halt','DiophantineConsistency.BFS943.Direct80IndexOne',
 'DiophantineConsistency.HAExpressionNoZeroEquiv']
assert set(first)==set(missing)
done=set(front)|set(external);stages=[]
for n in first:
    row=missing[n];source=D/row['path'];pin(source,row['sha256']);deps=imports(source)
    assert deps==row['lexical_imports'] and set(deps)<=done,(n,sorted(set(deps)-done))
    stages.append({'module':n,'kind':'qualified-source-candidate','source':row['path'],
      'source_sha256':row['sha256'],'lexical_imports':deps,'unreserved_output_name':n.replace('.','/')+'.olean'})
    done.add(n)
for row in inv['drafts_topological']:
    n=row['module'];source=OVERLAY/row['overlay_path'];assert source.is_file() and not source.is_symlink()
    pin(source,row['overlay_sha256']);deps=imports(source)
    assert [d for d in deps if '.' not in d]==row['bare_imports'] and [d for d in deps if '.' in d]==row['qualified_imports']
    assert n not in done and set(deps)<=done,(n,sorted(set(deps)-done))
    stages.append({'module':n,'kind':'bare-inert-overlay','source':str(source.relative_to(D)),
      'source_sha256':row['overlay_sha256'],'lexical_imports':deps,'unreserved_output_name':n+'.olean'})
    done.add(n)
assert len(stages)==201 and stages[-1]['module']=='Natural79Endpoint'
assert len({s['unreserved_output_name'] for s in stages})==201
scan=cut['proposed_output_collision_scan'];names=sorted(s['module'] for s in stages)
assert names==scan['names'] and len(names)==201 and len(scan['roots'])==8 and len(scan['suffixes'])==13
hits=[]
for label,root in sorted(scan['roots'].items()):
    for n in names:
        for suffix in scan['suffixes']:
            p=Path(root)/(n.replace('.','/')+suffix)
            if os.path.lexists(p):hits.append({'root':label,'module':n,'suffix':suffix,'evidence':evidence(p)})
assert hits==scan['hits']
print(json.dumps({'scope':'bounded ordered lexical source candidate and sampled source/object/slot observations; no Lean, full provider closure or build-readiness claim',
 'overlay_inventory_sha256':sha((OVERLAY/'inventory.json').read_bytes()),'provider_cut_sha256':sha(CUT.read_bytes()),
 'candidate_stages':stages,'selected_project_frontier_sources_and_objects':project_records,
 'selected_external_cut_sources_and_objects':external_records,
 'bounded_collision_scan':{'names':len(names),'roots':scan['roots'],'suffixes':scan['suffixes'],'hits':hits}},sort_keys=True,indent=2))
