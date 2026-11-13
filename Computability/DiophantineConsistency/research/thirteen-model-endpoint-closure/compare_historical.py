#!/usr/bin/env python3
"""Read-only exact source/object comparison against the historical 1,210 pair."""
import hashlib
import json
import os
from pathlib import Path
import sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('reject optimized Python')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
HIST=Path('/tmp/ipra-aq29-fresh-source-closure-v2/manifest.json')
BASE=Path('/tmp/ipra-ordinary12-coexistence-source-03/manifest.json')
PAIR=Path('/tmp/ipra-aq29-fresh-project-pair')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    plan=json.loads((HERE/'source-manifest.json').read_text());base=json.loads(BASE.read_text());hist=json.loads(HIST.read_text())
    if H(HIST)!='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48' or len(hist['sources'])!=1210:raise ValueError('historical manifest drift')
    if H(BASE)!='9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded':raise ValueError('70-source base drift')
    full=dict(base['sources']);full.update(plan['sources'])
    selected=set(plan['sources']);queue=list(plan['direct_parent_boundary'])
    while queue:
        n=queue.pop()
        if n in selected:continue
        if n not in base['sources']:raise ValueError(('missing base boundary',n))
        selected.add(n)
        queue.extend(x for x in base['sources'][n]['imports'] if x in base['sources'])
    current={n:full[n] for n in selected}; old=hist['sources']; overlap=selected & set(old);missing=selected-set(old)
    for n,r in current.items():
        if H(ROOT/r['workspace_path'])!=r['sha256']:raise ValueError(('current source drift',n))
    changed={n for n in overlap if current[n]['sha256']!=old[n]['sha256']}
    different_imports={n for n in overlap if current[n]['imports']!=old[n]['imports']}
    reverse={n:set() for n in selected}
    for n,row in current.items():
        for dep in row['imports']:
            if dep in selected:reverse[dep].add(n)
    dirty=set(changed)|set(missing);todo=list(dirty)
    while todo:
        n=todo.pop()
        for m in reverse[n]-dirty:dirty.add(m);todo.append(m)
    states={s:json.loads((PAIR/s/'state.json').read_text()) for s in ('author','peer')}
    records={s:{r['module']:r for r in state['records']} for s,state in states.items()}
    if any(len(r)!=1210 for r in records.values()):raise ValueError('historical state rows')
    findings={};side_hashes={}
    for side in ('author','peer'):
        missing_files=[];object_mismatch=[];not_regular=[];hashes={}
        for n,r in records[side].items():
            obj=PAIR/side/'lib'/Path(*n.split('.')).with_suffix('.olean')
            if not obj.is_file():missing_files.append(n);continue
            if obj.is_symlink():not_regular.append(n)
            h=H(obj);hashes[n]=h
            if h!=r['object_sha256']:object_mismatch.append(n)
        findings[side]={'missing':sorted(missing_files),'symlink':sorted(not_regular),'mismatch_to_record':sorted(object_mismatch)}
        side_hashes[side]=hashes
    sibling_mismatch=sorted(n for n in set(side_hashes['author']) & set(side_hashes['peer']) if side_hashes['author'][n]!=side_hashes['peer'][n])
    result={'status':'HISTORICAL_COMPARISON_NOT_A_BUILD','source_anchor':plan['source_anchor'],
      'historical_manifest_sha256':H(HIST),'base_manifest_sha256':H(BASE),'source_survey_sha256':H(HERE/'source-manifest.json'),
      'scope':'Declared source graph and actual retained olean hashes only. No successor build, Lean replay, transitive package/dynamic audit, current axiom inventory or iPRA endpoint claimed.',
      'selected_count':len(selected),'selected_parent70_count':len(selected & set(base['sources'])),
      'historical_overlap_count':len(overlap),'new_count':len(missing),'changed_overlap_count':len(changed),
      'imports_changed_count':len(different_imports),'dirty_reverse_closure_count':len(dirty),
      'reusable_source_clean_count':len(selected-dirty),'new_modules':sorted(missing),'changed_modules':sorted(changed),
      'imports_changed_modules':sorted(different_imports),'dirty_reverse_closure':sorted(dirty),
      'all_historical_objects_checked_per_side':1210,'object_findings':findings,'sibling_object_mismatch':sibling_mismatch}
    target=HERE/'historical-comparison.json'
    if sys.argv[1:]==['--check']:
        if json.loads(target.read_text())!=result:raise ValueError('comparison mismatch')
    elif not sys.argv[1:]:
        if target.exists():raise ValueError('refusing overwrite')
        target.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:raise ValueError('use no arguments or --check')
    print('PASS_HISTORICAL_COMPARISON',len(selected),'new',len(missing),'changed',len(changed),'dirty',len(dirty),'reusable',len(selected-dirty),'object_findings',findings,'sibling_mismatch',len(sibling_mismatch))
if __name__=='__main__':main()
