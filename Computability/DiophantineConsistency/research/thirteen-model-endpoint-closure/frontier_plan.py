#!/usr/bin/env python3
"""Compute and audit a candidate historical-object successor frontier; no Lean runs."""
import hashlib
import json
import os
import sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('reject optimized Python')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
PAIR=Path('/tmp/ipra-aq29-fresh-project-pair')
BASE=Path('/tmp/ipra-ordinary12-coexistence-source-03/manifest.json')
HIST=Path('/tmp/ipra-aq29-fresh-source-closure-v2/manifest.json')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')

def main():
    survey=json.loads((HERE/'source-manifest.json').read_text());comparison=json.loads((HERE/'historical-comparison.json').read_text())
    base=json.loads(BASE.read_text());hist=json.loads(HIST.read_text())
    if H(HIST)!=comparison['historical_manifest_sha256'] or H(BASE)!=comparison['base_manifest_sha256'] or H(HERE/'source-manifest.json')!=comparison['source_survey_sha256']:
        raise ValueError('comparison input drift')
    allrows=dict(base['sources']);allrows.update(survey['sources'])
    selected=set(survey['sources']);todo=list(survey['direct_parent_boundary'])
    while todo:
        n=todo.pop()
        if n in selected:continue
        if n not in base['sources']:raise ValueError(('missing parent',n))
        selected.add(n);todo.extend(x for x in base['sources'][n]['imports'] if x in base['sources'])
    dirty=set(comparison['dirty_reverse_closure']);clean=selected-dirty
    if len(selected)!=1145 or len(dirty)!=338 or len(clean)!=807:raise ValueError('unexpected frontier size')
    order=[n for n in base['order'] if n in selected]+[n for n in survey['order'] if n in selected]
    if len(order)!=len(selected) or len(set(order))!=len(selected):raise ValueError('order coverage')
    positions={n:i for i,n in enumerate(order)}
    for n in order:
        for dep in allrows[n]['imports']:
            if dep in selected and positions[dep]>=positions[n]:raise ValueError(('not topological',n,dep))
            if n in clean and dep in dirty:raise ValueError(('dirty dependency of clean seed',n,dep))
    states={s:json.loads((PAIR/s/'state.json').read_text()) for s in ('author','peer')}
    records={s:{r['module']:r for r in state['records']} for s,state in states.items()}
    if any(len(rs)!=1210 for rs in records.values()):raise ValueError('historical record count')
    checks={};all_guards={};fixed_external={}
    for side in ('author','peer'):
        state=states[side];guards=state['guarded_companions'];checked={};boundary={}
        for n in sorted(clean):
            r=records[side][n];row=allrows[n];old=hist['sources'][n]
            if H(ROOT/row['workspace_path'])!=row['sha256'] or row['sha256']!=old['sha256'] or r['source_sha256']!=row['sha256'] or r['exit']!=0:
                raise ValueError(('unclean seed source',side,n))
            obj=PAIR/side/'lib'/Path(*n.split('.')).with_suffix('.olean')
            if not obj.is_file() or obj.is_symlink() or H(obj)!=r['object_sha256']:raise ValueError(('seed object drift',side,n))
            expected_outputs={str(obj)[:-len('.olean')]+suffix for suffix in SUFFIXES}
            if set(state['outputs'][n])!=expected_outputs:raise ValueError(('seed output coverage',side,n))
            for key,val in state['outputs'][n].items():
                path=Path(key)
                if val is None:
                    if os.path.lexists(path):raise ValueError(('unexpected seed output companion',side,key))
                elif not path.is_file() or str(path.resolve())!=val['realpath'] or H(path)!=val['sha256']:
                    raise ValueError(('seed output companion drift',side,key))
                checked[key]=val
            observed=set(r['direct_inputs']);declared=set(row['imports'])
            if not declared<=observed or observed-declared-{'Init'}:raise ValueError(('direct import coverage',side,n))
            for dep,item in r['direct_inputs'].items():
                q=Path(item['path']);entry=guards.get(str(q))
                if entry is None or entry['sha256']!=item['sha256'] or not q.is_file() or H(q)!=item['sha256']:
                    raise ValueError(('direct dependency drift',side,n,dep))
                if dep in selected:
                    expected=PAIR/side/'lib'/Path(*dep.split('.')).with_suffix('.olean')
                    if dep not in clean or item['kind']!='project' or q!=expected:
                        raise ValueError(('project dependency not reusable',side,n,dep))
                else:
                    if item['kind'] not in ('package','toolchain'):raise ValueError(('unselected project dependency',side,n,dep))
                    boundary[dep]={'kind':item['kind'],'path':str(q),'sha256':item['sha256']}
                stem=str(q)[:-len('.olean')]
                if not str(q).endswith('.olean'):raise ValueError(('non-olean direct dependency',str(q)))
                for suffix in SUFFIXES:
                    key=stem+suffix
                    if key not in guards:raise ValueError(('missing recorded companion guard',side,key))
                    val=guards[key];path=Path(key)
                    if val is None:
                        if os.path.lexists(path):raise ValueError(('unexpected companion',side,key))
                    elif not path.is_file() or str(path.resolve())!=val['realpath'] or H(path)!=val['sha256']:
                        raise ValueError(('companion drift',side,key))
                    checked[key]=val
        checks[side]={'seed_count':len(clean),'direct_and_output_guard_count':len(checked),'external_direct_modules':len(boundary)}
        all_guards[side]=checked;fixed_external[side]=boundary
    if {n:(x['kind'],x['sha256']) for n,x in fixed_external['author'].items()}!={n:(x['kind'],x['sha256']) for n,x in fixed_external['peer'].items()}:
        raise ValueError('sibling external direct boundaries differ')
    # All source-declared external imports needed by the 338 rebuilds,
    # including direct package/toolchain object companions.
    external={};package=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
    tool=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
    for n in dirty:
        for dep in ['Init',*allrows[n]['imports']]:
            if dep in selected:continue
            if dep in allrows:raise ValueError(('unselected project source',n,dep))
            if dep in external:continue
            rel=Path(*dep.split('.')).with_suffix('.olean');q=package/rel;kind='package'
            if not q.is_file():q=tool/rel;kind='toolchain'
            if not q.is_file():raise ValueError(('missing rebuild external',n,dep))
            stem=str(q)[:-len('.olean')];companions={}
            for suffix in SUFFIXES:
                path=Path(stem+suffix)
                if os.path.lexists(path):
                    if not path.is_file():raise ValueError(('invalid rebuild external companion',str(path)))
                    companions[str(path)]={'realpath':str(path.resolve()),'sha256':H(path)}
                else:companions[str(path)]=None
            external[dep]={'kind':kind,'path':str(q),'sha256':H(q),'companions':companions}
    secs=[records['author'][n]['seconds'] for n in dirty if n in records['author']]
    result={'status':'CANDIDATE_FRONTIER_PLAN_NOT_A_BUILD','source_anchor':survey['source_anchor'],
      'comparison_sha256':H(HERE/'historical-comparison.json'),'source_survey_sha256':H(HERE/'source-manifest.json'),
      'historical_manifest_sha256':H(HIST),'base_manifest_sha256':H(BASE),
      'selected':len(selected),'reusable_seed_count':len(clean),'rebuild_count':len(dirty),
      'rebuild_order':[n for n in order if n in dirty],'reusable_seeds':[n for n in order if n in clean],
      'all_selected_source_hashes':{n:allrows[n]['sha256'] for n in order},
      'checks':checks,'direct_and_seed_output_guards':all_guards,'direct_external':fixed_external,'rebuild_external_guards':external,
      'historical_changed_rebuild_modules_with_timings':len(secs),'historical_author_seconds_for_those_modules':sum(secs),
      'scope':'Candidate source-declared topological successor plan and point-in-time direct input, reusable-output and rebuild-external companion authentication, not a builder or Lean replay. Recheck all guards before and after any build; mutations between checks, package-transitive/dynamic ancestry, complete final axiom inventory and Foundation outer-wrapper exit remain outside scope.'}
    dest=HERE/'frontier-plan.json'
    if sys.argv[1:]==['--check']:
        if json.loads(dest.read_text())!=result:raise ValueError('frontier plan mismatch')
    elif not sys.argv[1:]:
        if dest.exists():raise ValueError('refusing overwrite')
        dest.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    else:raise ValueError('use no arguments or --check')
    print('PASS_CANDIDATE_FRONTIER',len(dirty),'reuse',len(clean),'guards',checks,'historical_author_seconds',round(sum(secs),1))
if __name__=='__main__':main()
