#!/usr/bin/env python3
"""Independently compare two completed selective sibling rebuild states."""
import json
import os
from pathlib import Path
import re
import sys
import prepare
import rebuild

H = prepare.digest

def compare(prepared, old_snap, new_snap, preparation_sha256):
    prepared = Path(prepared).resolve(strict=True)
    old_snap = Path(old_snap).resolve(strict=True); new_snap = Path(new_snap).resolve(strict=True)
    receipt = prepared/'preparation.json'
    if H(receipt) != preparation_sha256: raise ValueError('preparation pin mismatch')
    prep = json.loads(receipt.read_text())
    if prep.get('source_basis')!='HISTORICAL_PARENT':
        raise ValueError('historical preparation basis required')
    if prep['status'] != 'PREPARED_NOT_REBUILT' or prep['output'] != str(prepared):
        raise ValueError('preparation identity')
    if H(Path(prepare.__file__)) != prep['preparer_sha256']: raise ValueError('preparer changed')
    if H(old_snap/'manifest.json') != prep['old_snapshot_sha256'] or H(new_snap/'manifest.json') != prep['new_snapshot_sha256']:
        raise ValueError('snapshot changed')
    old = json.loads((old_snap/'manifest.json').read_text()); new = json.loads((new_snap/'manifest.json').read_text())
    parent = Path(prep['parent_pair']).resolve(strict=True)
    parent_states = rebuild.parent_check(parent,prep,old,new,old_snap,new_snap)
    plan = prep['plan']; affected = set(plan['affected']); seeds = set(plan['unaffected'])
    if new['target'] not in affected: raise ValueError('target not freshly rebuilt')
    states = []
    for label in ('author','peer'):
        base = prepared/label; lib = base/'lib'; state_file = base/'rebuild-state.json'
        state = json.loads(state_file.read_text()); states.append(state)
        if state.get('source_basis')!='HISTORICAL_PARENT':
            raise ValueError(('historical sibling basis required',label))
        if (state['status'] != 'PASS' or state['sibling'] != label or state['preparation_sha256'] != preparation_sha256
                or state['old_snapshot_sha256'] != prep['old_snapshot_sha256']
                or state['new_snapshot_sha256'] != prep['new_snapshot_sha256']
                or state['parent_pair_sha256'] != prep['parent_pair_sha256']
                or state['driver_sha256'] != H(Path(rebuild.__file__))):
            raise ValueError(('sibling identity',label))
        if state['expected_axiom_reports'] != len(prepare.expected_names(new)):
            raise ValueError(('target axiom report count differs from pinned extension manifest',label))
        expected = rebuild.expected_seed_inventory(parent/label/'lib',parent_states[label],plan['unaffected'])
        if expected != prep['seeds'][label]: raise ValueError(('seed parent mismatch',label))
        if [r['module'] for r in state['records']] != plan['affected'] or set(state['outputs']) != affected:
            raise ValueError(('affected coverage',label))
        guards = state['guarded_companions']; rebuild.guard(guards)
        guard_keys={str(dep['path'])[:-6]+suffix for row in state['records']
                    for dep in row['direct_inputs'].values() for suffix in prepare.SUFFIXES}
        if set(guards)!=guard_keys:raise ValueError(('input companion coverage',label))
        expected_inventory = set(expected)
        for name in seeds:
            for suffix in prepare.SUFFIXES:
                rel = name.replace('.', '/')+suffix; p=lib/rel
                if rel in expected:
                    if not p.is_file() or p.is_symlink() or H(p)!=expected[rel]: raise ValueError(('seed changed',label,rel))
                    original = parent/label/'lib'/rel
                    if (p.stat().st_dev,p.stat().st_ino)==(original.stat().st_dev,original.stat().st_ino):
                        raise ValueError(('seed linked to parent',label,rel))
                elif os.path.lexists(p): raise ValueError(('new seed companion',label,rel))
        pkg = Path(parent_states[label]['package_overlay']); lean = Path(parent_states[label]['lean_path'])
        tool = lean.parent.parent/'lib/lean'; foundation = Path(json.loads(Path(parent_states[label]['provider']).read_text())['root'])/'.lake/build/lib/lean/Foundation'
        tops = {n.split('.')[0] for n in new['order']}; rebuild.reject_fallbacks(pkg,tool,tops)
        seen = set(); positions={name:i for i,name in enumerate(new['order'])}
        for row in state['records']:
            name=row['module']; source=new_snap/new['sources'][name]['snapshot_path']; obj=lib/(name.replace('.','/')+'.olean')
            if row['exit'] != 0 or H(source)!=new['sources'][name]['sha256'] or row['source_sha256']!=H(source):
                raise ValueError(('affected source or exit',label,name))
            if not obj.is_file() or obj.is_symlink() or H(obj)!=row['object_sha256']:
                raise ValueError(('affected object',label,name))
            outputs=state['outputs'][name];rebuild.guard(outputs)
            if set(outputs)!={str(obj)[:-6]+suffix for suffix in prepare.SUFFIXES}:
                raise ValueError(('output companion coverage',label,name))
            if outputs.get(str(obj)) is None or outputs[str(obj)]['sha256'] != row['object_sha256']:
                raise ValueError(('affected object guard',label,name))
            expected_inventory.update(str(Path(k).relative_to(lib)) for k,v in outputs.items() if v is not None)
            if H(row['log']) != row['log_sha256']: raise ValueError(('affected log drift',label,name))
            text=Path(row['log']).read_text()
            if re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',text):
                raise ValueError(('forbidden diagnostic',label,name))
            matches=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
            report_names=[x[0] for x in matches];reports=[x[1] for x in matches]
            if reports != row['axiom_reports'] or report_names != row['axiom_report_names']:
                raise ValueError(('axiom report drift',label,name))
            if name == new['target'] and (report_names != prepare.expected_names(new) or len(reports) != state['expected_axiom_reports'] or any(
                    {x.strip() for x in rep.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for rep in reports)):
                raise ValueError(('target axioms',label))
            declared=set(new['sources'][name]['imports']);actual=set(row['direct_inputs'])
            if not declared <= actual or actual-declared-{'Init'}: raise ValueError(('direct import coverage',label,name))
            for module, dep in row['direct_inputs'].items():
                q=Path(dep['path']); g=guards.get(str(q))
                if not {str(q)[:-6]+suffix for suffix in prepare.SUFFIXES} <= set(guards):
                    raise ValueError(('input companion coverage',label,name,module))
                if g is None or g['sha256']!=dep['sha256'] or H(q)!=dep['sha256']:
                    raise ValueError(('direct dependency binding',label,name,module))
                if module in new['sources']:
                    kind='seed' if module in seeds else 'fresh'
                    if (dep['kind']!=kind or q!=lib/(module.replace('.','/')+'.olean')
                            or positions[module]>=positions[name] or (kind=='fresh' and module not in seen)):
                        raise ValueError(('project dependency',label,name,module))
                else:
                    base_path={'package':pkg,'toolchain':tool}.get(dep['kind'])
                    if base_path is None or q!=base_path/(module.replace('.','/')+'.olean'):
                        raise ValueError(('external dependency',label,name,module))
                    if module.split('.')[0]=='Foundation' and (dep['kind']!='package' or not q.resolve().is_relative_to(foundation.resolve())):
                        raise ValueError(('Foundation provider',label,module))
            seen.add(name)
        actual_inventory=set()
        for p in lib.rglob('*'):
            if p.is_symlink(): raise ValueError(('project artifact symlink',label,str(p)))
            if p.is_file(): actual_inventory.add(str(p.relative_to(lib)))
        if actual_inventory != expected_inventory: raise ValueError(('project inventory',label))
    if prep['seeds']['author'] != prep['seeds']['peer']:
        raise ValueError('sibling seed mismatch')
    inventories=[]
    for label in ('author','peer'):
        lib=prepared/label/'lib'
        inventories.append({str(p.relative_to(lib)) for p in lib.rglob('*') if p.is_file()})
    if inventories[0]!=inventories[1]:raise ValueError('sibling inventories differ')
    identity=lambda p:(p.stat().st_dev,p.stat().st_ino)
    parent_inodes={identity(Path(path)) for parent_state in parent_states.values()
                   for group in parent_state['outputs'].values()
                   for path,entry in group.items() if entry is not None}
    seen_inodes={}
    for label in ('author','peer'):
        for rel in inventories[0]:
            key=identity(prepared/label/'lib'/rel)
            if key in parent_inodes:raise ValueError(('project output linked to parent',label,rel))
            if key in seen_inodes:raise ValueError(('sibling hardlink or duplicate project inode',label,rel,seen_inodes[key]))
            seen_inodes[key]=(label,rel)
    a,b=states
    if a['expected_axiom_reports']!=b['expected_axiom_reports']: raise ValueError('axiom counts differ')
    for x,y in zip(a['records'],b['records']):
        for key in ('module','exit','source_sha256','log_sha256','object_sha256','axiom_reports','axiom_report_names'):
            if x[key]!=y[key]: raise ValueError(('row mismatch',x['module'],key))
        if {k:(v['kind'],v['sha256']) for k,v in x['direct_inputs'].items()} != {k:(v['kind'],v['sha256']) for k,v in y['direct_inputs'].items()}:
            raise ValueError(('direct dependency mismatch',x['module']))
        name=x['module'];stem=name.replace('.','/')
        def companions(state,label):
            group=state['outputs'][name];lib=prepared/label/'lib'
            return {suffix:(None if group[str(lib/(stem+suffix))] is None else
                            group[str(lib/(stem+suffix))]['sha256']) for suffix in prepare.SUFFIXES}
        if companions(a,'author')!=companions(b,'peer'):
            raise ValueError(('fresh companion mismatch',name))
    rebuild.parent_check(parent,prep,old,new,old_snap,new_snap)
    return {'status':'MATCHED_SELECTIVE_PASS','preparation_sha256':preparation_sha256,
            'affected_modules':len(plan['affected']),'seed_modules':len(plan['unaffected']),
            'author_state_sha256':H(prepared/'author/rebuild-state.json'),
            'peer_state_sha256':H(prepared/'peer/rebuild-state.json'),
            'source_basis':'HISTORICAL_PARENT',
            'scope':'Two selective rebuilds from separately copied historical parent seeds and separately committed additions. This is not a current-source result. Package-transitive, dynamic and transient-mutation ancestry remains inherited.'}

if __name__=='__main__':
    if len(sys.argv)!=5: raise SystemExit('usage: compare.py prepared old-snapshot new-snapshot preparation-sha256')
    print(json.dumps(compare(*sys.argv[1:]),indent=2,sort_keys=True))
