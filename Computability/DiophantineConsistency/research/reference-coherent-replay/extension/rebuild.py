#!/usr/bin/env python3
"""Rebuild one sibling's affected closure using authenticated isolated seeds.

This is a selective rebuild, not a second full source compilation. Parent
package-transitive and dynamic provenance and transient mutation remain
inherited. The other sibling is never used as an object provider.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import prepare

H = prepare.digest
SUFFIXES = prepare.SUFFIXES

def guard(entries):
    for name, expected in entries.items():
        path = Path(name)
        if expected is None:
            if os.path.lexists(path): raise ValueError(('new companion', name))
        elif not path.is_file() or str(path.resolve()) != expected['realpath'] or H(path) != expected['sha256']:
            raise ValueError(('changed companion', name))

def scan(stem, allow_symlink=False):
    result = {}
    for suffix in SUFFIXES:
        p = Path(str(stem)+suffix)
        if os.path.lexists(p):
            if not p.is_file() or (p.is_symlink() and not allow_symlink): raise ValueError(('bad companion', str(p)))
            result[str(p)] = {'realpath': str(p.resolve()), 'sha256': H(p)}
        else: result[str(p)] = None
    return result

def parent_check(parent, record, old, new, old_snap, new_snap):
    prepare.verify_policy(new);prepare.verify_freezer_identity(new)
    freezer_observation=Path(record['freezer_observation'])
    if H(freezer_observation)!=record['freezer_observation_sha256']:
        raise ValueError('freezer observation changed')
    prepare.check_freezer_observation(json.loads(freezer_observation.read_text()),
                                      record['new_snapshot_sha256'],new_snap,len(new['order']))
    pair_path = parent/'pair-state.json'
    if H(pair_path) != record['parent_pair_sha256']:
        raise ValueError('parent pair state changed')
    pair = json.loads(pair_path.read_text())
    observation = Path(record['parent_observation'])
    if H(observation) != record['parent_observation_sha256']:
        raise ValueError('parent observation changed')
    prepare.check_parent_observation(json.loads(observation.read_text()), record['parent_pair_sha256'], pair_path, len(old['order']))
    if pair['status'] != 'MATCHED_PASS' or pair['snapshot_sha256'] != record['old_snapshot_sha256']:
        raise ValueError('parent pair not matched to old source')
    if [(r['label'], r['exit']) for r in pair['runs']] != [('author', 0), ('peer', 0)]:
        raise ValueError('parent builder exits not zero')
    for row in pair['runs']:
        if H(row['process_log']) != row['process_log_sha256'] or H(parent/row['label']/'state.json') != row['builder_state_sha256']:
            raise ValueError(('parent process evidence drift', row['label']))
    for file, key in (('rebuild.py', 'driver_sha256'), ('compare.py', 'comparator_sha256'), ('run_pair.py', 'coordinator_sha256')):
        if H(prepare.PAIR_TOOLS/file) != pair[key]: raise ValueError(('parent driver drift', file))
    spec = importlib.util.spec_from_file_location('parent_compare', prepare.PAIR_TOOLS/'compare.py')
    compare = importlib.util.module_from_spec(spec); spec.loader.exec_module(compare)
    if compare.compare(parent/'author/state.json', parent/'peer/state.json') != pair['comparison']:
        raise ValueError('parent pair comparison changed')
    states = {label: json.loads((parent/label/'state.json').read_text()) for label in ('author','peer')}
    for label in ('author','peer'):
        if prepare.select(old, new, states[label]['records']) != record['plan']:
            raise ValueError(('project ancestry plan changed', label))
    prepare.verify_snapshot(old_snap, old, False); prepare.verify_snapshot(new_snap, new, True)
    prepare.verify_current_git(new)
    return states

def expected_seed_inventory(parent_lib, state, names):
    expected = {}
    for name in names:
        stem = parent_lib.joinpath(*name.split('.'))
        group = state['outputs'][name]
        for suffix in SUFFIXES:
            original = Path(str(stem)+suffix)
            if str(original) not in group: raise ValueError(('parent companion missing', str(original)))
            item = group[str(original)]
            if item is not None:
                expected[name.replace('.', '/')+suffix] = item['sha256']
    return expected

def reject_fallbacks(pkg, tool, tops):
    for root in (pkg, tool):
        for top in tops:
            for suffix in ('', *SUFFIXES, '.so', '.dll', '.dylib'):
                if os.path.lexists(root/(top+suffix)):
                    raise ValueError(('project fallback artifact', str(root/(top+suffix))))

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--prepared', type=Path, required=True)
    p.add_argument('--preparation-sha256', required=True)
    p.add_argument('--old-snapshot', type=Path, required=True)
    p.add_argument('--new-snapshot', type=Path, required=True)
    p.add_argument('--sibling', choices=('author','peer'), required=True)
    p.add_argument('--expected-axiom-reports', type=int, required=True)
    args = p.parse_args()
    prepared = args.prepared.resolve(strict=True); receipt = prepared/'preparation.json'
    if H(receipt) != args.preparation_sha256: raise ValueError('preparation receipt pin')
    record = json.loads(receipt.read_text())
    if record['status'] != 'PREPARED_NOT_REBUILT' or record['output'] != str(prepared):
        raise ValueError('invalid preparation')
    if H(Path(prepare.__file__)) != record['preparer_sha256']: raise ValueError('preparer changed')
    old_snap = args.old_snapshot.resolve(strict=True); new_snap = args.new_snapshot.resolve(strict=True)
    if H(old_snap/'manifest.json') != record['old_snapshot_sha256'] or H(new_snap/'manifest.json') != record['new_snapshot_sha256']:
        raise ValueError('snapshot pin mismatch')
    old = json.loads((old_snap/'manifest.json').read_text()); new = json.loads((new_snap/'manifest.json').read_text())
    parent = Path(record['parent_pair']).resolve(strict=True)
    states = parent_check(parent, record, old, new, old_snap, new_snap)
    label = args.sibling; base = prepared/label; lib = base/'lib'
    sibling = prepared/('peer' if label == 'author' else 'author')/'lib'
    if (lib.is_symlink() or sibling.is_symlink() or lib.resolve() == sibling.resolve()
            or lib.resolve().is_relative_to(parent) or sibling.resolve().is_relative_to(parent)):
        raise ValueError('project sibling isolation')
    expected = expected_seed_inventory(parent/label/'lib', states[label], record['plan']['unaffected'])
    if expected != record['seeds'][label]: raise ValueError('seed inventory disagrees with parent')
    prepare.verify_seeds(lib, expected)
    for rel in expected:
        copied = lib/rel; original = parent/label/'lib'/rel
        if (copied.stat().st_dev, copied.stat().st_ino) == (original.stat().st_dev, original.stat().st_ino):
            raise ValueError(('seed hard-linked to parent', rel))
        other = sibling/rel
        if other.is_file() and (copied.stat().st_dev, copied.stat().st_ino) == (other.stat().st_dev, other.stat().st_ino):
            raise ValueError(('seed hard-linked to sibling', rel))
    state_path = base/'rebuild-state.json'; logs = base/'rebuild-logs'
    if state_path.exists() or logs.exists(): raise ValueError('refusing to overwrite sibling rebuild')
    parent_state = states[label]
    if args.expected_axiom_reports != len(prepare.expected_names(new)):
        raise ValueError('target axiom report count differs from pinned extension manifest')
    logs.mkdir()
    provider = Path(parent_state['provider']); pr = json.loads(provider.read_text())
    pkg = Path(parent_state['package_overlay']); lean = Path(parent_state['lean_path']); tool = lean.parent.parent/'lib/lean'
    tops = {n.split('.')[0] for n in new['order']}; reject_fallbacks(pkg, tool, tops)
    env = dict(os.environ, LEAN_PATH=str(lib)+':'+str(pkg), LEAN_NUM_THREADS='1')
    for var in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'): env.pop(var, None)
    plan = record['plan']; affected = set(plan['affected']); seed_names = set(plan['unaffected'])
    if new['target'] not in affected:
        raise ValueError('target must be freshly rebuilt and checked')
    for name in affected:
        for suffix in SUFFIXES:
            if os.path.lexists(lib/(name.replace('.','/')+suffix)):
                raise ValueError(('new module companion already exists',name,suffix))
    order_index = {n:i for i,n in enumerate(new['order'])}; fresh = {}; guards = {}; rows = []
    state = {'status':'RUNNING','sibling':label,'preparation_sha256':H(receipt),
             'old_snapshot_sha256':record['old_snapshot_sha256'], 'new_snapshot_sha256':record['new_snapshot_sha256'],
             'parent_pair_sha256':record['parent_pair_sha256'], 'driver_sha256':H(Path(__file__)),
             'expected_axiom_reports':args.expected_axiom_reports,'records':rows,
             'scope':'Selective sibling rebuild from matched-parent, ancestry-verified seeds. Package-transitive, dynamic and transient-mutation ancestry remains inherited.'}
    def save():
        q=base/'rebuild-state.tmp';q.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');q.replace(state_path)
    save()
    try:
        for index, name in enumerate(new['order']):
            if name not in affected: continue
            if shutil.disk_usage(lib).free < prepare.MIN_FREE:
                raise ValueError('disk reserve exhausted during affected rebuild')
            state.update(phase='compile', module=name, index=index); save()
            source = new_snap/new['sources'][name]['snapshot_path']
            if H(source) != new['sources'][name]['sha256']: raise ValueError(('source drift',name))
            dep = subprocess.run([str(lean),'--deps',str(source)],env=env,capture_output=True,text=True)
            if dep.returncode or dep.stderr: raise ValueError(('deps failure',name,dep.returncode,dep.stderr))
            direct = {}
            for line in dep.stdout.splitlines():
                q = Path(line)
                if not q.is_absolute() or not q.is_file() or not str(q).endswith('.olean'):
                    raise ValueError(('bad dependency',name,line))
                if q.is_relative_to(lib):
                    module = str(q.relative_to(lib))[:-6].replace('/','.')
                    if module not in seed_names and module not in fresh: raise ValueError(('unavailable project dependency',name,module))
                    if module not in order_index or order_index[module] >= index: raise ValueError(('dependency order',name,module))
                    kind = 'seed' if module in seed_names else 'fresh'
                elif q.is_relative_to(pkg):
                    module = str(q.relative_to(pkg))[:-6].replace('/','.'); kind = 'package'
                    if module.split('.')[0] in tops: raise ValueError(('project fallback',name,module))
                    if module.split('.')[0]=='Foundation' and not q.resolve().is_relative_to((Path(pr['root'])/'.lake/build/lib/lean/Foundation').resolve()):
                        raise ValueError(('mixed Foundation',module))
                elif q.is_relative_to(tool):
                    module = str(q.relative_to(tool))[:-6].replace('/','.');kind = 'toolchain'
                    if module.split('.')[0] in tops or module.split('.')[0]=='Foundation': raise ValueError(('bad toolchain fallback',module))
                else: raise ValueError(('dependency outside allowed roots',line))
                if module in direct:
                    if direct[module]['path'] != str(q) or direct[module]['kind'] != kind:
                        raise ValueError(('multiple dependency providers',name,module))
                    continue
                direct[module]={'path':str(q),'kind':kind,'sha256':H(q)}
                for key, value in scan(Path(str(q)[:-6]), allow_symlink=True).items():
                    if key in guards and guards[key] != value: raise ValueError(('input drift',key))
                    guards[key] = value
            declared=set(new['sources'][name]['imports']);actual=set(direct)
            if not declared <= actual or actual-declared-{'Init'}: raise ValueError(('declared/compiler imports differ',name))
            project={d for d in declared if d in new['sources']}
            if {d for d,v in direct.items() if v['kind'] in {'seed','fresh'}} != project:
                raise ValueError(('project imports differ',name))
            guard(guards)
            obj=lib/(name.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
            for suffix in SUFFIXES:
                if os.path.lexists(lib/(name.replace('.','/')+suffix)):
                    raise ValueError(('new module companion already exists',name,suffix))
            log=logs/(f'{index:04d}-'+name.replace('.','_')+'.log')
            cmd=[str(lean),'-M8000','-j1','-DElab.async=false','--root='+str(new_snap/'src'),str(source),'-o',str(obj)]
            start=time.monotonic()
            with log.open('x') as f: process=subprocess.run(cmd,cwd=new_snap/'src',env=env,stdout=f,stderr=subprocess.STDOUT)
            text=log.read_text();matches=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
            report_names=[x[0] for x in matches];reports=[x[1] for x in matches]
            row={'module':name,'exit':process.returncode,'source_sha256':H(source),'direct_inputs':direct,
                 'log':str(log),'log_sha256':H(log),'object_sha256':H(obj) if obj.is_file() else None,
                 'axiom_reports':reports,'axiom_report_names':report_names,'seconds':round(time.monotonic()-start,3)}
            rows.append(row);save()
            if process.returncode or not obj.is_file() or re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',text):
                raise ValueError(('compilation failed',name))
            if name==new['target']:
                if report_names!=prepare.expected_names(new) or len(reports)!=args.expected_axiom_reports or any({x.strip() for x in rep.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for rep in reports):
                    raise ValueError('target axiom reports')
            if H(source)!=new['sources'][name]['sha256']: raise ValueError(('source changed',name))
            fresh[name]=scan(Path(str(obj)[:-6])); guard(guards)
            print('PASS',len(rows),len(affected),name,flush=True)
        if [r['module'] for r in rows] != plan['affected']: raise ValueError('affected row coverage')
        guard(guards)
        for item in fresh.values(): guard(item)
        for name in seed_names:
            for suffix in SUFFIXES:
                rel = name.replace('.', '/') + suffix; path = lib/rel
                if rel in expected:
                    if not path.is_file() or path.is_symlink() or H(path)!=expected[rel]:
                        raise ValueError(('seed drift',rel))
                elif os.path.lexists(path):
                    raise ValueError(('new seed companion',rel))
        inventory = set(expected)
        for group in fresh.values():
            inventory.update(str(Path(path).relative_to(lib)) for path,value in group.items() if value is not None)
        actual_inventory = set()
        for path in lib.rglob('*'):
            if path.is_symlink(): raise ValueError(('project output symlink',str(path)))
            if path.is_file(): actual_inventory.add(str(path.relative_to(lib)))
        if actual_inventory != inventory: raise ValueError('project output inventory mismatch')
        reject_fallbacks(pkg,tool,tops)
        parent_check(parent,record,old,new,old_snap,new_snap)
        if H(receipt)!=args.preparation_sha256 or H(Path(__file__))!=state['driver_sha256']:
            raise ValueError('driver or preparation changed')
        state.update(status='PASS',phase='complete',module=None,guarded_companions=guards,outputs=fresh,
                     workspace_head=prepare.verify_current_git(new));save()
        print('PASS',len(rows),'affected modules',flush=True)
    except BaseException as exc:
        state.update(status='FAILED',failure=repr(exc));save();print('FAILED',repr(exc),flush=True);raise

if __name__ == '__main__': main()
