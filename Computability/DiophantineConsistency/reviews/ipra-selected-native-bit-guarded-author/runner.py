#!/usr/bin/env python3
"""Guarded, explicitly author-only extension; never an independently matched replay."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
PARENT = Path('/tmp/ipra-aq29-fresh-project-pair/author')
PARENT_STATE_SHA = 'b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'
AUDIT = ROOT / 'Computability/DiophantineConsistency/reviews/fresh-project-author-independent-audit/receipt.json'
AUDIT_SHA = 'd21db65b29de29614976a3f32e42a1f44d8ddad60b30e5894abb473cfb5e9bcf'
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
LIMIT = 8 * 1024 * 1024
START = time.monotonic()
READ = 0

def digest(path):
    global READ
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        while block := f.read(1024 * 1024):
            h.update(block); READ += len(block)
            delay = READ / LIMIT - (time.monotonic() - START)
            if delay > 0: time.sleep(delay)
    return h.hexdigest()

def require(condition, message):
    if not condition: raise ValueError(message)

def check_guard(entries):
    for name, expected in entries.items():
        p = Path(name)
        if expected is None:
            require(not os.path.lexists(p), ('unexpected companion', name))
        else:
            require(p.is_file() and str(p.resolve()) == expected['realpath'] and
                    digest(p) == expected['sha256'], ('changed companion', name))

def scan(stem):
    result = {}
    for suffix in SUFFIXES:
        p = Path(str(stem)+suffix)
        if os.path.lexists(p):
            require(p.is_file() and not p.is_symlink() and p.stat().st_nlink == 1,
                    ('bad new companion', str(p)))
            result[str(p)] = {'realpath':str(p.resolve()), 'sha256':digest(p)}
        else: result[str(p)] = None
    return result

def guard_external(path, parent_guard):
    require(str(path).endswith('.olean'), ('not an olean',str(path)))
    stem=str(path)[:-6]
    keys=[stem+s for s in SUFFIXES]
    require(all(k in parent_guard for k in keys),('external absent from parent audit',str(path)))
    require(parent_guard[str(path)] is not None, ('external olean absent from parent audit',str(path)))
    check_guard({k:parent_guard[k] for k in keys})

def reject_fallbacks(bases, tops):
    for base in bases:
        for top in tops:
            for suffix in ('',*SUFFIXES,'.so','.dll','.dylib'):
                require(not os.path.lexists(base/(top+suffix)),('project fallback namespace',str(base/(top+suffix))))

def reject_parent_shadow(records, names):
    require(not any(dep in names for record in records for dep in record['direct_inputs']),
            'addition shadows a recorded parent dependency')

def protected_output(out, protected):
    require(out.is_absolute(), 'output must be absolute')
    # Resolve existing ancestors too: symlinks may not move the new output into
    # a parent, peer, source snapshot, provider, repository, or their ancestors.
    resolved=out.resolve(strict=False)
    for item in protected:
        p=Path(item).resolve(strict=False)
        require(not resolved.is_relative_to(p) and not p.is_relative_to(resolved),
                ('output overlaps protected input',str(resolved),str(p)))
    return resolved

def safe_source(root, relative):
    p = Path(relative)
    require(not p.is_absolute() and '..' not in p.parts and p.parts and
            not any(ord(ch)<32 for ch in relative), ('unsafe source', relative))
    q = root
    for part in p.parts:
        q = q / part
        require(not q.is_symlink(), ('symlink source', str(q)))
    require(q.is_file() and q.resolve().is_relative_to(root), ('missing source', relative))
    return q

def verify_additions(spec, root):
    names, rows = spec['order'], spec['sources']
    require(spec['status'] == 'FROZEN_ADDITIONS' and len(set(names)) == len(names) and
            set(names) == set(rows) and names, 'invalid additions coverage')
    require(re.fullmatch('[0-9a-f]{40}', spec['source_commit']) is not None, 'invalid commit')
    subprocess.run(['git','cat-file','-e',spec['source_commit']+'^{commit}'], cwd=root, check=True)
    paths = set()
    for name in names:
        row = rows[name]; p = safe_source(root, row['workspace_path'])
        require(MODULE.fullmatch(name) is not None and row['workspace_path'] not in paths,
                ('invalid module or duplicate source', name))
        paths.add(row['workspace_path'])
        entry=subprocess.run(['git','ls-tree','-z',spec['source_commit'],'--',row['workspace_path']],
                             cwd=root,check=True,capture_output=True).stdout
        head,sep,path=entry.partition(b'\t')
        require(sep and path==row['workspace_path'].encode()+b'\0' and
                head.split(b' ')[:2] in ([b'100644',b'blob'],[b'100755',b'blob']),
                ('source is not a regular tracked blob',name))
        blob = subprocess.run(['git','show',spec['source_commit']+':'+row['workspace_path']],
                              cwd=root, check=True, capture_output=True).stdout
        require(hashlib.sha256(blob).hexdigest() == row['sha256'] == digest(p),
                ('source differs from pinned Git blob', name))
        declared = re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',
                              blob.decode(), re.MULTILINE)
        require(len(declared) == len(set(declared)) and set(declared) == set(row['imports']),
                ('declared imports changed', name))
    reports=spec['axiom_reports']
    require(isinstance(reports,dict) and reports and set(reports) <= set(names), 'checks outside additions')
    for module, declarations in reports.items():
        require(isinstance(declarations,list) and declarations and len(set(declarations))==len(declarations) and
                all(isinstance(n,str) and MODULE.fullmatch(n) for n in declarations),('bad report policy',module))
    return names, rows

def verify_parent(state, audit):
    require(digest(PARENT/'state.json') == PARENT_STATE_SHA == audit['author_state_sha256'],
            'parent state identity changed')
    require(digest(AUDIT) == AUDIT_SHA and audit['status'] == 'PASS_INDEPENDENT_AUTHOR_ARTIFACT_AUDIT',
            'author audit identity changed')
    require(state['status'] == 'PASS' and len(state['records']) == 1210 and
            state['manifest_sha256'] == audit['manifest_sha256'] and
            state['provider_receipt_sha256'] == audit['foundation_provider_receipt_sha256'],
            'author state not audited PASS')
    snap = Path(state['snapshot']).resolve(strict=True); provider = Path(state['provider'])
    foundation_input = Path(state['foundation_input_path'])
    require(digest(snap/'manifest.json') == state['manifest_sha256'] and
            digest(provider) == state['provider_receipt_sha256'] and
            digest(foundation_input) == state['foundation_input_sha256'], 'parent inputs changed')
    pm = json.loads((snap/'manifest.json').read_text()); pr = json.loads(provider.read_text())
    require([r['module'] for r in state['records']] == pm['order'] and
            set(state['outputs']) == set(pm['order']), 'parent coverage changed')
    for name, record in zip(pm['order'],state['records']):
        row = pm['sources'][name]; p = snap/row['snapshot_path']
        require(p == snap/'src'/(name.replace('.','/')+'.lean') and
                p.resolve().is_relative_to(snap/'src') and p.is_file() and not p.is_symlink() and
                digest(p) == row['sha256'] == record['source_sha256'] and record['exit'] == 0 and
                digest(record['log']) == record['log_sha256'], ('parent source/log changed', name))
    for guard in state['outputs'].values(): check_guard(guard)
    check_guard(state['guarded_companions']); check_guard(pr['declared_external_guard'])
    foundation = Path(pr['root'])/'.lake/build/lib/lean/Foundation'
    actual = {str(p.relative_to(foundation)) for p in foundation.rglob('*') if p.is_file() or p.is_symlink()}
    require(actual == set(pr['foundation_artifacts']), 'Foundation inventory changed')
    for rel, sha in pr['foundation_artifacts'].items():
        p = foundation/rel
        require(p.is_file() and not p.is_symlink() and digest(p) == sha, ('Foundation changed', rel))
    lean = Path(state['lean_path']); require(digest(lean) == state['lean_sha256'], 'Lean changed')
    return pm, pr

def run():
    ap = argparse.ArgumentParser(); ap.add_argument('--manifest',type=Path,required=True)
    ap.add_argument('--manifest-sha256',required=True); ap.add_argument('--output',type=Path,required=True)
    args = ap.parse_args(); manifest = args.manifest.resolve(strict=True)
    require(digest(manifest) == args.manifest_sha256, 'additions manifest hash mismatch')
    spec = json.loads(manifest.read_text()); names, rows = verify_additions(spec, ROOT)
    state = json.loads((PARENT/'state.json').read_text()); audit = json.loads(AUDIT.read_text())
    provider=json.loads(Path(state['provider']).read_text())
    out = protected_output(args.output, [ROOT,PARENT.parent,state['snapshot'],provider['root'],
                                        state['package_overlay'],Path(state['lean_path']).parent.parent,manifest])
    require(out.parent.is_dir(), 'output parent directory must exist')
    require(shutil.disk_usage(out.parent).free >= 4*1024**3, 'insufficient free disk')
    out.mkdir(parents=True, exist_ok=False)
    src, lib, logs = out/'src', out/'lib', out/'logs'
    for p in (src,lib,logs): p.mkdir()
    result = {'status':'RUNNING','manifest_sha256':args.manifest_sha256,'parent_state_sha256':PARENT_STATE_SHA,
              'author_audit_sha256':AUDIT_SHA,'driver_sha256':digest(Path(__file__)),'rows':[],
              'scope':'Author-only historical project extension; no peer match, current-source claim, package-transitive or dynamic provenance.'}
    def save():
        q=out/'state.tmp'; q.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n'); q.replace(out/'state.json')
    save()
    try:
        pm, pr = verify_parent(state,audit); parent_names=set(pm['order']); known=set(parent_names)
        tops={n.split('.')[0] for n in pm['order']}
        require(all(n.split('.')[0] in tops for n in names), 'new project namespace')
        require(not parent_names.intersection(names),'addition shadows parent project module')
        reject_parent_shadow(state['records'],set(names))
        for name in names:
            require(all(d not in names or d in known for d in rows[name]['imports']),('not topological',name))
            known.add(name)
        overlay_guard={}
        for name in pm['order']:
            for original, entry in state['outputs'][name].items():
                p=Path(original); rel=p.relative_to(PARENT/'lib'); dest=lib/rel; dest.parent.mkdir(parents=True,exist_ok=True)
                require(not os.path.lexists(dest),('overlay collision',str(dest)))
                if entry is None: overlay_guard[str(dest)]=None
                else:
                    dest.symlink_to(p)
                    overlay_guard[str(dest)]={'realpath':str(p.resolve()),'sha256':entry['sha256']}
        for name in names:
            dest=src.joinpath(*name.split('.')).with_suffix('.lean'); dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(safe_source(ROOT,rows[name]['workspace_path']),dest)
            require(digest(dest)==rows[name]['sha256'],('copy mismatch',name))
        pkg=Path(state['package_overlay']); lean=Path(state['lean_path']); tool=lean.parent.parent/'lib/lean'
        reject_fallbacks((pkg,tool),tops)
        env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(pkg),LEAN_NUM_THREADS='1')
        for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'): env.pop(key,None)
        built=set(); new_guards={}
        for idx,name in enumerate(names):
            source=src.joinpath(*name.split('.')).with_suffix('.lean'); row=rows[name]
            require(not source.is_symlink() and digest(source)==row['sha256'], ('new source changed before',name))
            dep=subprocess.run([str(lean),'--deps',str(source)],cwd=src,env=env,capture_output=True,text=True)
            require(dep.returncode==0 and not dep.stderr,('lean --deps failed',name,dep.stderr))
            observed={}
            for line in dep.stdout.splitlines():
                p=Path(line); require(p.is_absolute() and p.is_file(),('missing direct import',name,line))
                if p.is_relative_to(lib):
                    mod=str(p.relative_to(lib))[:-6].replace('/','.')
                    require(mod in parent_names or mod in built,('unknown project input',name,mod))
                    if mod in parent_names:
                        expected=(PARENT/'lib'/p.relative_to(lib)).resolve()
                        require(p.is_symlink() and p.resolve()==expected,('mixed parent object',mod))
                    else: require(not p.is_symlink(),('linked new object',mod))
                elif p.is_relative_to(pkg):
                    mod=str(p.relative_to(pkg))[:-6].replace('/','.')
                    guard_external(p,state['guarded_companions'])
                elif p.is_relative_to(tool):
                    mod=str(p.relative_to(tool))[:-6].replace('/','.')
                    guard_external(p,state['guarded_companions'])
                else: raise ValueError(('outside input root',name,line))
                item={'path':str(p),'sha256':digest(p),'realpath':str(p.resolve())}
                require(mod not in observed or observed[mod]==item,('conflicting direct import',mod))
                observed[mod]=item
            require(set(row['imports']) <= set(observed) and set(observed)-set(row['imports']) <= {'Init'},
                    ('direct imports differ',name,sorted(observed),row['imports']))
            obj=lib.joinpath(*name.split('.')).with_suffix('.olean'); obj.parent.mkdir(parents=True,exist_ok=True)
            for suffix in SUFFIXES:
                require(not os.path.lexists(Path(str(obj)[:-6]+suffix)),('new companion exists',name,suffix))
            log=logs/(f'{idx:03d}-'+name.replace('.','_')+'.log')
            with log.open('x') as f:
                p=subprocess.run([str(lean),'-M8000','-j1','-DElab.async=false','--root='+str(src),
                                  str(source),'-o',str(obj)],cwd=src,env=env,stdout=f,stderr=subprocess.STDOUT)
            text=log.read_text(); reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
            rec={'module':name,'exit':p.returncode,'source_sha256':digest(source),'log_sha256':digest(log),
                 'object_sha256':digest(obj) if obj.is_file() else None,'imports':observed,'axiom_reports':reports}
            result['rows'].append(rec);save()
            require(p.returncode==0 and obj.is_file() and not obj.is_symlink() and
                    not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',text),('Lean failure',name))
            require([x[0] for x in reports]==spec['axiom_reports'].get(name,[]),('axiom report names',name,reports))
            for _, report in reports:
                require(not ({x.strip() for x in report.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}),('axioms',name,report))
            for item in observed.values():
                q=Path(item['path']);require(q.is_file() and str(q.resolve())==item['realpath'] and digest(q)==item['sha256'],('direct drift',name,str(q)))
            require(not source.is_symlink() and digest(source)==row['sha256'], ('new source changed after',name))
            new_guards[name]=scan(Path(str(obj)[:-6]))
            built.add(name);print('PASS',idx+1,len(names),name,flush=True)
        verify_additions(spec,ROOT);verify_parent(state,audit)
        reject_fallbacks((pkg,tool),tops)
        require(digest(manifest)==args.manifest_sha256 and digest(Path(__file__))==result['driver_sha256'], 'driver/manifest drift')
        check_guard(overlay_guard)
        for guard in new_guards.values(): check_guard(guard)
        actual={str(p) for p in lib.rglob('*') if p.is_file() or p.is_symlink()}
        expected={p for p,v in overlay_guard.items() if v is not None}
        expected.update(p for guard in new_guards.values() for p,v in guard.items() if v is not None)
        require(actual == expected, 'overlay file inventory changed')
        actual_sources={str(p) for p in src.rglob('*') if p.is_file() or p.is_symlink()}
        expected_sources={str(src.joinpath(*n.split('.')).with_suffix('.lean')) for n in names}
        require(actual_sources==expected_sources, 'new source inventory changed')
        for idx,row in enumerate(result['rows']):
            source=src.joinpath(*row['module'].split('.')).with_suffix('.lean')
            log=logs/(f'{idx:03d}-'+row['module'].replace('.','_')+'.log')
            require(not source.is_symlink() and digest(source)==row['source_sha256']==rows[row['module']]['sha256'] and
                    digest(log)==row['log_sha256'],('new source/log changed',row['module']))
        result.update(status='AUTHOR_ONLY_PASS',overlay_guards=overlay_guard,new_output_guards=new_guards)
        save();print('AUTHOR_ONLY_PASS',len(names),flush=True)
    except BaseException as e:
        result.update(status='FAILED',failure=repr(e));save();raise

if __name__=='__main__': run()
