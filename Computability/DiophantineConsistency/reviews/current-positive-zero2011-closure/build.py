#!/usr/bin/env python3
"""PROPOSED driver. Execute only after ROOT reads/approves this exact file.

Reuse authenticated closed machine/Bridge objects; rebuild all other custom
imports serially into a new private directory. Never install project objects.
"""
from pathlib import Path
import argparse
import fcntl
import json
import os
import re
import shutil
import subprocess
import time

from plan import imports, require, sha

HERE = Path(__file__).resolve().parent
EXPECTED_REPORTS = {
    'packingData', 'not_conZFC_positive_zero', 'positive_zero_iff_not_conZFC',
    'no_positive_zero_iff_conZFC', 'no_thirteen_positive_zero_iff_conZFC',
    'not_conZFC_simultaneous_thirteen_zero'}

def save(path, data):
    tmp = path.with_suffix('.tmp')
    tmp.write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')
    tmp.replace(path)

def verify(record):
    require(Path(record['path']).is_file(), 'Missing pinned file: '+record['path'])
    require(sha(record['path']) == record['sha256'], 'Hash drift: '+record['path'])

def object_path(lib, module):
    return lib.joinpath(*module.split('.')).with_suffix('.olean')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--run-dir', required=True)
    args = parser.parse_args()
    manifest_path = HERE/'manifest.json'
    require(sha(manifest_path) == args.manifest_sha256, 'Manifest differs from reviewed hash')
    m = json.loads(manifest_path.read_text())
    require(m['status'] == 'PLAN_ONLY_NOT_EXECUTED', 'Unexpected manifest scope')
    verify(m['planner'])  # The imported source parser is also byte-pinned.
    root = Path(m['root'])
    work = Path(args.run_dir).resolve()
    require(work.parent == Path('/tmp') and work.name.startswith('current-positive-zero2011-closure-'),
            'Use a dedicated /tmp/current-positive-zero2011-closure-* directory')
    require(not work.exists(), 'Run directory exists; inspect it, never silently restart')
    require(shutil.disk_usage('/tmp').free > m['summary']['fresh_observed_primary_bytes'] + 512*2**20,
            'Insufficient free disk for observed object estimate plus 512 MiB reserve')
    work.mkdir()
    lock = (work/'lock').open('w')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    lib = work/'lib'; lib.mkdir()
    (work/'logs').mkdir()
    # Remove the shared project path completely, not merely prepend an overlay.
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(lib)] + m['external_lean_path'])
    env.pop('LEAN_SRC_PATH', None)
    lean = next(r['path'] for r in m['toolchain'] if r['path'].endswith('/bin/lean'))
    state_path = work/'state.json'
    state = {'status': 'VALIDATING', 'driver_pid': os.getpid(), 'started_unix': time.time(),
        'source_snapshot': m['head'], 'manifest_sha256': sha(manifest_path),
        'driver_sha256': sha(Path(__file__)), 'planner_sha256': sha(HERE/'plan.py'),
        'lean_path': env['LEAN_PATH'], 'completed': [], 'active': None}
    save(state_path, state)
    records = {x['module']: x for x in m['modules']}
    done = {}
    try:
        subprocess.run(['git','merge-base','--is-ancestor',m['head'],'HEAD'],cwd=root,check=True)
        for r in m['toolchain'] + m['evidence_files']: verify(r)
        boundary = {x['module']: x['object'] for x in m['external_boundary']}
        boundary_extra = [r for x in m['external_boundary'] for r in
                          x['companions'] + ([x['observed_source']] if x['observed_source'] else [])]
        for r in list(boundary.values())+boundary_extra: verify(r)
        seen = set()
        for x in m['modules']:
            verify(x['source'])
            require(imports(Path(x['source']['path'])) == x['imports'], 'Import graph drift')
            require(all(d in seen or d in boundary for d in x['imports']), 'Invalid dependency order')
            for p in m['external_lean_path']:
                require(not object_path(Path(p),x['module']).exists(),
                        'External path shadows custom module: '+x['module'])
            if x['action'] == 'reuse':
                ev = x['evidence']
                require(x['source']['sha256'] == ev['source_sha256'], 'Cache source unbound')
                require(x['observed_shared_object']['sha256'] == ev['object_sha256'], 'Cache object unbound')
                require(not x['observed_companions'], 'Uncertified cache companions require a revised plan')
                require(all(d not in records or records[d]['action']=='reuse' for d in x['imports']),
                        'Reused module has a fresh project dependency')
                verify(x['observed_shared_object'])
            else:
                require(x['action']=='fresh', 'Unknown action')
            seen.add(x['module'])
        state['status'] = 'RUNNING'; save(state_path,state)
        for number,x in enumerate(m['modules'],1):
            name = x['module']; output = object_path(lib,name)
            output.parent.mkdir(parents=True,exist_ok=True)
            verify(x['source'])
            # Check the exact direct dependency objects selected for this command.
            for dep in x['imports']:
                verify(done[dep]['object'] if dep in done else boundary[dep])
            if x['action']=='reuse':
                verify(x['observed_shared_object'])
                output.symlink_to(x['observed_shared_object']['path'])
                result = {'module':name,'action':'authenticated_reuse'}
            else:
                require(shutil.disk_usage('/tmp').free > 256*2**20, 'Disk reserve below 256 MiB')
                log = work/'logs'/f'{number:03d}-{name}.log'
                timing = log.with_suffix('.time')
                command = ['/usr/bin/time','-f','elapsed=%e max_rss_kb=%M','-o',str(timing),
                    lean,'-M6000','-j1','-DElab.async=false','-o',str(output),x['source']['path']]
                started = time.time()
                with log.open('w') as out:
                    proc = subprocess.Popen(command,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
                    state['active']={'module':name,'pid':proc.pid,'command':command,
                                     'log':str(log),'started_unix':started}
                    save(state_path,state)
                    print(json.dumps({'event':'compile',**state['active']}),flush=True)
                    code = proc.wait()
                result = {'module':name,'action':'fresh','exit_code':code,
                    'seconds':time.time()-started,'log':str(log),'log_sha256':sha(log),
                    'timing':str(timing),'timing_sha256':sha(timing)}
                if code != 0: state['failed_command'] = result
                require(code == 0, 'Lean failed: '+name+'; inspect '+str(log))
            require(output.is_file(), 'Missing output after success: '+name)
            verify(x['source'])
            for dep in x['imports']:
                verify(done[dep]['object'] if dep in done else boundary[dep])
            result['source_sha256']=x['source']['sha256']
            result['object']={'path':str(output),'sha256':sha(output),'bytes':output.stat().st_size}
            result['companions']=[{'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
                for p in (Path(str(output)+s) for s in ('.private','.server')) if p.is_file()]
            done[name]=result; state['completed'].append(result); state['active']=None
            save(state_path,state)
            print(json.dumps({'event':'complete','number':number,'module':name,'action':result['action']}),flush=True)
        for x in m['modules']:
            verify(x['source']); verify(done[x['module']]['object'])
            for c in done[x['module']]['companions']: verify(c)
        for r in m['toolchain']+m['evidence_files']: verify(r)
        for r in list(boundary.values())+boundary_extra: verify(r)
        checks = done[m['targets'][-1]]
        text = Path(checks['log']).read_text()
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)
        require({n.rsplit('.',1)[-1] for n,_ in reports} == EXPECTED_REPORTS and len(reports)==6,
                'Unexpected endpoint axiom report set')
        for name,axioms in reports:
            require(set(re.findall(r'[A-Za-z][A-Za-z.]*',axioms)) <=
                    {'propext','Classical.choice','Quot.sound'}, 'Unexpected axiom in '+name)
        state.update(status='PASS',finished_unix=time.time(),axiom_reports=reports,
            counts=m['summary'], scope='Fresh custom modules plus closed source/object-authenticated cache modules as counted in the manifest; installed external packages remain trusted precompiled boundary.')
        save(state_path,state)
        print(json.dumps({'event':'PASS','modules':len(done),'directory':str(work)}),flush=True)
    except BaseException as exc:
        state.update(status='FAILED',finished_unix=time.time(),
                     failure={'type':type(exc).__name__,'message':str(exc)})
        save(state_path,state)
        raise

if __name__ == '__main__': main()
