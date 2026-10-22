#!/usr/bin/env python3
"""Fresh, sequential replay of the shared-prefix K215 runtime proof.

Use --repo only with the pinned checkout; every borrowed source is checked
against its expected hash. Without --repo all proof inputs are bundled.
No compiled object is reused from the repository or delivered evidence.
"""
from pathlib import Path
import argparse, fcntl, hashlib, json, os, re, shutil, subprocess, sys, time

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',required=True,help='Path to Lean 4.32.0 executable')
    p.add_argument('--repo',type=Path,help='Optional pinned ProveIt checkout')
    p.add_argument('--out',type=Path,required=True,help='A new, nonexistent output directory')
    p.add_argument('--scope',choices=['bridge','sites'],default='sites')
    args=p.parse_args()
    packet=Path(__file__).resolve().parent
    manifest=json.loads((packet/'sources.json').read_text())
    out=args.out.resolve()
    if out.exists(): p.error('--out must not already exist; no stale proof objects are reused')
    lean=Path(args.lean).resolve(strict=True)
    version=subprocess.check_output([str(lean),'--version'],text=True).strip()
    if 'version 4.32.0' not in version:
        p.error('This packet is pinned to Lean 4.32.0; received '+version)
    selected=manifest['scopes'][args.scope]
    modules={x['module']:x for x in manifest['modules']}
    # Validate all selected bytes before authoring the fresh build tree.
    inputs={}
    for name in selected:
        row=modules[name]
        source=packet/'src'/row['path']
        if args.repo and row.get('current_repository_path'):
            source=args.repo/row['current_repository_path']
        if sha(source)!=row['sha256']:
            raise SystemExit('Source hash mismatch: '+str(source))
        inputs[name]=source
    out.mkdir(parents=True)
    src=out/'src'; objects=out/'objects'; logs=out/'logs'
    logs.mkdir()
    for name in selected:
        dst=src/modules[name]['path']; dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(inputs[name],dst)
    env=os.environ.copy(); env['LEAN_PATH']=str(objects)
    results=[]
    toolchain={'version':version,'binary_sha256':sha(lean),'binary':str(lean)}
    for relative in ['../lib/lean/Init.olean','../lib/lean/libleanshared.so']:
        path=(lean.parent/relative).resolve()
        if path.exists():toolchain[relative]={'sha256':sha(path),'path':str(path)}
    (out/'toolchain.json').write_text(json.dumps(toolchain,indent=2)+'\n')
    for name in selected:
        row=modules[name]; source=src/row['path']
        obj=objects/Path(row['path']).with_suffix('.olean')
        obj.parent.mkdir(parents=True,exist_ok=True)
        command=[str(lean),'-o',str(obj),str(source)]
        dep_objects={}
        for dep in row['imports']:
            if dep.startswith('BusyBeaver.'):
                dp=objects/(dep.replace('.','/')+'.olean')
                if not dp.exists(): raise SystemExit('Missing prior object: '+str(dp))
                dep_objects[dep]=sha(dp)
        started=time.monotonic()
        with Path('/tmp/proveit-k215-proof-build.lock').open('a+') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            acquired=time.monotonic()
            run=subprocess.run(command,cwd=src,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            finished=time.monotonic()
        text=run.stdout.decode(errors='replace')
        log=logs/(name+'.log');log.write_bytes(run.stdout)
        record={'module':name,'source_sha256':sha(source),'direct_dependency_objects':dep_objects,
                'returncode':run.returncode,'compiler_seconds':finished-acquired,
                'lock_wait_seconds':acquired-started,'command':command,'log_sha256':sha(log)}
        if obj.exists():record['object_sha256']=sha(obj)
        results.append(record)
        (out/'records.json').write_text(json.dumps(results,indent=2)+'\n')
        print(name, 'PASS' if run.returncode==0 else 'FAIL',f'{finished-acquired:.2f}s',flush=True)
        if run.returncode:
            print(text)
            return run.returncode
        if 'sorryAx' in text: raise SystemExit('Rejected sorryAx in successful compiler output')
    reports='\n'.join((logs/(name+'.log')).read_text() for name in selected)
    expected=['KResidual215.checkFrom_contract','KResidual215.walk_contract',
              'KResidual215.covered_of_residual']
    if args.scope=='sites':
        expected += ['KResidualSites215.all_sites','KResidualSites215.covered',
                     'KResidualSites215.halts_iff','KResidualAudit.concrete_counts',
                     'KResidualAudit.old_simulation_api','KResidualAudit.residual_simulation_api',
                     'KResidualAudit.rejects_empty']
    for name in expected:
        full='SetTheory.BusyBeaver.ZFC.'+name
        if not re.search(re.escape(full)+r"' (?:depends on axioms:|does not depend on any axioms)",reports):
            raise SystemExit('Missing named axiom report: '+full)
    axioms=set()
    for block in re.findall(r'depends on axioms: \[(.*?)\]',reports,re.S):
        axioms.update(word.strip() for word in block.split(',') if word.strip())
    allowed={'propext','Classical.choice','Quot.sound'}
    if not axioms.issubset(allowed):raise SystemExit('Unexpected printed axioms: '+repr(axioms-allowed))
    summary={'status':'PASS','scope':args.scope,'fresh_modules':len(selected),
             'printed_axiom_union':sorted(axioms),'complete_ZFC_endpoint_rebuilt':False}
    (out/'result.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    return 0

if __name__=='__main__':sys.exit(main())
