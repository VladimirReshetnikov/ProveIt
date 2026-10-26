#!/usr/bin/env python3
"""Replay the seven proof replacements without modifying the source checkout.

Requires Python 3.11+, git, an installed pinned Lean compiler, and pinned packages.
The --verify-only path needs no Lean installation and writes nothing to the repo.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time
import tomllib

PACKET = Path(__file__).resolve().parents[1]
PIN = '1e2a853935a6155cbcf2aa199aaca51946c4fff9'
TARGETS = [
    'DiophantineConsistency.AnnotatedClosure',
    'DiophantineConsistency.ObjectNaturalDiscrete',
    'DiophantineConsistency.ObjectNaturalOrderedSemiring',
    'DiophantineConsistency.ObjectPairingInjective',
    'DiophantineConsistency.WangTiles942HelicalQuotientChecks',
    'DiophantineConsistency.WangTiles942SeamColumnsChecks',
    'DiophantineConsistency.WangTiles942CycleBandChecks',
    'DiophantineConsistency.WangTiles942BandMarkerChecks',
]

def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()

def run(cmd, **kwargs):
    return subprocess.run(cmd, check=True, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, **kwargs)

def resolve_lean(repo: Path, requested: str | None, env: dict[str, str]) -> str:
    # Resolve an elan proxy in the checkout, then retain the actual executable.
    # Later compilations run from several source roots and must not reselect it.
    candidate=shutil.which(requested) if requested else None
    if requested and candidate is None:
        raise SystemExit('Requested Lean executable is unavailable: '+requested)
    if candidate is None:
        elan=shutil.which('elan')
        if elan:
            try:
                candidate=run([elan,'which','lean'],cwd=repo,env=env).stdout.strip()
            except subprocess.CalledProcessError:
                pass
        if not candidate:candidate=shutil.which('lean')
    if not candidate:
        raise SystemExit('Install the pinned Lean toolchain or supply --lean /path/to/lean.')
    candidate=str(Path(candidate).resolve())
    try:
        prefix=Path(run([candidate,'--print-prefix'],cwd=repo,env=env).stdout.strip())
    except subprocess.CalledProcessError as error:
        raise SystemExit('Could not resolve the installed Lean compiler: '+error.stderr.strip())
    executable=(prefix/'bin'/('lean.exe' if os.name=='nt' else 'lean')).resolve()
    if not prefix.is_absolute() or not executable.is_file():
        raise SystemExit('Lean returned an invalid installation prefix: '+str(prefix))
    return str(executable)

def outside_checkout(path: Path, repo: Path):
    if path.is_relative_to(repo):
        raise SystemExit('Replay output must be outside the source checkout: '+str(path))

def temporary_work_directory(repo: Path) -> Path:
    # gettempdir() probes candidates with writes, so filter before any probe.
    candidates=[os.environ.get(key) for key in ('TMPDIR','TEMP','TMP')]
    candidates+=([str(Path.home()/'AppData/Local/Temp')] if os.name=='nt'
                 else ['/tmp','/var/tmp','/usr/tmp'])
    candidates.append(str(Path.cwd()))
    for candidate in dict.fromkeys(c for c in candidates if c):
        parent=Path(candidate).resolve()
        if parent.is_relative_to(repo):continue
        try:
            return Path(tempfile.mkdtemp(prefix='proveit-lean-refinements-',dir=parent))
        except OSError:
            continue
    raise SystemExit('No writable temporary directory outside the checkout; supply --work-dir.')

def strip_comments(t: str) -> str:
    out=[]; i=0; depth=0
    while i < len(t):
        if t[i:i+2]=='/-': depth+=1; out.append('  '); i+=2
        elif depth and t[i:i+2]=='-/': depth-=1; out.append('  '); i+=2
        elif depth: out.append('\n' if t[i]=='\n' else ' '); i+=1
        elif t[i:i+2]=='--':
            j=t.find('\n',i)
            if j<0: break
            out.append('\n'); i=j+1
        else: out.append(t[i]); i+=1
    return ''.join(out)

def imports(p: Path):
    return [n for line in re.findall(r'^\s*(?:(?:public|meta)\s+)?import\s+([^\n]+)',
        strip_comments(p.read_text()), re.M) for n in line.split()]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--work-dir',type=Path,help='empty output directory outside the checkout')
    parser.add_argument('--lean',help='installed Lean executable; otherwise resolve elan or PATH')
    parser.add_argument('--verify-only',action='store_true')
    args=parser.parse_args();repo=args.repo.expanduser().resolve()
    requested_work=args.work_dir.expanduser().resolve() if args.work_dir else None
    if requested_work is not None:outside_checkout(requested_work,repo)
    expected=json.loads((PACKET/'evidence/source-targets.json').read_text())
    for row in expected['files']:
        p=repo/row['path'];q=PACKET/'overlay'/row['path']
        if not p.is_file() or sha(p)!=row['before_sha256']:
            raise SystemExit('Source mismatch; rebase this patch before replay: '+str(p))
        if sha(q)!=row['after_sha256']:
            raise SystemExit('Packet overlay integrity failure: '+str(q))
    for filename in ('lean-toolchain','lake-manifest.json','lakefile.toml'):
        if sha(repo/filename)!=expected['environment_sha256'][filename]:
            raise SystemExit('Pinned environment changed: '+filename)
    run(['git','-C',str(repo),'apply','--check',str(PACKET/'patches/all-refinements.patch')])
    print('PASS: seven original sources, overlays, environment pins, and patch applicability.')
    if args.verify_only:return 0

    # Do not invoke Lake: loading its configuration can write checkout caches.
    env=dict(os.environ)
    env.pop('LEAN_PATH',None);env.pop('LEAN_SYSROOT',None)
    lean=resolve_lean(repo,args.lean,env)
    version=run([lean,'--version'],cwd=repo,env=env).stdout.strip()
    if 'version 4.32.0,' not in version:
        raise SystemExit('Expected Lean 4.32.0, received: '+version)
    manifest=json.loads((repo/'lake-manifest.json').read_text())
    packages=repo/manifest.get('packagesDir','.lake/packages'); package_paths=[]; pins={}
    for item in manifest['packages']:
        p=packages/item['name']
        rev=run(['git','-C',str(p),'rev-parse','HEAD']).stdout.strip()
        if rev!=item['rev']:raise SystemExit('Package pin mismatch: '+item['name'])
        package_paths.append(p/'.lake/build/lib/lean');pins[item['name']]=rev
    if requested_work is not None:
        work=requested_work
        work.mkdir(parents=True,exist_ok=True)
        if any(work.iterdir()):raise SystemExit('--work-dir must be empty: '+str(work))
    else:
        work=temporary_work_directory(repo)
    build=work/'build';logs=work/'logs';build.mkdir();logs.mkdir()
    env['LEAN_PATH']=os.pathsep.join(map(str,[build,*package_paths]))
    config=tomllib.loads((repo/'lakefile.toml').read_text())
    roots=[(x['name'],repo/x.get('srcDir','.')) for x in config['lean_lib']]
    found={};order=[];active=set()
    def visit(name):
        if name in found:return
        root=next((r for lib,r in roots if name==lib or name.startswith(lib+'.')),None)
        if root is None:return
        original=root/(name.replace('.','/')+'.lean')
        overlay=PACKET/'overlay'/original.relative_to(repo)
        source=overlay if overlay.exists() else original
        source_root=(PACKET/'overlay'/root.relative_to(repo)) if overlay.exists() else root
        if not source.is_file():raise FileNotFoundError(source)
        if name in active:raise RuntimeError('Import cycle: '+name)
        active.add(name)
        for dep in imports(source):visit(dep)
        active.remove(name);found[name]=(source,source_root);order.append(name)
    for target in TARGETS:visit(target)
    records={'source_reference':PIN,'lean_executable':lean,'lean_version':version,'package_pins':pins,'modules':{}}
    for name in order:
        source,root=found[name];output=build/(name.replace('.','/')+'.olean')
        output.parent.mkdir(parents=True,exist_ok=True)
        command=[lean,'-R',str(root),'-o',str(output),str(source)]
        start=time.monotonic()
        result=subprocess.run(command,env=env,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log=logs/(name+'.log');log.write_text(result.stdout)
        records['modules'][name]={'source':str(source),'source_sha256':sha(source),
            'returncode':result.returncode,'seconds':time.monotonic()-start,
            'output_sha256':sha(output) if result.returncode==0 else None,
            'dependency_olean_sha256':{d:sha(build/(d.replace('.','/')+'.olean')) for d in imports(source) if d in found}}
        (work/'replay-results.json').write_text(json.dumps(records,indent=2)+'\n')
        print(('PASS ' if result.returncode==0 else 'FAIL ')+name,flush=True)
        if result.returncode:
            print(result.stdout);return result.returncode
    audit=PACKET/'lean/CombinedAxiomAudit.lean'
    result=subprocess.run([lean,str(audit)],env=env,cwd=audit.parent,text=True,
                          stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (logs/'combined-axioms.log').write_text(result.stdout)
    if result.returncode or 'sorryAx' in result.stdout:
        print(result.stdout);raise SystemExit('Axiom audit failed.')
    expected_axioms=json.loads((PACKET/'evidence/expected-axioms.json').read_text())
    actual={name:sorted(a.strip() for a in axioms.split(',') if a.strip()) for name,axioms in
            re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",result.stdout,re.S)}
    if actual!={k:sorted(v) for k,v in expected_axioms.items()}:
        raise SystemExit('Axiom set comparison failed; see '+str(logs/'combined-axioms.log'))
    print('PASS: complete candidate closure and expected axiom sets.')
    print('Receipts: '+str(work))
    return 0

if __name__=='__main__':raise SystemExit(main())
