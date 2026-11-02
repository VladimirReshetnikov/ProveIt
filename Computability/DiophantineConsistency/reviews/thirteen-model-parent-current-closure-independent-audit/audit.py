#!/usr/bin/env python3
"""Independently inspect the lakefile-aware source-declared closure survey."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-parent-current-closure'
PARENT=Path('/tmp/ipra-ordinary12-coexistence-source-03')
PHASH='9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def git(*args):return subprocess.run(['git',*args],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout

def main():
    for name in ('README.md','audit_plan.py','source-manifest.json'):
        p=PKG/name;need(hashlib.sha256(git('show','e18501cbd4:'+p.relative_to(ROOT).as_posix())).hexdigest()==sha(p),'committed bytes '+name)
    plan=PKG/'audit_plan.py'
    normal=subprocess.run([sys.executable,'-I',str(plan)],capture_output=True,text=True,timeout=180)
    need(normal.returncode==0 and not normal.stderr and normal.stdout.strip()=='PASS_SOURCE_DECLARED_CLOSURE 44 parent-boundary 8 missing-external []','normal survey')
    opt=subprocess.run([sys.executable,'-I','-O',str(plan)],capture_output=True,text=True,timeout=60)
    need(opt.returncode==1 and 'closure survey rejects optimized Python' in opt.stderr,'optimized refusal')
    m=json.loads((PKG/'source-manifest.json').read_bytes());anchor=m['source_anchor']
    need(anchor=='ee7380b19d9c3a9d917795b271244dd15c04de33' and m['status']=='SOURCE_DECLARED_INCREMENTAL_CLOSURE_SURVEY','anchor/status')
    need(subprocess.run(['git','merge-base','--is-ancestor',anchor,'HEAD'],cwd=ROOT).returncode==0,'anchor ancestry')
    lake=ROOT/'lakefile.toml';tool=ROOT/'lean-toolchain'
    need(sha(lake)==m['lakefile_sha256'] and sha(tool)==m['lean_toolchain_sha256'] and
         lake.read_bytes()==git('show',anchor+':lakefile.toml') and tool.read_bytes()==git('show',anchor+':lean-toolchain'),'workspace configuration')
    libs={e['name']:e.get('srcDir','.') for e in tomllib.loads(lake.read_text())['lean_lib']}
    for lib in ('DiophantineConsistency','FirstOrder','PAHF','Foundation'):need(lib in libs,'library '+lib)
    need(not (ROOT/libs['Foundation']/'Foundation').exists(),'Foundation local absence')
    pm=PARENT/'manifest.json';need(sha(pm)==m['parent_manifest_sha256']==PHASH,'parent manifest')
    frozen=json.loads(pm.read_bytes());bound=frozen['sources']
    need(frozen['status']=='FROZEN_NOT_COMPILED' and len(bound)==70 and set(bound)==set(frozen['order']),'frozen source boundary')
    for name,row in bound.items():
        w=ROOT/row['workspace_path'];snap=PARENT/row['snapshot_path']
        need(sha(w)==sha(snap)==row['sha256']==hashlib.sha256(git('show',anchor+':'+row['workspace_path'])).hexdigest(),'frozen source '+name)
    rows=m['sources'];order=m['order'];need(len(rows)==len(order)==44 and len(set(order))==44 and set(rows)==set(order),'44 module inventory')
    position={name:i for i,name in enumerate(order)};parents=set();externals=set();edges={}
    for name in order:
        row=rows[name];top=name.split('.')[0];need(top in libs and top!='Foundation','project classification '+name)
        expected=(ROOT/libs[top]/Path(*name.split('.'))).with_suffix('.lean')
        need(expected==ROOT/row['workspace_path'] and sha(expected)==row['sha256']==hashlib.sha256(git('show',anchor+':'+row['workspace_path'])).hexdigest(),'mapped pinned source '+name)
        declarations=[]
        for line in expected.read_text().splitlines():
            # Encountering an unrecognized import form fails rather than silently skipping it.
            if re.match(r'^\s*(?:(?:public|private)\s+)?import\b',line):
                hit=re.fullmatch(r'import\s+([A-Za-z0-9_.]+)(?:\s*--.*)?\s*',line)
                need(hit is not None,'unsupported source import '+name+': '+line)
                declarations.append(hit.group(1))
        need(declarations==row['imports'],'declared imports '+name)
        edges[name]=[]
        for dep in declarations:
            if dep in bound:parents.add(dep)
            elif dep in rows:
                need(position[dep]<position[name],'topology '+dep);edges[name].append(dep)
            else:
                need(dep in m['external_direct'] and (dep.startswith('Foundation.') or dep.split('.')[0] not in libs),'external classification '+dep)
                externals.add(dep)
    need(sorted(parents)==m['direct_parent_boundary'] and len(parents)==8 and externals==set(m['external_direct']) and len(externals)==8,'direct boundary')
    for name,e in m['external_direct'].items():need(e['sha256'] is not None and sha(e['path'])==e['sha256'],'external object '+name)
    roots=m['roots'];need(roots==['DiophantineConsistency.ArithmeticWindowZero','DiophantineConsistency.ArithmeticRankForcing2011'],'roots')
    reached=set();todo=list(roots)
    while todo:
        n=todo.pop()
        if n not in reached:reached.add(n);todo.extend(edges[n])
    need(reached==set(order),'source closure reachability')
    other=[x for x in order if not x.startswith('DiophantineConsistency.')]
    need(set(other)=={'FirstOrder.Fol','FirstOrder.Calculus','FirstOrder.Completeness','PAHF.AckermannHFCore','PAHF.PACore'},'other local libraries')
    print(json.dumps({'status':'PASS_INDEPENDENT_SOURCE_CLOSURE_AUDIT','source_commit':'e18501cbd4',
      'source_anchor':anchor,'author_survey_normal_exit':0,'author_survey_optimized_exit':1,
      'additional_source_modules':44,'frozen_parent_sources':70,'direct_parent_modules':8,'direct_external_objects':8,
      'non_diophantine_project_modules':other,'scope':'Source-declared closure and point-in-time external hashes only; no Lean build, --deps, companion, transitive package or dynamic-load audit.'},indent=2))

if __name__=='__main__':main()
