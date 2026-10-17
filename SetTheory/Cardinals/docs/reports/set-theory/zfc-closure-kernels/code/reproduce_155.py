"""Recover batch155 offline and replay selected functional suites on scratch copies.

--prepare-only (the default) recovers all five packages. --run42,43,44,45,46|all
selects finite checks. --extended adds source43's eight-gap/affine/100M run and
source45's transport/control jobs. Other optional searches and source42 Lean
commands are recorded in the source dossiers. No Coq or Lean runs by default.
Bulk manifest checks are omitted in memory; functional assertions remain.
"""
from __future__ import annotations
import argparse,ast,io,json,os,runpy,subprocess,sys,tempfile,time
from pathlib import Path
from zipfile import ZipFile

ARRIVAL='fab89c5d26b81cd2ccab2ee5d213ff23725c7726'
PACKAGES={
 42:('proveit_zfc252_research_2026-10-17.zip','zfc_finite_closure_20261017'),
 43:('zfc_consistency_research_2026-10-17.zip','zfc_consistency_research_2026-10-17'),
 44:('zfc_finite_closure_2026-10-17.zip','zfc_finite_closure'),
 45:('zfc_fused_transport.zip','zfc_fused_transport'),
 46:('zfc_research_2026-10-17.zip','zfc_research_2026-10-17')}

def worker(kind,package,argv):
    helper=str(Path(__file__).resolve())
    if kind=='42':
        path=package/'verify.py';sys.path.insert(0,str(package))
        g=runpy.run_path(str(path),run_name='intake_verify')
        def sources():
            a=package/'provenance/inherited_bridge/coq/tm/Prog254.v'
            b=package/'machine/vendor/busy-beaver/ZF/m254/coq/tm/Prog254.v'
            assert a.read_bytes()==b.read_bytes()
            return dict(bulk_provenance_manifests='skipped by intake',decoder_source_identical_to_machine_package=True)
        original=g['command']
        def command(cmd,cwd=None):
            if len(cmd)>1 and cmd[1]==str(package/'machine/code/reproduce.py'):
                return original([sys.executable,helper,'_worker','42-machine',str(package),*cmd[2:]],cwd)
            return original(cmd,cwd)
        g['main'].__globals__['source_checks']=sources;g['main'].__globals__['command']=command
        sys.argv=[str(path),*argv];return g['main']()
    if kind in {'45','46'}:
        adapter=Path(__file__).with_name('reproduce_155_transport.py' if kind=='45' else 'reproduce_155_borrowed.py')
        sys.argv=[str(adapter),str(package),*argv]
        return runpy.run_path(str(adapter),run_name='__main__')
    path=package/({'42-machine':'machine/code/reproduce.py','43':'code/reproduce.py','46':'code/verify_all.py'}[kind])
    sys.path.insert(0,str(path.parent));tree=ast.parse(path.read_text(),filename=str(path))
    if kind=='42-machine':
        class Skip(ast.NodeTransformer):
            matches=0
            def visit_For(self,node):
                if isinstance(node.iter,ast.Subscript) and isinstance(node.iter.value,ast.Name) and node.iter.value.id=='manifest':
                    self.matches+=1;return ast.copy_location(ast.Pass(),node)
                return self.generic_visit(node)
        adapter=Skip();tree=adapter.visit(tree)
        if adapter.matches!=1:raise ValueError('Unexpected source42 manifest loop')
    else:
        name='identities' if kind=='43' else 'integrity';matches=0
        for node in tree.body:
            if isinstance(node,ast.FunctionDef) and node.name==name:
                matches+=1;node.body=ast.parse("return None").body
        if matches!=1:raise ValueError('Unexpected manifest function')
    sys.argv=[str(path),*argv]
    exec(compile(ast.fix_missing_locations(tree),str(path),'exec'),{'__name__':'__main__','__file__':str(path)})

def main():
    if not __debug__:raise SystemExit('Keep Python assertions enabled.')
    sys.dont_write_bytecode=True
    if len(sys.argv)>1 and sys.argv[1]=='_worker':
        return worker(sys.argv[2],Path(sys.argv[3]).resolve(),sys.argv[4:])
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path);p.add_argument('--output',type=Path)
    p.add_argument('--prepare-only',action='store_true');p.add_argument('--run',default='')
    p.add_argument('--extended',action='store_true');a=p.parse_args()
    repo=a.repo.resolve() if a.repo else next(x for x in Path(__file__).resolve().parents if (x/'.git').exists())
    try:selected=set(PACKAGES) if a.run=='all' else {int(x) for x in a.run.split(',') if x}
    except ValueError:p.error('--run expects42,43,44,45,46 or all')
    if selected-PACKAGES.keys() or (a.prepare_only and selected):p.error('Select42–46 or prepare-only')
    work=a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-batch155-reproduce-'))
    if work.is_relative_to(repo) or (work.exists() and any(work.iterdir())):p.error('Use new/empty scratch outside checkout')
    work.mkdir(parents=True,exist_ok=True);packages={}
    for n,(archive,wrapper) in PACKAGES.items():
        raw=subprocess.check_output(['git','show',f'{ARRIVAL}:docs/incoming/{archive}'],cwd=repo)
        dest=work/str(n)
        with ZipFile(io.BytesIO(raw)) as z:
            for item in z.infolist():
                if not (dest/item.filename).resolve().is_relative_to(dest.resolve()) or ((item.external_attr>>16)&0o170000)==0o120000:raise ValueError('Unsafe member')
            z.extractall(dest)
        packages[n]=dest/wrapper
        if not packages[n].is_dir():raise ValueError('Unexpected wrapper')
    record=dict(batch=155,arrival=ARRIVAL,packages={str(k):str(v) for k,v in packages.items()},scratch=str(work),checks=[],scope='Finite recovery/replay, not a full consistency-machine certificate',bulk_manifest_checks='omitted in memory',Coq_built=False,Lean_built=False)
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
    for n in sorted(selected):
        package=packages[n];args=[]
        if n==42:args=['--output',str(work/'source42.json')]
        if n==43:args=['--output',str(work/'source43-results')]+(['--full','--long-run'] if a.extended else [])
        if n==44:args=['--output',str(work/'source44.json')]
        if n==45:args=['--extended'] if a.extended else []
        if n==46:args=['--output',str(work/'source46.json')]
        cmd=[sys.executable,'-B',str(package/'code/verify_release.py'),*args] if n==44 else [sys.executable,'-B',str(Path(__file__).resolve()),'_worker',str(n),str(package),*args]
        start=time.monotonic();log=work/f'source{n}.log'
        with log.open('w') as f:r=subprocess.run(cmd,cwd=package,env=env,stdout=f,stderr=subprocess.STDOUT)
        record['checks'].append(dict(source=n,command=cmd,returncode=r.returncode,seconds=time.monotonic()-start,log=str(log)))
        (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n');print(n,'exit',r.returncode,flush=True)
        if r.returncode:raise SystemExit(f'Failed: {log}')
    record['status']='PASS';(work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    print(work,flush=True)

if __name__=='__main__':main()
