"""Recover batch154 offline; run explicitly selected finite suites on scratch copies.

Default/--prepare-only only recovers all five packages. --run 37,38,39,40,41|all
runs their functional default suites. --extended also runs the advertised
bounded machine/grammar searches; --contexts regenerates source39's context
inventories. --lean explicitly supplies Lean4.32 for source38's fresh26 closure.
Bulk provenance/manifest checks are omitted in memory; all formula, table,
certificate and functional source-identity assertions remain. No Coq/network.
"""
from __future__ import annotations
import argparse, ast, io, json, os, re, subprocess, sys, tempfile, time
from pathlib import Path
from zipfile import ZipFile

PACKAGES = {
 37: ('61e77836565f63582561f54745f633d50efd9c7d', 'zfc_consistency_research_2026-10-16 (2).zip', 'zfc_consistency_research'),
 38: ('61e77836565f63582561f54745f633d50efd9c7d', 'zfc_consistency_research_20261016.zip', 'zfc_consistency_research_20261016'),
 39: ('61e77836565f63582561f54745f633d50efd9c7d', 'zfc_unary_closure_research.zip', 'zfc_unary_closure_research'),
 40: ('3d731d8cf44941560752abc625149f7bfa109930', 'zfc_finite_kernel_research.zip', 'zfc_finite_kernel_report'),
 41: ('2b10c9072e2555ebadef3466c9c3b7a1bec81778', 'zfc_cyclic_algebra_research.zip', 'zfc_cyclic_algebra'),
}


def require_lean432(executable: Path) -> str:
    result = subprocess.run([str(executable.resolve()), '--version'],
                            capture_output=True, text=True, check=True)
    version = result.stdout.strip()
    if not re.search(r'\bLean \(version 4\.32\.0(?:,|\))', version):
        raise ValueError('Expected Lean 4.32.0; compiler reports: ' + version)
    return version


def worker(kind: str, script: Path, argv: list[str]):
    sys.path.insert(0, str(script.parent))
    sys.argv = [str(script), *argv]
    tree = ast.parse(script.read_text(), filename=str(script))
    if kind == '37':
        found = set()
        for node in tree.body:
            if isinstance(node, ast.FunctionDef) and node.name in {'verify_inputs', 'verify_manifest'}:
                found.add(node.name)
                node.body = ast.parse("print('SKIP: bulk manifest/provenance loops by intake policy', flush=True)").body
        if found != {'verify_inputs', 'verify_manifest'}: raise ValueError('Unexpected source37 adapter')
    elif kind == '38':
        # Invoke all original functional run_step bodies, excluding only source_pins.
        ns = {'__name__': 'intake_verifier', '__file__': str(script)}
        exec(compile(tree, str(script), 'exec'), ns)
        checks = [ns['run_step'](*job) for job in [
            ('public253_invariant_macro_and_bootstrap', 'experiments/public253', 'check_certificate.py', 180),
            ('public253_eight_rejection_tests', 'experiments/public253', 'test_certificate.py', 180),
            ('equational_kernel_tests', 'experiments/equational', 'test_cyclic_algebra.py', 300),
            ('grammar_independent_certificates_and_corruption_controls', 'experiments/grammar', 'verify_certificates.py', 180)]]
        result = dict(bulk_manifest_checks='omitted by intake policy', checks=checks,
                      scope='All four default functional suites; no kernel build or optional search')
        (script.parent/'intake-validation.json').write_text(json.dumps(result,indent=2)+'\n')
        raise SystemExit(0 if all(c['status']=='PASS' for c in checks) else 1)
    elif kind == '38-lean':
        compiler = os.environ.get('ZFC_LEAN')
        if not compiler:
            raise ValueError('The archived build requires an explicit Lean4.32 executable')
        require_lean432(Path(compiler))
        class Omit(ast.NodeTransformer):
            matches = 0
            def visit_For(self, node):
                if ast.unparse(node.iter) == "manifest['sources']":
                    self.matches += 1
                    return ast.copy_location(ast.Pass(), node)
                return self.generic_visit(node)
            def visit_Dict(self,node):
                self.generic_visit(node)
                for i,k in enumerate(node.keys):
                    if isinstance(k,ast.Constant) and k.value=='upstream_git_blobs_verified':
                        node.values[i]=ast.Constant(0)
                return node
        adapter=Omit();tree=adapter.visit(tree)
        if adapter.matches!=1: raise ValueError('Unexpected source38 Lean manifest adapter')
    else: raise ValueError(kind)
    ast.fix_missing_locations(tree)
    exec(compile(tree, str(script), 'exec'), {'__name__': '__main__', '__file__': str(script)})


def main():
    if not __debug__: raise SystemExit('Assertions must remain enabled.')
    sys.dont_write_bytecode=True
    if len(sys.argv)>1 and sys.argv[1]=='_worker':
        return worker(sys.argv[2],Path(sys.argv[3]).resolve(),sys.argv[4:])
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path);p.add_argument('--output',type=Path)
    p.add_argument('--prepare-only',action='store_true');p.add_argument('--run',default='')
    p.add_argument('--extended',action='store_true');p.add_argument('--contexts',action='store_true')
    p.add_argument('--lean',type=Path,help='explicit pinned4.32 executable, serialized build only')
    a=p.parse_args();repo=a.repo.resolve() if a.repo else next(x for x in Path(__file__).resolve().parents if (x/'.git').exists())
    try: selected=set(PACKAGES) if a.run=='all' else {int(x) for x in a.run.split(',') if x}
    except ValueError: p.error('--run expects source numbers37–41 or all')
    if selected-PACKAGES.keys() or (a.prepare_only and (selected or a.lean)):
        p.error('Choose sources37–41; --prepare-only excludes execution')
    if a.lean and 38 not in selected:p.error('--lean requires selecting source38')
    lean_version = None
    if a.lean:
        try: lean_version = require_lean432(a.lean)
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            p.error(str(error))
    work=a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-batch154-reproduce-'))
    if work.is_relative_to(repo) or (work.exists() and any(work.iterdir())):
        p.error('Use new/empty scratch outside the checkout')
    work.mkdir(parents=True,exist_ok=True);packages={}
    for number,(arrival,archive,wrapper) in PACKAGES.items():
        data=subprocess.check_output(['git','show',f'{arrival}:docs/incoming/{archive}'],cwd=repo)
        dest=work/str(number)
        with ZipFile(io.BytesIO(data)) as z:
            for item in z.infolist():
                if not (dest/item.filename).resolve().is_relative_to(dest.resolve()) or ((item.external_attr>>16)&0o170000)==0o120000:
                    raise ValueError('Unsafe archive member')
            z.extractall(dest)
        package=dest/wrapper
        if not package.is_dir():raise ValueError('Unexpected package wrapper')
        packages[number]=package
    record=dict(packages={str(k):str(v) for k,v in packages.items()},scratch=str(work),checks=[],
                scope='Offline recovery and selected finite checks; no end-to-end consistency or state-bound certificate',
                bulk_manifest_checks='omitted by intake policy', optional_lean_version=lean_version)
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
    helper=str(Path(__file__).resolve())
    def run(number,name,args,folder=None,adapt=None):
        base=packages[number];script=base/args[0]
        command=[sys.executable,'-B',helper,'_worker',adapt,str(script),*args[1:]] if adapt else [sys.executable,'-B',str(script),*args[1:]]
        begin=time.monotonic();log=work/(name+'.log')
        with log.open('w') as f:r=subprocess.run(command,cwd=base/(folder or ''),env=env,stdout=f,stderr=subprocess.STDOUT)
        record['checks'].append(dict(name=name,command=command,returncode=r.returncode,seconds=round(time.monotonic()-begin,3),log=str(log)))
        (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n');print(name,'exit',r.returncode,flush=True)
        if r.returncode:raise SystemExit(f'{name} failed: {log}')
    if 37 in selected:run(37,'37-replay',['reproduce.py',*(['--all'] if a.extended else [])],adapt='37')
    if 38 in selected:
        run(38,'38-replay',['verify.py'],adapt='38')
        if a.extended:
            run(38,'38-regenerate',['experiments/public253/regenerate.py'])
            folder='experiments/public253/searches/'
            for name,script,table in [('edge','edge_redirect_search.py','source_zfc253.tm'),('incoming','incoming_row_search.py','source_zfc253.tm'),('shortcut','row_shortcuts.py','source_zfc253.tm'),('shortcut-incoming','incoming_row_search.py','zfc253_shortcut.tm')]:
                run(38,'38-'+name,[folder+script,str(packages[38]/'experiments/public253'/table),'--radius','6','--bound','64','--output',str(work/('38-'+name+'.json'))])
            g='experiments/grammar/'
            run(38,'38-baseline',[g+'research-inputs/Computability/BusyBeaver/Research/ZFC/layout_grammar_experiment.py','--output',str(work/'baseline'),'--start-seed','130','--seeds','1','--lanes','coarse','--exponents','4'])
            for name,steps,seed,temp,restart in [('rotation','15000','20261016','0.8','0'),('plateau','20000','281','0.08','5000')]:
                run(38,'38-'+name,[g+'grammar_rotation_search.py','--output',str(work/name),'--steps',steps,'--chains','4','--seed',seed,'--temperature',temp,'--restart-period',restart])
        if a.lean:
            env['ZFC_LEAN']=str(a.lean.resolve());run(38,'38-lean',['formal/build.py'],adapt='38-lean')
    if 39 in selected:
        run(39,'39-replay',['verify.py',*(['--search'] if a.extended else [])])
        if a.contexts:
            run(39,'39-inventory',['machine/edge_inventory.py'])
            for radius in (4,6):run(39,f'39-contexts{radius}',['machine/edge_contexts.py','--radius',str(radius)])
    if 40 in selected:
        for name,args in [('kernel',['code/finite_kernel.py']),('verify',['code/verify_kernel.py']),('reify',['code/reify.py']),('baseline34',['baselines/34-k12-theory-finite_assignment_kernel.py','--out',str(work/'baseline34')]),('machine',['engineering/audit.py'])]:run(40,'40-'+name,args)
        if a.extended:
            for radius,fuel in [(20,128),(10,32)]:run(40,f'40-search{radius}',['engineering/reproduce_search.py','--radius',str(radius),'--fuel',str(fuel)])
    if 41 in selected:run(41,'41-replay',['reproduce.py'])
    (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n');print('Evidence:',work,flush=True)

if __name__=='__main__':main()
