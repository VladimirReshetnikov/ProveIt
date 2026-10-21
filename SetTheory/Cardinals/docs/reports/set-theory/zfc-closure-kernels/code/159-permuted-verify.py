#!/usr/bin/env python3
"""Offline reproduction. --runtime freshly derives all 6,176 primary cases.

The default verifies the finite construction, inherited logical certificate,
complete source control graph, literal blank prefixes, and stored case inventory.
It does not present stored receipts as a fresh universal runtime derivation.
Add --secondary-runtime to regenerate the second 216-state variant as well.
"""
from pathlib import Path
import argparse, gzip, hashlib, importlib.util, json, shutil, subprocess, sys, tempfile, zipfile

ROOT=Path(__file__).resolve().parent
K217='K217_Dominated_Continuation_2026-10-20'
K218='K218_Dominated_Rho8_2026-10-20'
PARENT_SHA='4aa33f0c4844043d243fb7d01ef316d4b72de641864e5317525f7cfac7f5c809'
GRANDPARENT_SHA='080b4fe855c109ab77588c01c9e012d9572afa7721682306370ccb2eb22cbea9'

def need(ok,msg):
    if not ok:raise ValueError(msg)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def readz(p):return json.loads(gzip.decompress(p.read_bytes()))

def run(args,work,logname,cwd=None):
    with (work/logname).open('w') as log:
        p=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=cwd,stdout=log,stderr=subprocess.STDOUT)
    if p.returncode:
        print((work/logname).read_text()[-9000:])
        raise RuntimeError('Failed: '+logname)
    print('PASS',logname,flush=True)

def unpack(archive,out):
    out.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            need((out/info.filename).resolve().is_relative_to(out.resolve()),'Archive path containment')
            need((info.external_attr>>16)&0o170000 != 0o120000,'No archive symlinks')
        z.extractall(out)

def inventory(directory,sites_path,table_path,expected_rules,expected_min):
    cases=readz(directory/'runtime_cases.json.gz')
    report=json.loads((directory/'runtime.json').read_text())
    metrics=json.loads((directory/'runtime_metrics.json').read_text())
    sites=json.loads(sites_path.read_text())
    wanted=[(i,positive) for i,(_,op,arg) in enumerate(sites)
            for positive in ((False,True) if op=='CD' else (False,))]
    need([(x['site_index'],x['positive']) for x in cases]==wanted,'Complete ordered guarded inventory')
    need(len(sites)==4751 and len(cases)==6176,'Site / case census')
    need(report['status']=='UNIVERSAL_MATHEMATICAL_PASS' and report['failures']==[],'Stored proof status')
    need(report['working_states']==216 and report['proved_cases']==report['expected_cases']==6176,'Stored report census')
    need(report['table_sha256']==sha(table_path) and report['sites_sha256']==sha(sites_path),'Exact runtime byte binding')
    for x in cases:
        need(len(x['duration'])==13 and x['duration'][0]>0 and all(v>=0 for v in x['duration']),
             'Positive finite affine duration')
    need(sum(x['symbolic_steps'] for x in cases)==metrics['symbolic_rules']==expected_rules,'Symbolic rule count')
    need(min(x['duration'][0] for x in cases)==metrics['minimum_duration_constant']==expected_min,'Minimum clock constant')
    need(len({tuple(row) for x in cases for row in x['rows']})==432,'All 432 table rows represented')
    print('PASS stored case inventory:',directory.name,'(fresh derivation requires runtime option)',flush=True)
    return cases,report

def module(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj)
    return obj

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--runtime',action='store_true')
    ap.add_argument('--secondary-runtime',action='store_true')
    ap.add_argument('--work',type=Path,help='Retain outputs here; directory must not exist')
    a=ap.parse_args()
    need(__debug__ and not sys.flags.optimize,'Run Python with assertions enabled; no -O')
    manifest=json.loads((ROOT/'manifest.json').read_text())
    for name,digest in manifest['files'].items():
        need(sha(ROOT/name)==digest,'Manifest mismatch: '+name)
    print('PASS release manifest:',len(manifest['files']),'files',flush=True)
    primary,pr=inventory(ROOT/'evidence',ROOT/'machine/sites216.json',ROOT/'machine/k216.native.tm',1605450,6)
    secondary,sr=inventory(ROOT/'secondary',ROOT/'secondary/sites120.json',ROOT/'secondary/k216-120.native.tm',1605505,9)
    temporary=None
    if a.work:
        work=a.work.resolve();work.mkdir(parents=True,exist_ok=False)
    else:
        temporary=tempfile.TemporaryDirectory(prefix='proveit-k216-');work=Path(temporary.name)
    archive=ROOT/'parent'/f'{K217}.zip';need(sha(archive)==PARENT_SHA,'Pinned K217 archive')
    unpack(archive,work/'predecessors');parent=work/'predecessors'/K217
    nested=parent/'parent'/f'{K218}.zip';need(sha(nested)==GRANDPARENT_SHA,'Pinned K218 archive')
    unpack(nested,work/'predecessors');base=work/'predecessors'/K218
    need((ROOT/'source/baseline219.json').read_bytes()==(base/'source/baseline_sites219.json').read_bytes(),'K219 source provenance')
    run([base/'verify_all.py'],work,'inherited-finite.log',cwd=base)
    checker=base/'binary/code/runtime/symbolic_runtime.py'
    helper=base/'binary/code/runtime/independent_runtime.py'
    for rep in (pr,sr):
        need(rep['checker_sha256']==sha(checker) and rep['helper_sha256']==sha(helper),'Pinned runtime checker hashes')

    rebuilt=work/'rebuilt-sources'
    run([ROOT/'code/build_sources.py','--baseline219',ROOT/'source/baseline219.json',
         '--baseline217',parent/'machine/sites217.json','--output',rebuilt],work,'source-build.log')
    for left,right in [('sites205_reference.json','source/reference205.json'),('sites202.json','source/frozen202.json'),
                       ('sites210.json','machine/sites216.json'),('sites120.json','secondary/sites120.json')]:
        need((rebuilt/left).read_bytes()==(ROOT/right).read_bytes(),'Exact source reconstruction: '+left)
    for permutation,path in [('210','machine/sites216.json'),('120','secondary/sites120.json')]:
        run([ROOT/'code/audit_command_permutation.py','--baseline219',ROOT/'source/baseline219.json',
             '--frozen202',ROOT/'source/frozen202.json','--candidate',ROOT/path,
             '--permutation',permutation,'--output',work/f'source-{permutation}.json'],work,f'source-{permutation}.log')
    run([ROOT/'code/audit_source210.py',ROOT/'source/reference205.json',ROOT/'source/frozen202.json',
         ROOT/'machine/sites216.json',parent/'code/vendor/source_language.py',work/'independent-source.json'],
         work,'independent-source.log')

    built=work/'rebuilt-tables'
    run([ROOT/'code/reconstruct.py','--baseline217',parent/'machine/k217.native.tm','--output',built],work,'table-build.log')
    for left,right in [('k216-210.native.tm','machine/k216.native.tm'),('k216-210.tm','machine/k216.tm'),
                       ('k216-120.native.tm','secondary/k216-120.native.tm'),('k216-120.tm','secondary/k216-120.tm')]:
        need((built/left).read_bytes()==(ROOT/right).read_bytes(),'Exact table reconstruction: '+left)
    machine=work/'machine-audit';shutil.copytree(ROOT/'machine',machine)
    run([machine/'audit.py'],work,'machine-audit.log')
    for name in ['k216.tm','canonicalization.json','blank-prefix.json.gz','blank-seed.json','local81-proof.json','full_table.tex','audit.json']:
        left=(machine/name).read_bytes();right=(ROOT/'machine'/name).read_bytes()
        if name.endswith('.gz'):
            left,right=gzip.decompress(left),gzip.decompress(right)
        need(left==right,'Exact regenerated finite audit: '+name)
    startup=work/'startup210.json';startup.write_bytes(gzip.decompress((ROOT/'evidence/startup.json.gz').read_bytes()))
    run([ROOT/'code/audit_blank210.py',ROOT/'machine/k216.native.tm',startup,work/'independent-blank.json'],
        work,'independent-blank.log')

    # A fixed-length literal replay for the corroborating secondary table.
    auditor=module(ROOT/'machine/audit.py','k216_literal_audit')
    secondary_start=readz(ROOT/'secondary/startup.json.gz')
    endpoint,trace=auditor.simulate(auditor.parse((ROOT/'secondary/k216-120.native.tm').read_bytes()),96244)
    need(trace==secondary_start['trace'],'Secondary full blank trace')
    need(endpoint['state']==84 and endpoint['head']==-8,'Secondary blank root state / head')
    need(endpoint['one_cells']==auditor.expected_seed()['one_cells'],'Secondary complete blank frame')
    print('PASS independent fixed-length secondary blank replay',flush=True)

    for requested,perm,table,sites,directory,saved in [
        (a.runtime,'210','machine/k216.native.tm','machine/sites216.json','evidence',primary),
        (a.secondary_runtime,'120','secondary/k216-120.native.tm','secondary/sites120.json','secondary',secondary)]:
        if not requested:continue
        dest=work/f'runtime{perm}'
        run([base/'binary/code/validate_native.py',ROOT/table,ROOT/sites,dest],work,f'runtime-{perm}.log')
        rep=json.loads((dest/'runtime.json').read_text())
        need(rep['status']=='UNIVERSAL_MATHEMATICAL_PASS' and rep['proved_cases']==6176,'Fresh universal runtime proof')
        need(json.loads((dest/'runtime_cases.json').read_text())==saved,'Exact freshly regenerated ordered case receipts')
        need(json.loads((dest/'startup.json').read_text())==readz(ROOT/directory/'startup.json.gz'),'Exact regenerated startup trace')
        need(rep['table_sha256']==sha(ROOT/table) and rep['sites_sha256']==sha(ROOT/sites),'Fresh runtime byte binding')
        print('PASS all 6176 fresh runtime cases:',perm,flush=True)

    result={'status':'ALL_REQUESTED_K216_CHECKS_PASS','working_states':216,'transition_rows':432,
            'primary_blank_steps':95674,'secondary_blank_steps':96244,'runtime_cases_per_machine':6176,
            'fresh_primary_runtime':a.runtime,'fresh_secondary_runtime':a.secondary_runtime,
            'primary_native_sha256':sha(ROOT/'machine/k216.native.tm'),
            'primary_canonical_sha256':sha(ROOT/'machine/k216.tm'),
            'proof_assistant_endpoint':'No new Lean/Rocq theorem for these bytes; mathematical certificates and inherited calibration.'}
    (work/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
    if a.work:print('Regenerated evidence:',work,flush=True)
    if temporary:temporary.cleanup()

if __name__=='__main__':main()
