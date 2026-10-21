"""Own ten-leaf replay on a disposable copy; no wrappers or ancestor suites."""
from pathlib import Path,PurePosixPath
import argparse,concurrent.futures,gzip,hashlib,json,os,shutil,stat,subprocess,sys,time,zipfile
ap=argparse.ArgumentParser();ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
O=a.output.resolve();O.mkdir(exist_ok=False);P=O/'packet';shutil.copytree(a.packet.resolve(),P);(O/'logs').mkdir()
def extract(archive):
    with zipfile.ZipFile(archive) as z:
        names=set()
        for i in z.infolist():
            p=PurePosixPath(i.filename);assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
            assert i.filename not in names;names.add(i.filename)
        z.extractall(O/'parents')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
arc=P/'parent/K217_Dominated_Continuation_2026-10-20.zip'
assert sha(arc)=='4aa33f0c4844043d243fb7d01ef316d4b72de641864e5317525f7cfac7f5c809';extract(arc)
B=O/'parents/K217_Dominated_Continuation_2026-10-20';arc=B/'parent/K218_Dominated_Rho8_2026-10-20.zip'
assert sha(arc)=='080b4fe855c109ab77588c01c9e012d9572afa7721682306370ccb2eb22cbea9';extract(arc)
G=O/'parents/K218_Dominated_Rho8_2026-10-20'
assert (P/'source/baseline219.json').read_bytes()==(G/'source/baseline_sites219.json').read_bytes()
for rel,h in {'validate_native.py':'49b0a77bafa3549cef72e381352eeadad28937519ec5463c3cf3bee545f6f7e2','runtime/symbolic_runtime.py':'7ca30fd11def00e973d8f30997e51fa2dd87ae2eff311ea8c9fc4ac08c9d774f','runtime/independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346','inputs/legacy_mapping.json':'26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'}.items():
    assert sha(G/'binary/code'/rel)==h
M=O/'machine-audit';shutil.copytree(P/'machine',M)
(O/'startup210.json').write_bytes(gzip.decompress((P/'evidence/startup.json.gz').read_bytes()))
jobs=[
('source-build',[P/'code/build_sources.py','--baseline219',P/'source/baseline219.json','--baseline217',B/'machine/sites217.json','--output',O/'rebuilt-sources'],O/'rebuilt-sources/source_build.json','PASS_DETERMINISTIC_SOURCE_REBUILD'),
('permutation210',[P/'code/audit_command_permutation.py','--baseline219',P/'source/baseline219.json','--frozen202',P/'source/frozen202.json','--candidate',P/'machine/sites216.json','--permutation','210','--output',O/'source210.json'],O/'source210.json','PASS_EXACT_SOURCE_COMMAND_PERMUTATION'),
('permutation120',[P/'code/audit_command_permutation.py','--baseline219',P/'source/baseline219.json','--frozen202',P/'source/frozen202.json','--candidate',P/'secondary/sites120.json','--permutation','120','--output',O/'source120.json'],O/'source120.json','PASS_EXACT_SOURCE_COMMAND_PERMUTATION'),
('independent-source',[P/'code/audit_source210.py',P/'source/reference205.json',P/'source/frozen202.json',P/'machine/sites216.json',B/'code/vendor/source_language.py',O/'independent-source.json'],O/'independent-source.json','PASS'),
('table-build',[P/'code/reconstruct.py','--baseline217',B/'machine/k217.native.tm','--output',O/'rebuilt-tables'],O/'rebuilt-tables/reconstruction.json','PASS_EXACT_TABLE_RECONSTRUCTION'),
('machine-audit',[M/'audit.py'],M/'audit.json','PASS'),
('blank210',[P/'code/audit_blank210.py',P/'machine/k216.native.tm',O/'startup210.json',O/'blank210.json'],O/'blank210.json','PASS'),
('blank120',[Path(__file__).resolve().with_name('secondary_blank.py'),'--packet',P,'--output',O/'blank120.json'],O/'blank120.json','INDEPENDENT_SECONDARY_NATIVE_CANONICAL_BLANK_PASS'),
('runtime210',[G/'binary/code/validate_native.py',P/'machine/k216.native.tm',P/'machine/sites216.json',O/'runtime210'],O/'runtime210/runtime.json','UNIVERSAL_MATHEMATICAL_PASS'),
('runtime120',[G/'binary/code/validate_native.py',P/'secondary/k216-120.native.tm',P/'secondary/sites120.json',O/'runtime120'],O/'runtime120/runtime.json','UNIVERSAL_MATHEMATICAL_PASS')]
result={'status':'RUNNING','scope':'Eight selected finite/source leaves and two independent full runtime replays; each on a disposable copy. Inherited logical calibration reviewed separately. No manifest wrapper, ancestor suite, C++ compilation, broad search or proof assistant.','jobs':[]}
def run(job):
    name,args,receipt,expected=job;cap=360 if name.startswith('runtime') else 90
    cmd=[sys.executable,'-B',*map(str,args)];now=time.monotonic()
    env=dict(os.environ);env['PYTHONOPTIMIZE']='0';env['PYTHONDONTWRITEBYTECODE']='1'
    with (O/'logs'/(name+'.stdout')).open('w') as out,(O/'logs'/(name+'.stderr')).open('w') as err:
        try:rc=subprocess.run(cmd,cwd=P,env=env,stdout=out,stderr=err,timeout=cap).returncode;timed=False
        except subprocess.TimeoutExpired:rc=None;timed=True
    data=json.loads(receipt.read_text()) if receipt.exists() else None
    ok=rc==0 and data is not None and data.get('status')==expected
    if ok and name.startswith('runtime'):
        ok=data['proved_cases']==data['expected_cases']==6176 and not data['failures'] and data['working_states']==216
    if ok and name=='source-build':
        for x,y in [('sites205_reference.json','source/reference205.json'),('sites202.json','source/frozen202.json'),('sites210.json','machine/sites216.json'),('sites120.json','secondary/sites120.json')]:ok &= (O/'rebuilt-sources'/x).read_bytes()==(P/y).read_bytes()
    if ok and name=='table-build':
        for x,y in [('k216-210.native.tm','machine/k216.native.tm'),('k216-210.tm','machine/k216.tm'),('k216-120.native.tm','secondary/k216-120.native.tm'),('k216-120.tm','secondary/k216-120.tm')]:ok &= (O/'rebuilt-tables'/x).read_bytes()==(P/y).read_bytes()
    if ok and name=='machine-audit':
        for x in ['k216.tm','canonicalization.json','blank-prefix.json.gz','blank-seed.json','local81-proof.json','full_table.tex','audit.json']:
            l=(M/x).read_bytes();r=(P/'machine'/x).read_bytes()
            if x.endswith('.gz'):l,r=gzip.decompress(l),gzip.decompress(r)
            ok &= l==r
    return dict(name=name,argv=cmd,cwd=str(P),timeout_seconds=cap,exit_code=rc,timed_out=timed,seconds=time.monotonic()-now,receipt=str(receipt),status=data.get('status') if data else None,accepted=bool(ok))
def record(r):
    result['jobs'].append(r);result['status']='RUNNING' if r['accepted'] else 'FAIL'
    (O/'actual.json').write_text(json.dumps(result,indent=2)+'\n');print(r['name'],r['accepted'],r['status'],flush=True)
for job in jobs[:8]:
    r=run(job);record(r)
    if not r['accepted']:sys.exit(1)
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    for r in pool.map(run,jobs[8:]):record(r)
result['status']='TEN_SELECTED_LEAVES_PASS' if all(r['accepted'] for r in result['jobs']) else 'FAIL'
(O/'actual.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],flush=True)
if result['status']!='TEN_SELECTED_LEAVES_PASS':sys.exit(1)
