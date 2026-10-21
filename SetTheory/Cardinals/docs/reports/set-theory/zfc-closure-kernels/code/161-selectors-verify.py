#!/usr/bin/env python3
"""Offline exact K215 reconstruction and audits. --runtime derives every case afresh.

Default: manifests, inherited finite proofs, both source reconstructions,
source bisimulation, table reconstruction, positive-block marker proofs,
complete blank startup, canonical table, mutation control, stored inventory.
--runtime additionally regenerates all 6,176 unbounded symbolic derivations.
Python 3.10+, standard library; assertions must remain enabled.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
PARENT='K217_Dominated_Continuation_2026-10-20'
GRAND='K218_Dominated_Rho8_2026-10-20'
PARENT_SHA='4aa33f0c4844043d243fb7d01ef316d4b72de641864e5317525f7cfac7f5c809'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def gzjson(p):return json.loads(gzip.decompress(p.read_bytes()))
def unpack(archive,dest):
    dest.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            need((dest/info.filename).resolve().is_relative_to(dest.resolve()),'Archive containment')
            need((info.external_attr>>16)&0o170000!=0o120000,'Archive symlink')
        z.extractall(dest)
def run(args,work,logname,cwd=None):
    with (work/logname).open('w') as log:
        p=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=cwd,stdout=log,stderr=subprocess.STDOUT)
    if p.returncode:
        print((work/logname).read_text()[-9000:]);raise RuntimeError('Failed: '+logname)
    print('PASS',logname,flush=True)
def inventory():
    cases=gzjson(ROOT/'evidence/runtime_cases.json.gz')
    sites=json.loads((ROOT/'source/sites215.json').read_text())
    report=json.loads((ROOT/'evidence/runtime.json').read_text())
    expected=[(i,p) for i,(_,op,arg) in enumerate(sites) for p in ((False,True) if op=='CD' else (False,))]
    need([(x['site_index'],x['positive']) for x in cases]==expected,'Ordered case inventory')
    need(len(sites)==4751 and len(cases)==6176,'Case census')
    need(report['status']=='UNIVERSAL_MATHEMATICAL_PASS' and not report['failures'],'Stored runtime result')
    need(report['proved_cases']==report['expected_cases']==6176 and report['working_states']==215,'Runtime census')
    need(report['table_sha256']==sha(ROOT/'machine/k215.native.tm') and report['sites_sha256']==sha(ROOT/'source/sites215.json'),'Runtime byte binding')
    need(report['checker_sha256']==sha(ROOT/'code/runtime/symbolic_runtime.py') and report['helper_sha256']==sha(ROOT/'code/runtime/independent_runtime.py'),'Checker byte binding')
    for c in cases:
        need(len(c['duration'])==13 and c['duration'][0]>0 and all(x>=0 for x in c['duration']),'Positive affine duration')
    need(sum(c['symbolic_steps'] for c in cases)==1698790,'Symbolic rule count')
    need(min(c['duration'][0] for c in cases)==6,'Minimum duration constant')
    keys=set()
    for line in (ROOT/'machine/k215.native.tm').read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,z=line.split();keys.add((int(q),int(b)))
    states={q for q,b in keys}|{254}
    mapping={int(k):int(v) for k,v in json.loads((ROOT/'code/inputs/legacy_mapping.json').read_text()).items()}
    for q in states:
        if q not in mapping:mapping[q]=q+1000
    need(len({mapping[q] for q in states})==len(states),'Legacy-map injectivity')
    need(mapping[84]==96 and mapping[254]==254,'Legacy dispatcher/halt anchors')
    need({tuple(row) for c in cases for row in c['rows']}=={(mapping[q],b) for q,b in keys},'Every actual literal row key covered')
    print('PASS stored case inventory (fresh derivation uses --runtime)',flush=True)
    return cases
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--runtime',action='store_true')
    ap.add_argument('--work',type=Path,help='Retain outputs; directory must not exist')
    a=ap.parse_args();need(__debug__ and not sys.flags.optimize,'Run with assertions enabled')
    manifest=json.loads((ROOT/'manifest.json').read_text())
    for name,digest in manifest['files'].items():need(sha(ROOT/name)==digest,'Manifest: '+name)
    print('PASS release manifest',len(manifest['files']),'files',flush=True)
    saved_cases=inventory();temp=None
    if a.work:work=a.work.resolve();work.mkdir(parents=True,exist_ok=False)
    else:temp=tempfile.TemporaryDirectory(prefix='k215-replay-');work=Path(temp.name)
    archive=ROOT/'parent'/f'{PARENT}.zip';need(sha(archive)==PARENT_SHA,'Pinned parent')
    unpack(archive,work/'parents');parent=work/'parents'/PARENT
    run([parent/'verify.py','--work',work/'parent-proof'],work,'inherited-finite.log',cwd=parent)
    grand=work/'parent-proof'/GRAND
    need(sha(grand/'binary/code/runtime/symbolic_runtime.py')==sha(ROOT/'code/runtime/symbolic_runtime.py'),'Unchanged inherited induction checker')
    need(sha(grand/'binary/code/runtime/independent_runtime.py')==sha(ROOT/'code/runtime/independent_runtime.py'),'Unchanged inherited tape helper')
    need(sha(grand/'binary/code/inputs/legacy_mapping.json')==sha(ROOT/'code/inputs/legacy_mapping.json'),'Unchanged inherited label map')
    reference=ROOT/'reference/permuted216'
    need((reference/'source/baseline219.json').read_bytes()==(grand/'source/baseline_sites219.json').read_bytes(),'Historical source provenance')
    buildref=work/'reference-source'
    run([reference/'code/build_sources.py','--baseline219',reference/'source/baseline219.json',
         '--baseline217',parent/'machine/sites217.json','--output',buildref],work,'reference-build.log')
    for l,r in [('sites205_reference.json','source/reference205.json'),('sites202.json','source/frozen202.json'),('sites210.json','sites210.json')]:
        need((buildref/l).read_bytes()==(reference/r).read_bytes(),'Reference source: '+l)
    run([reference/'code/audit_command_permutation.py','--baseline219',reference/'source/baseline219.json',
         '--frozen202',reference/'source/frozen202.json','--candidate',reference/'sites210.json',
         '--permutation','210','--output',work/'reference-calibration.json'],work,'reference-calibration.log')
    partial=ROOT/'reference/partial216';pr=work/'partial-rebuilt'
    run([partial/'code/reconstruct216.py','--parent',parent,'--out',pr],work,'partial-rebuild.log')
    need((pr/'k216.native.tm').read_bytes()==(partial/'machine/k216.native.tm').read_bytes(),'Partial native source pin')
    need((pr/'sites216.json').read_bytes()==(partial/'source/sites216.json').read_bytes(),'Partial source pin')
    rebuilt=work/'rebuilt'
    run([ROOT/'code/reconstruct.py','--parent',partial,'--output',rebuilt],work,'reconstruction.log')
    for l,r in [('k215.native.tm','machine/k215.native.tm'),('k215.tm','machine/k215.tm'),
                ('sites215.json','source/sites215.json'),('canonicalization.json','machine/canonicalization.json')]:
        need((rebuilt/l).read_bytes()==(ROOT/r).read_bytes(),'Exact reconstruction: '+l)
    run([ROOT/'code/audit_source.py','--reference',reference/'sites210.json',
         '--candidate',ROOT/'source/sites215.json','--out',work/'source.json'],work,'source-bisimulation.log')
    run([ROOT/'code/audit_folds.py','--parent-native',partial/'machine/k216.native.tm',
         '--candidate-native',ROOT/'machine/k215.native.tm','--output',work/'folds'],work,'folds.log')
    startup=work/'startup.json';startup.write_bytes(gzip.decompress((ROOT/'evidence/startup.json.gz').read_bytes()))
    run([ROOT/'code/audit_blank.py','--table',ROOT/'machine/k215.native.tm','--trace',startup,
         '--out',work/'blank.json'],work,'blank.log')
    run([ROOT/'code/audit_machine.py','--machine',ROOT/'machine','--trace',startup,
         '--out',work/'machine-audit'],work,'canonical-machine.log')
    need((work/'machine-audit/full_table.tex').read_bytes()==(ROOT/'sections/full_table.tex').read_bytes(),'Exact typeset table')
    run([ROOT/'code/negative_control.py','--table',ROOT/'machine/k215.native.tm',
         '--sites',ROOT/'source/sites215.json','--out',work/'negative-control.json'],work,'negative-control.log')
    if a.runtime:
        runtime=work/'runtime'
        run([ROOT/'code/validate_native.py',ROOT/'machine/k215.native.tm',ROOT/'source/sites215.json',runtime],work,'runtime.log')
        rep=json.loads((runtime/'runtime.json').read_text())
        need(rep['status']=='UNIVERSAL_MATHEMATICAL_PASS' and rep['proved_cases']==6176,'Fresh unbounded runtime')
        need(rep['table_sha256']==sha(ROOT/'machine/k215.native.tm') and rep['sites_sha256']==sha(ROOT/'source/sites215.json'),'Fresh byte binding')
        need(json.loads((runtime/'runtime_cases.json').read_text())==saved_cases,'Every ordered regenerated case receipt')
        need(json.loads((runtime/'startup.json').read_text())==json.loads(startup.read_text()),'Entire regenerated startup trace')
        print('PASS all 6176 freshly derived case receipts',flush=True)
    result={'status':'ALL_REQUESTED_K215_CHECKS_PASS','working_states':215,'rows':430,
        'blank_steps':95714,'source_occurrences':4751,'guarded_cases':6176,'symbolic_rules':1698790,
        'fresh_runtime':a.runtime,'native_sha256':sha(ROOT/'machine/k215.native.tm'),
        'canonical_sha256':sha(ROOT/'machine/k215.tm'),'source_sha256':sha(ROOT/'source/sites215.json'),
        'proof_assistant_endpoint':'Ordinary mathematical and executable symbolic proof; no new exact-table Lean/Rocq or internal PA theorem.'}
    (work/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
    if a.work:print('Regenerated evidence:',work)
    if temp:temp.cleanup()
if __name__=='__main__':main()
