#!/usr/bin/env python3
"""Fresh, read-only-to-release, standard-library replay for Report 16.
Run python3 replay.py [--receipt /path/outside/package.json].
No network, CA factor allocation, full physical prologue, or giant polynomial.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
SPECIAL={'manifest.json','SHA256SUMS'}
def require(ok,message):
    if not ok:raise RuntimeError(message)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def shipped(p):
    rel=p.relative_to(ROOT)
    return p.is_file() and not any(x.startswith('.') or x=='__pycache__' for x in rel.parts) and rel.as_posix() not in SPECIAL
def read_json(p):
    def nodup(items):
        d={}
        for k,v in items:
            require(k not in d,'Duplicate manifest key');d[k]=v
        return d
    return json.loads(p.read_text(),object_pairs_hook=nodup)
def verify_manifest():
    m=read_json(ROOT/'manifest.json');actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if shipped(p)}
    require(actual==set(m['files']),'Release inventory mismatch')
    for rel,v in m['files'].items():
        p=ROOT/rel;require(p.stat().st_size==v['bytes'] and digest(p)==v['sha256'],'Hash/length mismatch: '+rel)
    expected=''.join(v['sha256']+'  '+k+'\n' for k,v in m['files'].items())+digest(ROOT/'manifest.json')+'  manifest.json\n'
    require((ROOT/'SHA256SUMS').read_text()==expected,'SHA256SUMS mismatch')
    require(digest(ROOT/'source/source.json')==m['source_sha256'],'Source pin mismatch')
    return m

def run(command,cwd,label):
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    result=subprocess.run(command,cwd=cwd,env=env,text=True,capture_output=True)
    if result.returncode:
        print(result.stdout);print(result.stderr,file=sys.stderr)
        raise RuntimeError(label+' failed: '+str(result.returncode))
    print(label+': PASS',flush=True)
    return result.stdout

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    if args.receipt:
        require(not args.receipt.resolve().is_relative_to(ROOT),'Receipt must be outside published package')
    m=verify_manifest();print('Exact release inventory and hashes: PASS',flush=True)
    generated=['primitive3.json','normalized3.json','reversible5.json','reversible2-primitives.json','source.json','certificates.json','build-stats.json']
    with tempfile.TemporaryDirectory(prefix='report16-fresh-replay-') as temp:
        tmp=Path(temp);work=tmp/'source';shutil.copytree(ROOT/'source',work)
        run([sys.executable,str(work/'run_checks.py')],work,'Eight source checks in normal and optimized Python')
        for p in work.rglob('*'):
            if p.is_file() and p.relative_to(work).as_posix() in {k[len('source/'):] for k in m['files'] if k.startswith('source/')}:
                rel='source/'+p.relative_to(work).as_posix();require(digest(p)==m['files'][rel]['sha256'],'Checker changed a published source artifact: '+rel)
        run([sys.executable,str(work/'build_source.py')],work,'Literal graph regeneration')
        for name in generated:require(digest(work/name)==m['files']['source/'+name]['sha256'],'Regeneration mismatch: '+name)
        audit=tmp/'audit';audit.mkdir();shutil.copy2(ROOT/'audits/release_audit.py',audit/'release_audit.py')
        # The independent audit makes its own clean private copies.
        # Normal mode exercises the bundle-relative default, while optimized mode
        # receives the published source path explicitly. Both inputs are read-only.
        run([sys.executable,str(audit/'release_audit.py')],audit,'Independent release audit normal with relative default')
        run([sys.executable,'-O',str(audit/'release_audit.py'),str(ROOT/'source')],audit,'Independent release audit optimized')
        receipts=[read_json(audit/name) for name in ['release-audit-receipt.json','release-audit-optimized-receipt.json']]
        for v in receipts:require(v['status']=='PASS','Independent audit did not pass')
        primitive=tmp/'primitive-certificates';shutil.copytree(ROOT/'primitive-certificates',primitive)
        for mode in ([],['-O']):
            label='optimized' if mode else 'normal'
            run([sys.executable,*mode,str(primitive/'test_certificate.py')],primitive,'Primitive certificate tests '+label)
            source_arg=[str(work/'source.json')] if mode else []
            run([sys.executable,*mode,str(primitive/'audit_source.py'),*source_arg],primitive,'Primitive source ledger audit '+label)
        for name in ['example-source.json','example-materialized.json','example-witness.json','test-receipt.json','source-ledger-receipt.json','universal-h1-ledger.json']:
            require(digest(primitive/name)==m['files']['primitive-certificates/'+name]['sha256'],'Primitive replay artifact mismatch: '+name)
        primitive_audit=tmp/'audits/primitive'
        primitive_audit.mkdir(parents=True)
        shutil.copy2(ROOT/'audits/primitive/audit_certificate.py',primitive_audit/'audit_certificate.py')
        for mode in ([],['-O']):
            label='optimized' if mode else 'normal'
            inputs=['--certificate-root',str(primitive),'--literal-source',str(work/'source.json')] if mode else []
            run([sys.executable,*mode,str(primitive_audit/'audit_certificate.py'),*inputs,'--output',str(tmp/('primitive-independent-'+label))],primitive,'Independent 53786-check primitive audit '+label)
            independent=read_json(tmp/('primitive-independent-'+label)/('audit-'+label+'-receipt.json'))
            require(independent['status']=='passed' and independent['checks']==53786 and independent['expected_rejections']==136,'Primitive independent evidence count mismatch')
        orbit=tmp/'ca-orbit'
        run([sys.executable,str(primitive/'replay_primitive_ca.py'),'--source',str(primitive/'example-source.json'),'--compiler',str(work/'compiler-reference/reversible_binary.py'),'--output',str(orbit)],primitive,'All 6232 small-example CA steps')
        for name in ['primitive-example-orbit.json','primitive-example-ca-receipt.json']:
            require(digest(orbit/name)==m['files']['primitive-certificates/'+name]['sha256'],'CA orbit mismatch: '+name)
        summary={'status':'PASS','release':m['release'],'manifest_sha256':digest(ROOT/'manifest.json'),'source_sha256':m['source_sha256'],'manifest_payload_files':len(m['files']),'source_check_stages':8,'source_check_modes':['normal','optimized'],'byte_identical_regenerated_json_files':len(generated),'independent_audit_modes':['normal','optimized'],'independent_tm_macro_cases':receipts[0]['independent_tm_macro_cases'],'primitive_certificate_tests_per_mode':13,'primitive_certificate_modes':['normal','optimized'],'independent_primitive_checks_per_mode':53786,'independent_primitive_expected_rejections_per_mode':136,'small_example_CA_steps':6232,'small_example_first_halt':3115,'small_example_first_return':6232,'scope':['Final package inventory verified before and after replay','Published files untouched; all checks/regeneration run in temporary copies','No universal CA factor array or truth table allocated; small example has 387 materialized factors','No giant universal polynomial or complete physical prologue executed','Companion documents pinned; their prior full computational suites are not rerun']}
    verify_manifest()
    if args.receipt:args.receipt.parent.mkdir(parents=True,exist_ok=True);args.receipt.write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
