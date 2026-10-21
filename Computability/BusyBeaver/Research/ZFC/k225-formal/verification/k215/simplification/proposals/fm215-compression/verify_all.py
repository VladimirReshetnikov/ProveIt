#!/usr/bin/env python3
"""Portable ordinary audits. Lean compilation is an explicit separate command."""
from pathlib import Path
import argparse,copy,hashlib,importlib.util,json,subprocess,sys,tempfile

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not run with -O.')
ROOT=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise AssertionError(message)
def run(*args):
    result=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=ROOT,text=True,capture_output=True)
    require(result.returncode==0, 'Command failed: '+repr(args)+'\n'+result.stdout+result.stderr)
    return result.stdout
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--skip-manifest',action='store_true',help='Only for initial packet assembly before the manifest exists.')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args();checks={}
    if not args.skip_manifest:
        manifest=json.loads((ROOT/'MANIFEST.json').read_text())
        for name,digest in manifest['files'].items():
            require(sha(ROOT/name)==digest,'Manifest mismatch: '+name)
        checks['manifest_files']=len(manifest['files'])
    with tempfile.TemporaryDirectory(prefix='fm215-verify-') as tmp:
        tmp=Path(tmp)
        run(ROOT/'machine/build_fm215.py','--output',tmp/'rebuild')
        for name in ['fm215.native.tm','fm215.tm']:
            require((tmp/'rebuild'/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),'Rebuild mismatch: '+name)
        require(json.loads((tmp/'rebuild/canonicalization.json').read_text())==json.loads((ROOT/'machine/canonicalization.json').read_text()),'Renaming differs')
        checks['exact_reconstruction']='PASS'
        for name,script in [('fm215','machine/verify_fm215.py'),('lean_bindings','formal/check_lean_bindings.py'),('cm215','formal/check_cm215.py'),('tail_finite','research/tail-quantifiers/check_tail_quantifiers.py'),('rejected214','machine/research/verify_trial214_counterexample.py')]:
            out=tmp/(name+'.json');run(ROOT/script,'--output',out)
            checks[name]=json.loads(out.read_text())
        decoder=json.loads(run(ROOT/'checks/decoder_contexts.py'))
        checks['decoder']=decoder
        audit=module('decoder_contexts',ROOT/'checks/decoder_contexts.py')
        cert=json.loads((ROOT/'evidence/decoder_context_certificate.json').read_text())
        damaged=[]
        c=copy.deepcopy(cert);c['format']='wrong';damaged.append(c)
        c=copy.deepcopy(cert);c['root_role']=-1;damaged.append(c)
        c=copy.deepcopy(cert);c['roles'][0]['node']=-1;damaged.append(c)
        c=copy.deepcopy(cert)
        edge=next(e for r in c['roles'] for e in r['edges'] if e['kind']=='internal')
        edge['role']=-1;damaged.append(c)
        for c in damaged:
            try:audit.verify(c)
            except (AssertionError,ValueError,IndexError,KeyError):pass
            else:raise AssertionError('Malformed certificate accepted')
        checks['malformed_decoder_certificates_rejected']=len(damaged)
    receipt=json.loads((ROOT/'formal/fm215-kernel-receipt.json').read_text())
    require(receipt['status']=='PASS_KERNEL_AND_EXACT_BINDINGS','No saved successful kernel receipt')
    for m in receipt['modules']:
        require(m['exit_code']==0,'Failed module in saved receipt')
        require(sha(ROOT/'formal'/(m['module']+'.lean'))==m['source_sha256'],'Stale Lean source receipt')
        require(sha(ROOT/'formal'/(m['module']+'.compile.log'))==m['log_sha256'],'Stale compiler log receipt')
    tail=json.loads((ROOT/'research/tail-quantifiers/tail_lean_verification.json').read_text())
    require(tail['exit_code']==0,'Failed saved tail kernel receipt')
    require(sha(ROOT/'research/tail-quantifiers'/tail['source'])==tail['source_sha256'],'Stale tail source receipt')
    require(sha(ROOT/'research/tail-quantifiers'/tail['log'])==tail['log_sha256'],'Stale tail log receipt')
    checks['saved_kernel_receipts']='SOURCE_AND_LOG_HASHES_MATCH; kernel not rerun by this command'
    for item in json.loads((ROOT/'provenance/source-pins.json').read_text()):
        require(sha(ROOT/item['packet_file'])==item['sha256'],'Stale upstream source pin')
    output={'status':'PASS_ORDINARY_BUNDLE_AUDIT','scope':'Exact construction, finite obligations, counterexample, source/log binding. Kernel proofs replay separately.','checks':checks}
    if args.output:args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'status':output['status'],'checks':list(checks),'kernel_replayed':False},indent=2))

if __name__=='__main__':main()
