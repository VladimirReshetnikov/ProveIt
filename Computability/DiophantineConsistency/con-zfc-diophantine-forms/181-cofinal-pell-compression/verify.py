#!/usr/bin/env python3
"""Read-only release audit: exact coefficients, proof fixtures, reconstruction."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def require(test,msg):
    if not test:raise ValueError(msg)

def run(args):
    flags=['-B']+(['-O'] if sys.flags.optimize else [])
    proc=subprocess.run([sys.executable,*flags,*map(str,args)],cwd=ROOT,
                        capture_output=True,text=True)
    require(proc.returncode==0,'failed '+str(args[0])+'\n'+proc.stderr+'\n'+proc.stdout)
    try:return json.loads(proc.stdout)
    except json.JSONDecodeError as ex:raise ValueError('non-JSON audit output: '+str(args[0])) from ex

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--receipt',type=Path)
    ap.add_argument('--skip-manifest',action='store_true')
    args=ap.parse_args()
    result={'status':'pass','python_optimized':bool(sys.flags.optimize),
            'scope':'Finite coefficient identities, reconstruction and bounded fixtures; see report for unbounded proofs.'}
    mf=ROOT/'MANIFEST.sha256'
    if mf.exists() and not args.skip_manifest:
        count=0
        for line in mf.read_text().splitlines():
            digest,name=line.split('  ',1)
            file=ROOT/name
            require(file.is_file(),'manifest file missing: '+name)
            require(hashlib.sha256(file.read_bytes()).hexdigest()==digest,'manifest mismatch: '+name)
            count+=1
        result['manifest_files_checked']=count
    else:result['manifest_files_checked']=None
    result['one_square_endpoints']=run(['code/check_endpoint_delta.py'])
    result['canonical_frame_parity']=run(['code/check_frame_parity.py','inherited/package166/stages/compressed/raw_source.json'])
    result['one_square_finite_cases']=run(['code/check_one_square_center.py'])
    result['independent_finite_cases']=run(['code/check_one_square_independent.py'])
    result['oriented_pooling']=run(['pooling/check_oriented_independent.py','--root','pooling'])
    # Exporter first authenticates both complete factored specifications.
    # Invoke only its read-only authentication function here.
    sys.path.insert(0,str(ROOT/'code'))
    from export_pooling import authenticate
    authenticate()
    result['factored_definitions']='all request ports and both pooled residual formulas agree exactly'
    with tempfile.TemporaryDirectory(prefix='conzfc-rebuild-') as td:
        tmp=Path(td)
        result['quartic_rebuild']=run(['code/build_one_square.py','--output',tmp/'quartics'])
        compared=[]
        for p in sorted((tmp/'quartics').rglob('*')):
            if p.is_file():
                rel=p.relative_to(tmp/'quartics')
                target=ROOT/'equations'/rel
                require(p.read_bytes()==target.read_bytes(),'quartic reconstruction mismatch: '+str(rel))
                compared.append(str(rel))
        result['quartic_rebuilt_files']=compared
        for split,folder in [(False,'oriented_pool'),(True,'oriented_split')]:
            cmd=['pooling/build_oriented_pool.py','--output',tmp/folder]
            if split:cmd.append('--split')
            result[folder+'_rebuild']=run(cmd)
            compared=[]
            for p in sorted((tmp/folder).glob('*.json')):
                target=ROOT/'pooling'/folder/p.name
                require(p.read_bytes()==target.read_bytes(),'pool reconstruction mismatch: '+folder+'/'+p.name)
                compared.append(p.name)
            result[folder+'_rebuilt_files']=compared
    # A tuple evaluator should compute the supplied polynomial and reject a
    # wrong-dimensional or boolean input; it must never silently coerce it.
    with tempfile.TemporaryDirectory(prefix='conzfc-evaluate-') as td:
        for n in [229,228,207,206]:
            p=Path(td)/f'p{n}.json';p.write_text(json.dumps([0]*n))
            e=run(['evaluate.py',str(n),p,'--residuals'])
            require(e['value']==sum(v*v for v in e['residuals']),'evaluator sum differs')
        p=Path(td)/'bad.json';p.write_text('[true]')
        proc=subprocess.run([sys.executable,'-B',str(ROOT/'evaluate.py'),'206',str(p)],capture_output=True,text=True)
        require(proc.returncode!=0,'invalid tuple accepted')
    result['evaluator_controls']='four complete zero-tuple evaluations and invalid-input rejection pass'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
