#!/usr/bin/env python3
"""Integrity plus fresh independent exact stronger cubic-inequality verification."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent

def check_hashes():
    count=0
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        expected,name=line.split('  ',1)
        p=ROOT/name
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:
            raise ValueError('Integrity failure: '+name)
        count+=1
    return count

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--mode',choices=['full','hashes'],default='full')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args();start=time.time()
    result={'integrity_files':check_hashes(),'mode':args.mode}
    if args.mode=='full':
        with tempfile.TemporaryDirectory(prefix='universal-sink-all-degrees-replay-') as work:
            work=Path(work);data=work/'certificate-data';out=work/'fresh-results'
            shutil.copytree(ROOT/'certificate-data',data)
            shutil.copy2(ROOT/'checker/check.py',work/'check.py')
            run=subprocess.run([sys.executable,str(work/'check.py'),'--source',str(data),'--output',str(out)],capture_output=True,text=True,timeout=600)
            if run.returncode:raise RuntimeError(run.stdout+'\n'+run.stderr)
            receipt=json.loads((out/'receipt.json').read_text())
            if receipt['status']!='PASS':raise ValueError('Exact replay did not pass')
            result['fresh_exact_receipt']=receipt
            result['scope']='Exact factor-3 cubic certificates and complete core coverage; actual-degree closure is proved in the article.'
    else:result['scope']='Integrity only; this mode does not verify the mathematics.'
    result['status']='PASS';result['elapsed_seconds']=round(time.time()-start,3)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    summary={k:v for k,v in result.items()if k!='fresh_exact_receipt'}
    if 'fresh_exact_receipt'in result:
        r=result['fresh_exact_receipt']
        summary['labeled_core_formula_checks']=r['labeled_core_formula_checks']
        summary['permutation_classes']=r['independent_permutation_classes']
        summary['polynomial_squares']=r['total_positive_weight_polynomial_squares']
        summary['positive_remainder_monomials']=r['total_reconstructed_positive_remainder_terms']
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
