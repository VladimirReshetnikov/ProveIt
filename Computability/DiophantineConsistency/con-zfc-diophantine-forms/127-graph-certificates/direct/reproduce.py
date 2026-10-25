#!/usr/bin/env python3
"""Fresh offline reconstruction; every compared endpoint file must match."""
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse,json,subprocess,sys

HERE=Path(__file__).resolve().parent

def require(ok,msg):
    if not ok:raise ValueError(msg)

def run(mode='normal'):
    python=[sys.executable,'-B']+(['-O'] if mode=='optimized' else [])
    results=[]
    with TemporaryDirectory(prefix='oriented_cap_rebuild_') as temp:
        tmp=Path(temp)
        natural=['natural/equation.json','natural/expanded_polynomial.json',
                 'natural/elimination_certificate.json','natural/VERIFICATION.json']
        signed=['mixed_source.json','guarded.json','source_certificate.json','sign_certificate.json',
                'equation.json','projection_certificate.json','expanded_polynomial.json','METRICS.json']
        cases=[('equation240','build.py',['--support-cap','32'],natural),
               ('equation239','build.py',['--support-cap','96'],natural),
               ('integer381','build_signed_cap.py',['--late-signs'],signed),
               ('integer391','build_signed_cap.py',['--late-signs','--affine-support','4'],signed)]
        for name,script,args,files in cases:
            dest=tmp/name
            p=subprocess.run(python+[str(HERE/script),'--output',str(dest)]+args,
                             cwd=HERE,text=True,capture_output=True)
            require(p.returncode==0,'rebuild failed: '+name+'\n'+p.stderr)
            for rel in files:
                require((dest/rel).read_bytes()==(HERE/name/rel).read_bytes(),
                        'byte inequality: '+name+'/'+rel)
            if name.startswith('equation'):
                for rel in ['raw/equation.json','raw/raw_audit_input.json','raw/cap_certificate.json']:
                    require((dest/rel).read_bytes()==(HERE/'equation240'/rel).read_bytes(),
                            'raw byte inequality: '+name+'/'+rel)
            results.append({'endpoint':name,'byte_identical_files':len(files)+(3 if name.startswith('equation') else 0)})
    return {'status':'PASS','mode':mode,'fresh_subprocesses':True,'network_required':False,
            'results':results,'scope':'Exact endpoint syntax reconstruction, separate from unbounded proofs.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--mode',choices=['normal','optimized'],default='normal')
    p.add_argument('--output',type=Path);a=p.parse_args();result=run(a.mode)
    body=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(body)
    print(body,end='')
