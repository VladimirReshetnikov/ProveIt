#!/usr/bin/env python3
"""Verify frozen exact certificates and every final coefficient; no root search."""
import argparse, copy, hashlib, json, sys, time, zipfile
from pathlib import Path
sys.dont_write_bytecode = True
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import audit_projection as A
import affine_search
import beta_two_squares as B

def require(ok,message):
    if not ok: raise ValueError(message)
def read(p):return json.loads(p.read_text())
def source_checks():
    ledger=read(ROOT/'SOURCES.json'); out=[]
    for item,stage in zip(ledger['sources'],['source240','source242']):
        p=ROOT/item['file']; raw=p.read_bytes()
        require(hashlib.sha256(raw).hexdigest()==item['sha256'],'source archive hash')
        with zipfile.ZipFile(p) as z:
            expected=z.read(ledger['source_members'][stage])
        require(expected==(ROOT/'stages'/stage/'equation.json').read_bytes(),'source member mismatch')
        out.append({'file':item['file'],'sha256':item['sha256'],'bytes':len(raw)})
    return out

def beta_literal_check():
    source=read(ROOT/'stages/source242/equation.json'); target=read(ROOT/'stages/beta242/equation.json')
    require(len(source['variables'])==242 and len(source['residuals'])==178,'beta parent census')
    require(A.polynomial(source['residuals'][173]['terms'],242)=={():-1,(2,):1,(3,240):-1},'old product')
    require(A.polynomial(source['residuals'][177]['terms'],242)=={():-1,(240,):1,(241,):-4,(241,241):-4},'old square')
    require(A.polynomial(source['residuals'][0]['terms'],242)=={(4,):1,(3,3):-1},'F-square wire')
    for i,row in enumerate(source['residuals']):
        if i not in (173,177):
            require(not any(240 in m or 241 in m for _,m in row['terms']),'beta witness not private')
    expected=copy.deepcopy(source)
    expected['variables'][240]={'name':'beta.square_u','kind':'signed_witness'}
    expected['variables'][241]={'name':'beta.square_v','kind':'signed_witness'}
    expected['residuals'][173]={'label':'bootstrap.beta_base_two_squares','terms':[[-1,[]],[1,[2]],[-1,[4]],[-1,[240,240]],[-1,[241,241]]]}
    del expected['residuals'][177]
    expected['variant']+=':cofinal_beta_two_squares'
    require(expected==target,'literal beta mutation differs')
    generated,mutation=B.changed_equation(source)
    require(generated==target,'beta constructor differs')
    require(mutation==read(ROOT/'stages/beta242/mutation.json'),'beta mutation ledger differs')
    return {'status':'PASS','independent_literal_rows':True,'cofinal_samples':B.checks(),
            'semantic_scope':'Existential equivalence follows from the cofinal-spacing proof; this is not an integer coordinate bijection.'}

def manifest_check():
    p=ROOT/'MANIFEST.sha256'
    if not p.exists():return {'present':False}
    count=0
    for line in p.read_text().splitlines():
        if not line:continue
        h,name=line.split('  ',1);f=ROOT/name
        require(f.is_file() and hashlib.sha256(f.read_bytes()).hexdigest()==h,'manifest: '+name)
        count+=1
    return {'present':True,'status':'PASS','files':count}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--receipt',type=Path);args=parser.parse_args()
    start=time.monotonic();receipt={'status':'PASS','sources':source_checks(),'beta':beta_literal_check(),'checks':{}}
    jobs=[('primary_projection',A.audit,ROOT/'stages/source240/equation.json',ROOT/'stages/radical234'),
          ('primary_rows',A.audit_rows,ROOT/'stages/radical234/equation.json',ROOT/'equations/P234'),
          ('beta_projection',A.audit,ROOT/'stages/beta242/equation.json',ROOT/'stages/radical236'),
          ('beta_affine',A.audit_affine,ROOT/'stages/radical236/equation.json',ROOT/'stages/affine235'),
          ('beta235_rows',A.audit_rows,ROOT/'stages/affine235/equation.json',ROOT/'equations/P235_beta'),
          ('beta236_rows',A.audit_rows,ROOT/'stages/radical236/equation.json',ROOT/'equations/P236_beta')]
    for name,fn,source,directory in jobs:receipt['checks'][name]=fn(source,directory)
    ranks={}
    for name in ('P234','P235_beta'):
        r=affine_search.run(ROOT/'equations'/name/'equation.json')
        require(r['quadratic_left_nullity']==0,'unexpected affine row relation')
        ranks[name]=r
    receipt['affine_rank']=ranks
    from verify_printed import verify as verify_printed
    receipt['printed_equation']=verify_printed(ROOT)
    receipt['manifest']=manifest_check()
    receipt['elapsed_seconds']=round(time.monotonic()-start,3)
    receipt['scope']='Exact finite coefficient certificates and illustrative arithmetic checks. Ordinary unbounded proofs and inherited calibration are separate.'
    if args.receipt:args.receipt.write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    for label,key in [('P234','primary_rows'),('P235_beta','beta235_rows'),('P236_beta','beta236_rows')]:
        print(label,json.dumps(receipt['checks'][key]['output_metrics'],sort_keys=True))
    print('PASS: source pins, all projections, inverse row operations, full expansions, rank checks, printed coefficients, and mutation controls.')
    print('Unbounded correctness is proved in report/report.tex and the retained proof sources.')
if __name__=='__main__':main()
