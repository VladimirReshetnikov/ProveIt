#!/usr/bin/env python3
"""Read-only offline exact verification, with a complete optional rebuild."""
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, subprocess, sys, tempfile
sys.dont_write_bytecode=True
import check_source,check_natural,check_row_basis,render_equation
ROOT=Path(__file__).resolve().parent
PRE={'dimension206':(206,158,9167,560710452),'projected207':(207,159,6170,85445439),'projected208':(208,160,6183,83847165)}
FIN={'natural206':('dimension206',(206,158,8210,130686376)),'balanced207':('projected207',(207,159,5278,69238087)),'sparse208':('projected208',(208,160,5198,65866712))}
def need(b,m):
    if not b:raise ValueError(m)
def read(p):return json.loads(p.read_text())
def command(script,*args):
    return subprocess.run([sys.executable,'-B']+([] if __debug__ else ['-O'])+[str(script)]+list(map(str,args)),check=True,text=True,capture_output=True).stdout
def main():
    p=argparse.ArgumentParser();p.add_argument('--rebuild',action='store_true');p.add_argument('--output',type=Path);a=p.parse_args()
    result={'status':'PASS','scope':'All finite source rows, exact compositional identity, natural restorations, literal quartic coefficients, invertible row operations and parsed TeX; unbounded natural-domain completeness and logical calibration are the accompanying ordinary proofs.'}
    pins=read(ROOT/'SOURCE_MAP.json')
    for f in pins['files']:need(hashlib.sha256((ROOT/f['path']).read_bytes()).hexdigest()==f['sha256'],'source pin '+f['path'])
    result['pinned_inherited_files']=len(pins['files'])
    result['source_delta']=json.loads(command(ROOT/'check_source.py'))
    raw=read(ROOT/'raw/equation.json');parent=read(ROOT/'inherited/cofinal_raw/equation.json')
    check_source.verify(parent,raw)
    rawexp=check_row_basis.expand(check_row_basis.decode(raw['residuals'],len(raw['variables'])))
    need(read(ROOT/'raw/expanded_polynomial.json')==dict(schema='sparse_integer_polynomial_v1',domain='nonnegative integers',variables=310,terms=[[c,list(m)] for m,c in sorted(rawexp.items())]),'all raw SOS coefficients')
    result['raw_expanded_terms']=len(rawexp)
    result['contraction']={}
    for name,metrics in PRE.items():
        d=ROOT/name;eq=read(d/'equation.json');cert=read(d/'elimination_certificate.json')
        receipt,exp=check_natural.verify(raw,eq,cert)
        need(exp==read(d/'expanded_polynomial.json')['terms'],'all contraction coefficients '+name)
        need(tuple(receipt[k] for k in ('variables','rows','expanded_monomials','coefficient_height'))==metrics,'contraction metrics '+name)
        result['contraction'][name]=receipt
    result['row_basis']={}
    for name,(origin,metrics) in FIN.items():
        d=ROOT/name;src=ROOT/origin/'equation.json';cert=read(d/'row_basis_certificate.json');eq=read(d/'equation.json')
        need(cert['source']==origin+'/equation.json' and cert['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest(),'row source binding '+name)
        met,lead,exp=check_row_basis.verify(read(src),cert)
        need(cert['equation']==eq and cert['operations']==read(d/'operations.json'),'row literal certificate '+name)
        need(tuple(met[k] for k in ('variables','rows','terms','height'))==metrics,'row metrics '+name)
        need(read(d/'expanded_polynomial.json')==dict(schema='sparse_integer_polynomial_v1',domain='nonnegative integers',variables=metrics[0],terms=[[c,list(m)] for m,c in sorted(exp.items())]),'all row SOS coefficients '+name)
        result['row_basis'][name]=json.loads(command(ROOT/'check_row_basis.py',src,d/'row_basis_certificate.json'))
    result['rendered']={}
    for name in list(PRE)+list(FIN):
        d=ROOT/name;eq=read(d/'equation.json')
        for f,t in render_equation.generate(eq).items():need((d/f).read_text()==t,'deterministic render '+name+'/'+f)
        render_equation.ROOT=d;result['rendered'][name]=render_equation.parse_tex(eq)
    bad=deepcopy(read(ROOT/'dimension206/elimination_certificate.json'));bad['steps'][0]['restoration'][0][0]+=1
    try:check_natural.verify(raw,read(ROOT/'dimension206/equation.json'),bad)
    except ValueError:result['corrupted_restoration_rejected']=True
    else:raise ValueError('accepted corrupted restoration')
    # Retain the complete parent source, compiler, arithmetic and logic closure.
    result['inherited']=json.loads(command(ROOT/'inherited/verify.py',*(['--rebuild'] if a.rebuild else [])))
    if a.rebuild:
      with tempfile.TemporaryDirectory(prefix='natural-round20-') as tmp:
        out=Path(tmp)/'rebuild';command(ROOT/'build.py','--output',out)
        compared=[]
        for name,files in [('raw',['equation.json','expanded_polynomial.json','transformation.json'])]+[(n,['equation.json','expanded_polynomial.json','elimination_certificate.json','VERIFICATION.json','priority.json']) for n in PRE]+[(n,['equation.json','expanded_polynomial.json','row_basis_certificate.json','operations.json']) for n in FIN]:
          for file in files:
            need((out/name/file).read_bytes()==(ROOT/name/file).read_bytes(),'byte-identical rebuild '+name+'/'+file);compared.append(name+'/'+file)
        result['byte_identical_rebuild']=compared
    if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))
if __name__=='__main__':main()
