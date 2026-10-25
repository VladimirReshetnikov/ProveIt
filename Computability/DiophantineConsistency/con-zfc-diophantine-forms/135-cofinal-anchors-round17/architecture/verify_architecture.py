#!/usr/bin/env python3
"""Read-only exact endpoint audit and optional isolated producer replay."""
import argparse, hashlib, importlib.util, json, shutil, subprocess, sys, tempfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent

def require(ok,message):
    if not ok: raise ValueError(message)

def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def read(path): return json.loads(path.read_text())
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def check():
    affine=load_module('independent_affine',HERE/'check_affine_export.py')
    natural=load_module('independent_natural',HERE/'check_natural.py')
    result={}
    expected={228:(228,178,9866,2445412949744),229:(229,179,9184,83954634),230:(230,180,6858,83954472)}
    raw_hashes=set()
    for n,wanted in expected.items():
        root=HERE/('strict_natural'+str(n));s=read(root/'raw/equation.json')
        meta=read(root/'raw/semantic.json');target=read(root/'natural/equation.json')
        receipt,certificate=affine.verify(meta,s)
        receipt['negative_controls_rejected']=affine.negative_controls(meta,s,certificate)
        receipt.update(affine.check_expansion(s,read(root/'raw/expanded_polynomial.json')))
        affine.validate_quadratic_equation(target,'natural endpoint')
        inverse,expanded=natural.verify(s,target,read(root/'natural/elimination_certificate.json'))
        require(expanded==read(root/'natural/expanded_polynomial.json')['terms'],'coefficient mismatch')
        observed=tuple(inverse[k] for k in ('variables','rows','expanded_monomials','coefficient_height'))
        require(observed==wanted,'unexpected endpoint metrics')
        require(inverse['exact_degree']==4,'degree is not four')
        raw_hashes.add(digest(root/'raw/semantic.json'))
        result[str(n)]={'affine_export':receipt,'natural_projection':inverse,
            'equation_sha256':digest(root/'natural/equation.json'),
            'polynomial_sha256':digest(root/'natural/expanded_polynomial.json')}
    require(len(raw_hashes)==1,'three endpoints do not share exact semantic source')
    return {'status':'passed','endpoints':result,'semantic_source_sha256':next(iter(raw_hashes)),
        'scope':'Finite syntax, nonnegative restoration, full expansion and exact counts; ordinary unbounded proof and inherited logical calibration are separate.'}

def replay():
    compared=[]
    with tempfile.TemporaryDirectory(prefix='conzfc_round17_natural_') as tmp:
        root=Path(tmp)/'architecture';root.mkdir()
        shutil.copytree(HERE/'portable',root/'portable')
        for name in ('build_strict_anchor.py','build_unified_cap.py','contract_reordered.py'):
            shutil.copyfile(HERE/name,root/name)
        prefix=[sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])
        for n,cap in ((229,48),(230,32)):
            out=root/('strict_natural'+str(n))
            subprocess.run(prefix+[str(root/'build_strict_anchor.py'),'--output',str(out),'--support-cap',str(cap)],check=True,capture_output=True)
            for rel in ('raw/equation.json','raw/semantic.json','raw/expanded_polynomial.json','natural/equation.json','natural/expanded_polynomial.json','natural/elimination_certificate.json','SUMMARY.json'):
                require((out/rel).read_bytes()==(HERE/out.name/rel).read_bytes(),'isolated replay mismatch '+out.name+'/'+rel)
                compared.append(out.name+'/'+rel)
        out=root/'strict_natural228';(out/'natural').mkdir(parents=True)
        subprocess.run(prefix+[str(root/'contract_reordered.py'),str(root/'strict_natural229/raw/equation.json'),str(out/'natural'),'--support-cap','32'],check=True,capture_output=True)
        for rel in ('natural/equation.json','natural/expanded_polynomial.json','natural/elimination_certificate.json'):
            require((out/rel).read_bytes()==(HERE/out.name/rel).read_bytes(),'reordered replay mismatch '+rel)
            compared.append(out.name+'/'+rel)
    return {'status':'passed','isolated':True,'compared_byte_identically':compared}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--rebuild',action='store_true');p.add_argument('--output',type=Path);a=p.parse_args()
    result=check()
    if a.rebuild:result['reproduction']=replay()
    result['optimized']=bool(sys.flags.optimize)
    txt=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(txt)
    print(txt)
