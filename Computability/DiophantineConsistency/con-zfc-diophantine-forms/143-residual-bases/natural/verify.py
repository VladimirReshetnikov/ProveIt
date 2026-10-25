#!/usr/bin/env python3
"""Offline independent finite algebra and exact reconstruction, read-only by default."""
import argparse,copy,hashlib,json,subprocess,sys,tempfile
from pathlib import Path
import check_affine_export as affine
import check_natural as contraction
import check_semantic as semantic
import check_row_basis as rowbasis
import render_equation as render
ROOT=Path(__file__).resolve().parent

def require(x,m):
    if not x:raise ValueError(m)
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def call(script,*args):
    cmd=[sys.executable,'-B']+([] if __debug__ else ['-O'])+[str(ROOT/script)]+[str(a) for a in args]
    r=subprocess.run(cmd,check=True,text=True,capture_output=True)
    return r.stdout

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--rebuild',action='store_true');p.add_argument('--output',type=Path);a=p.parse_args()
    out={'status':'PASS','scope':'Finite exact algebra and artifact binding; not an unbounded arithmetic or consistency proof.'}
    sm=read(ROOT/'SOURCE_MAP.json')
    for item in sm['files']:require(sha(ROOT/item['path'])==item['released_sha256'],'source pin '+item['path'])
    out['retained_source_files']=len(sm['files'])
    raw=read(ROOT/'source/equation.json');meta=read(ROOT/'source/semantic.json')
    rec,cert=affine.verify(meta,raw);rec.update(affine.check_expansion(raw,read(ROOT/'source/expanded_polynomial.json')));rec['negative_controls']=affine.negative_controls(meta,raw,cert);out['affine']=rec
    out['contractions']={}
    expected={'projected229':(229,179,6596,83879378),'low_height228':(228,178,9522,560804902),'sparse228':(228,178,7512,2445412949744)}
    for name,metrics in expected.items():
        d=ROOT/name;eq=read(d/'equation.json');cc=read(d/'elimination_certificate.json')
        rec,poly=contraction.verify(raw,eq,cc);require(poly==read(d/'expanded_polynomial.json')['terms'],'full contracted polynomial '+name)
        require(tuple(rec[k] for k in ['variables','rows','expanded_monomials','coefficient_height'])==metrics,'endpoint counts '+name)
        affine.validate_quadratic_equation(eq,name);out['contractions'][name]=rec
    out['semantic']=[semantic.run(ROOT/n,True,ROOT/'source') for n in expected]
    source=read(ROOT/'projected229/equation.json');rc=read(ROOT/'row_basis_certificate.json')
    metrics,lead,poly=rowbasis.verify(source,rc)
    require(sha(ROOT/rc['source'])==rc['source_sha256'],'row-basis source hash')
    final=read(ROOT/'balanced229/equation.json');require(final==rc['equation'],'row-basis target binding')
    require(read(ROOT/'balanced229/expanded_polynomial.json')==dict(schema='sparse_integer_polynomial_v1',domain='nonnegative integers',variables=229,terms=[[c,list(m)] for m,c in sorted(poly.items())]),'full final collected polynomial')
    out['row_basis']=json.loads(call('check_row_basis.py',ROOT/'projected229/equation.json',ROOT/'row_basis_certificate.json'))
    out['rendered_rows']={}
    for name in ['balanced229','projected229','low_height228','sparse228']:
        eq=read(ROOT/name/'equation.json');render.ROOT=ROOT/name
        for file,text in render.generate(eq).items():require((ROOT/name/file).read_text()==text,'rendered text '+name+'/'+file)
        out['rendered_rows'][name]=render.parse_tex(eq)
    if a.rebuild:
        with tempfile.TemporaryDirectory(prefix='natural-descending-') as t:
            t=Path(t)
            call('build.py','--output',t/'build','--support-cap','32')
            files=[]
            for file in ['equation.json','expanded_polynomial.json','METRICS.json','semantic.json','local_majorant.json']:
                require((t/'build/raw'/file).read_bytes()==(ROOT/'source'/file).read_bytes(),'raw rebuild '+file);files.append('source/'+file)
            for file in ['equation.json','expanded_polynomial.json','elimination_certificate.json','VERIFICATION.json']:
                require((t/'build/natural'/file).read_bytes()==(ROOT/'projected229'/file).read_bytes(),'projected rebuild '+file);files.append('projected229/'+file)
            for name in ['low_height228','sparse228']:
                call('contract_fixed.py',t/'build/raw/equation.json',t/name,'--priority',ROOT/name/'priority.json')
                for file in ['equation.json','expanded_polynomial.json','elimination_certificate.json']:
                    require((t/name/file).read_bytes()==(ROOT/name/file).read_bytes(),'fixed-priority rebuild '+name+'/'+file);files.append(name+'/'+file)
            call('apply_row_basis.py',t/'build/natural/equation.json',ROOT/'row_operations.json',t/'balanced229')
            for file in ['equation.json','expanded_polynomial.json']:
                require((t/'balanced229'/file).read_bytes()==(ROOT/'balanced229'/file).read_bytes(),'row-basis rebuild '+file);files.append('balanced229/'+file)
            out['byte_identical_rebuild']=files
    if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
