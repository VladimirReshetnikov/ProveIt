#!/usr/bin/env python3
"""Reproduce every delivered ordinary polynomial in a fresh output directory.

Standard library only. No network, proof search, or consistency oracle is used.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent/'provenance/upstream')]
from affine_contract import contract,independent_verify,polynomial_and_metrics
from make_integer import make_integer,independent_verify as verify_integer
from verify_synchronized import exact_expansion

EXPECTED={
    'source895':(895,773,4863,63908265),
    'natural596':(596,474,7263,63909160),
    'natural529':(529,407,10782,211184624),
    'natural522':(522,400,20225,83900628),
    'integer2088':(2088,922,26791,83901150),
}

def need(ok,message):
    if not ok: raise ValueError(message)

def write(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n')

def counts(name,equation):
    m=equation['metrics']
    values=tuple(m[k] for k in ('variables','quadratic_rows','expanded_monomials','max_abs_expanded_coefficient'))
    need(values==EXPECTED[name],f'unreviewed metric change for {name}: {values}')
    need(m['exact_degree']==4,'degree changed')
    need(sum(m['variable_kinds'].values())==m['variables'],'stale variable-kind metadata')
    return m

def generate(output):
    output=Path(output).resolve()
    output.mkdir(parents=True,exist_ok=True)
    need(not any(output.iterdir()),'output directory must be empty')
    command=[sys.executable]+([] if __debug__ else ['-O'])+[str(HERE/'synchronized_builder.py'),
              '--product-index','--factored-source','--output',str(output/'source895')]
    result=subprocess.run(command,text=True,capture_output=True)
    need(result.returncode==0,'source generation failed: '+result.stdout+result.stderr)
    source=json.loads((output/'source895/equation.json').read_text())
    sourcepoly=json.loads((output/'source895/expanded_polynomial.json').read_text())
    exact_expansion(source,sourcepoly)
    census={'source895':counts('source895',source)}
    for cap,name in ((4,'natural596'),(16,'natural529'),(64,'natural522')):
        target,certificate=contract(source,support_cap=cap,terminal_quadratic=True)
        receipt=independent_verify(source,target,certificate)
        polynomial,_=polynomial_and_metrics(target['residuals'],len(target['variables']))
        exact=exact_expansion(target,polynomial)
        receipt['expanded_polynomial_audit']=exact
        for filename,data in (('equation.json',target),('elimination_certificate.json',certificate),
                              ('expanded_polynomial.json',polynomial),('VERIFICATION.json',receipt)):
            write(output/name/filename,data)
        census[name]=counts(name,target)
    natural=json.loads((output/'natural522/equation.json').read_text())
    integer,polynomial,certificate=make_integer(natural)
    receipt=verify_integer(natural,integer,polynomial,certificate)
    for filename,data in (('equation.json',integer),('expanded_polynomial.json',polynomial),
                          ('conversion_certificate.json',certificate),('VERIFICATION.json',receipt)):
        write(output/'integer2088'/filename,data)
    census['integer2088']=counts('integer2088',integer)
    files={str(p.relative_to(output)):sha256(p.read_bytes()).hexdigest()
           for p in sorted(output.rglob('*')) if p.is_file()}
    write(output/'CENSUS.json',{'status':'PASS','equations':census,'sha256':files,
        'scope':'Exact generation, contraction replay and coefficient checks; universal proofs are in report.tex.'})
    return census

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    census=generate(args.output)
    print(json.dumps({'status':'PASS','metrics':{n:{k:m[k] for k in
          ('variables','quadratic_rows','exact_degree','expanded_monomials','max_abs_expanded_coefficient')}
          for n,m in census.items()}},indent=2))

if __name__=='__main__':main()
