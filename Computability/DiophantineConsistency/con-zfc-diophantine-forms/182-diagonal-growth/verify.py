#!/usr/bin/env python3
"""Independent finite verifier for the delivered 214-variable quartic.

This checker imports neither the producer nor its polynomial utilities.
It authenticates the inherited equation, checks the entire source change,
recollects every coefficient, validates the printed formulas, and checks
the source-bound label certificate. Unbounded semantics are proved in
report.tex and the accompanying proof notes, not by finite sampling.
"""
from __future__ import annotations
import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
PYTHON = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else [])
PARENT_SHA = '8d919a1e5d6a802765b6d010c0140fb1d83c3d36d211b209b7a8d2fb3f3fb6f6'
EXPECTED = {'variables':214, 'residuals':153, 'degree':4,
            'monomials':5656, 'height':219813,
            'residual_monomials':1040, 'residual_height':464,
            'domain':'unrestricted integers'}

def need(ok, text):
    if not ok:
        raise ValueError(text)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def clean(p):
    return {m:c for m,c in p.items() if c}

def plus(a,b):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+c
    return clean(out)

def minus(a,b):
    return plus(a,{m:-c for m,c in b.items()})

def times(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(sorted(m+n))
            out[key]=out.get(key,0)+c*d
    return clean(out)

def terms_poly(terms, n, max_degree):
    out={}
    for c,m in terms:
        need(type(c) is int and c!=0,'nonzero integer coefficient required')
        need(type(m) is list and len(m)<=max_degree,'monomial degree')
        need(all(type(i) is int and 0<=i<n for i in m),'coordinate outside domain')
        need(m==sorted(m),'monomial order')
        key=tuple(m)
        need(key not in out,'duplicate coefficient')
        out[key]=c
    return out

def parse_text(text):
    def visit(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:
            return {} if n.value==0 else {():n.value}
        if isinstance(n,ast.Name) and n.id.startswith('x') and n.id[1:].isdigit():
            return {(int(n.id[1:]),):1}
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):
            return {m:-c for m,c in visit(n.operand).items()}
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,ast.Add):return plus(visit(n.left),visit(n.right))
            if isinstance(n.op,ast.Sub):return minus(visit(n.left),visit(n.right))
            if isinstance(n.op,ast.Mult):return times(visit(n.left),visit(n.right))
            if isinstance(n.op,ast.Pow):
                need(isinstance(n.right,ast.Constant) and n.right.value==2,'only fixed squares in rows')
                a=visit(n.left);return times(a,a)
        raise ValueError('unsupported literal expression')
    return visit(ast.parse(text.replace('^','**'),mode='eval').body)

def audit(eq, parent, expanded):
    need(eq['domain']=='unrestricted integers','witness domain')
    need(len(eq['variables'])==214 and len(eq['residuals'])==153,'complete shape')
    need(eq['variables']==parent['variables'][:214],'retained coordinate identities')
    need(eq['diagonal_coefficient']==464 and eq['horizon_minimum']==464,'fixed growth values')
    before=[terms_poly(r['terms'],215,2) for r in parent['residuals']]
    after=[terms_poly(r['terms'],214,2) for r in eq['residuals']]
    ports={0:'t0',2:'growth.F',93:'growth.index',132:'shared.A',
           139:'base0.T',140:'pow0.quotient',182:'growth.index_pair.Y',
           185:'cofinal.horizon_root',214:'growth.t_squared'}
    for i,name in ports.items():need(parent['variables'][i]['name']==name,'semantic port '+str(i))
    need(before[96]=={():1,(0,0):1,(0,132):-2,(139,):1},'parent power divisor')
    need(before[97]=={(0,182):-1,(2,):1,(139,140):1,(181,):-1},'parent power value')
    need(before[130]=={():-128,(0,):1,(185,185):-4},'parent horizon')
    need(before[152]=={(0,0):-1,(214,):1},'parent first index gate')
    need(before[153]=={(93,):1,(214,214):-1},'parent second index gate')
    expected={
        96:{():1,(93,93):1,(93,132):-2,(139,):1},
        97:{(93,182):-1,(2,):1,(139,140):1,(181,):-1},
        128:plus(before[128],{(0,0):1,(93,93):-1}),
        130:{():-464,(0,):1,(185,185):-1},
        152:{(0,0):-464,(93,):1},
    }
    for i,row in enumerate(after):
        need(row==expected.get(i,before[i]),'complete row binding '+str(i))
    # The index pair and its orientation contribution are retained.
    need(after[126]==before[126] and after[127]==before[127],'K-pair retained')
    need(after[141].get((93,93))==1 and after[141].get((93,182))==-2,'nominal K orientation')
    need(after[128].get((93,93))==-2,'both K base and K index in frame')
    need(all(214 not in m for row in after for m in row),'deleted wire has no remaining occurrence')
    all_terms=Counter()
    for row in after:
        for monomial,coefficient in times(row,row).items():
            all_terms[monomial]+=coefficient
    poly=clean(all_terms)
    supplied=terms_poly(expanded['terms'],214,4)
    need(poly==supplied,'every collected quartic coefficient')
    need({i for m in poly for i in m}==set(range(214)),'every quantified variable occurs')
    metrics={'variables':214,'residuals':153,'degree':max(map(len,poly)),
             'monomials':len(poly),'height':max(abs(c) for c in poly.values()),
             'residual_monomials':sum(map(len,after)),
             'residual_height':max(abs(c) for p in after for c in p.values()),
             'domain':'unrestricted integers'}
    need(metrics==EXPECTED,'measured metrics')
    return after,metrics

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--receipt',type=Path)
    ap.add_argument('--rebuild',action='store_true')
    ap.add_argument('--exact-majorant',action='store_true')
    args=ap.parse_args()
    parent_path=ROOT/'direct/principal/equation.json'
    need(sha(parent_path)==PARENT_SHA,'authenticated parent SHA-256')
    parent=json.loads(parent_path.read_text())
    path=ROOT/'direct/diagonal214'
    eq=json.loads((path/'equation.json').read_text())
    expanded=json.loads((path/'expanded_polynomial.json').read_text())
    rows,metrics=audit(eq,parent,expanded)
    need(json.loads((path/'metrics.json').read_text())==metrics,'metrics file')
    printed={}
    for line in (path/'residuals.txt').read_text().splitlines():
        if line.startswith('R') and ' = ' in line:
            name,expression=line.split(' = ',1)
            i=int(name[1:]);need(i not in printed,'duplicate printed row')
            printed[i]=parse_text(expression)
    need(printed==dict(enumerate(rows)),'all human-readable residuals')
    # Regenerate every displayed TeX formula and compare the entire appendix.
    subprocess.run(PYTHON+[str(ROOT/'code/export_report.py'),'--check'],check=True,capture_output=True,text=True)
    cmd=PYTHON+[str(ROOT/'majorant/check_label_majorant.py')]
    if args.exact_majorant:cmd.append('--exact')
    majorant=subprocess.run(cmd,check=True,capture_output=True,text=True)
    # Concrete fault controls for the risk-bearing changes.
    rejected=[]
    for row in (96,97,128,130,152):
        changed=json.loads(json.dumps(eq))
        changed['residuals'][row]['terms'][0][0]+=1
        try:audit(changed,parent,expanded)
        except (ValueError,TypeError):rejected.append(row)
        else:raise ValueError('changed source row accepted')
    rebuilt=[]
    if args.rebuild:
        with tempfile.TemporaryDirectory(prefix='conzfc-diagonal-') as td:
            dest=Path(td)/'rebuild'
            subprocess.run(PYTHON+[str(ROOT/'direct/build_diagonal.py'),'--output',str(dest)],check=True,capture_output=True,text=True)
            for file in sorted(path.iterdir()):
                if file.is_file():
                    need((dest/file.name).read_bytes()==file.read_bytes(),'deterministic rebuild '+file.name)
                    rebuilt.append(file.name)
    result={'status':'PASS','scope':'finite literal artifacts; unbounded proof remains separate',
            'metrics':metrics,'parent_sha256':PARENT_SHA,
            'equation_sha256':sha(path/'equation.json'),
            'expanded_sha256':sha(path/'expanded_polynomial.json'),
            'changed_row_corruptions_rejected':rejected,'rebuilt_files':rebuilt,
            'majorant_checker':'PASS','exact_majorant_requested':args.exact_majorant,
            'python_optimization':sys.flags.optimize,
            'printed_residuals_checked':153}
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
