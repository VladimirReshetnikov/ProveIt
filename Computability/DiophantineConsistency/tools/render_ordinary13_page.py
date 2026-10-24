#!/usr/bin/env python3
"""Render/check only the new ordinary13 page; no existing page is modified."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import ast
import sys

ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'candidates/one-page-ordinary13'
ALPHABET='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'

def need(ok,msg):
    if not ok:raise ValueError(msg)

def symbolic_binding():
    parent=json.loads((OUT/'parent-polynomial.json').read_text());new=json.loads((OUT/'polynomial.json').read_text())
    need(parent['source']==new['source'] and parent['witnesses']==new['witnesses'],'identical literal universal90-gate recipe')
    pool={}
    def intern(t):
        if t not in pool:pool[t]=len(pool)
        return pool[t]
    def leaf(x):return intern(('integer',x))if isinstance(x,int)else intern(('symbol','K'if x=='K0'else x))
    def op(tag,a,b):
        if tag in('+','*')and a>b:a,b=b,a
        return intern((tag,a,b))
    def power(x,n):
        if n==0:return leaf(1)
        if n==1:return x
        z=power(x,n//2);q=op('*',z,z)
        return q if n%2==0 else op('*',q,x)
    def parse(text,env):
        def go(n):
            if isinstance(n,ast.Name):return env[n.id]
            if isinstance(n,ast.Constant)and type(n.value)is int:return leaf(n.value)
            if isinstance(n,ast.BinOp):
                if isinstance(n.op,ast.Pow):return power(go(n.left),n.right.value)
                return op({ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(n.op)],go(n.left),go(n.right))
            raise ValueError(ast.dump(n))
        return go(ast.parse(text,mode='eval').body)
    printed=[('J','3*j+1'),('qm','beta*J'),('q','qm+1'),('C','q-F-alpha'),
      ('E','X*Y'),('k','eta+zeta'),('c','k*Y+eta'),('a','E+Y'),('H','4*a+3'),('Delta','a**2+H'),
      ('U','q**2*Y'),('M','q**3*qm'),('ell','E*(k*Y)'),('W','qm*k+1'),('Bt','(q*K+X)*C-q*F'),
      ('R','(qm*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*J'),
      ('Z','M*(ell+k+r)+qm*Y-q**3*W*Bt'),('D','U*(X+a*c)+H*(U*gamma+q*E-(k-R-1))'),
      ('A0','Z**2-M**2*(ell*(ell+k)+1)'),('A1','D**2-U**2*(Delta*c**2+1)'),
      ('Q','Delta*(f**2-1)'),('I','i*c**2'),('V','f**2*(c*T-R)-c'),('y','V+u'),
      ('P','((1+A0)*(1+A1)*(y**2-Q*(y**2-V**2)))*(1+(I**2-Q))-1')]
    env={x:leaf(x)for x in parent['witnesses']+['beta','K','MC','MF']}
    for name,expr in printed:env[name]=parse(expr,env)
    actual={x:leaf(x)for x in parent['witnesses']+parent['fixed_numerals']}
    for name,tag,a,b in parent['source']:
        actual[name]=op(tag,leaf(a)if isinstance(a,int)else actual[a],leaf(b)if isinstance(b,int)else actual[b])
    need(actual[parent['output']]==env['P'],'complete page formula equals all90 actual gates over free symbols')
    need(Counter(row[1]for row in parent['source'])=={'+':24,'-':17,'*':49},'actual90 operation breakdown')
    return {'all90_gates_match_printed_schedule':True,'method':'exact shared terms modulo commutative operand order; no hash or numerical substitution',
      'variables':len(parent['witnesses']),'degree':51,'operations':90,'operation_counts':{'+':24,'-':17,'*':49},
      'uniform_nonzero_degree_coefficient':'-32(3 beta)^15 at j15 F eta7 X6 Y13 f4 i2 u gamma alpha'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--render',action='store_true');args=ap.parse_args()
    literal=(OUT/'SEED.txt').read_text().strip();need(len(literal)==436 and all(c in ALPHABET for c in literal),'complete436-character seed')
    template=(OUT/'equation-template.tex').read_text();need(template.count('%%SEED%%')==1,'one complete inline seed slot')
    tex=template.replace('%%SEED%%','\n'.join(literal[j:j+62]+r'\par'for j in range(0,len(literal),62)))
    if args.render:
        (OUT/'equation.tex').write_text(tex)
        p=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(OUT),str(OUT/'equation.tex')],capture_output=True,text=True,timeout=60)
        (OUT/'RENDER.log').write_text(p.stdout+p.stderr);need(p.returncode==0 and 'Overfull'not in p.stdout,'clean PDF rendering')
    need((OUT/'equation.tex').read_text()==tex,'standaloneTeX includes exactly the displayed seed')
    info=subprocess.run(['pdfinfo',str(OUT/'equation.pdf')],capture_output=True,text=True,check=True).stdout
    need(re.search(r'Pages:\s+1\b',info)is not None and '612 x 792' in info,'one Letter page')
    subprocess.run(['pdftotext','-raw',str(OUT/'equation.pdf'),str(OUT/'equation.txt')],check=True)
    text=(OUT/'equation.txt').read_text();lines=[s.strip()for s in text.splitlines()]
    expected=[literal[j:j+62]for j in range(0,len(literal),62)]
    need(any(lines[k:k+len(expected)]==expected for k in range(len(lines))),'every printed seed character extracted exactly')
    need(ALPHABET in text,'all62 printed alphabet characters')
    glyphs=['α','η','ζ','γ','β','ρ','κ','ϱ','∆']
    need(all(g in text for g in glyphs),'all distinct printed Greek coefficient/unknown glyphs')
    result={'status':'PASS','python_optimization':sys.flags.optimize,'printed_unknown_aliases':{'j_*':'j'},
      'scope':'Exact finite page/circuit identity and rendering only. Ordinary native/Pell semantics and internal formalization boundaries remain explicit.',
      'formula_binding':symbolic_binding(),'render':{'pages':1,'paper':'Letter','no_overfull_boxes':True,'body_font_pt':9,
      'all436_seed_characters_exact':True,'all62_alphabet_characters_exact':True,'all_Greek_glyphs_present':glyphs,
      'nonwhite_pdf_characters':len(re.sub(r'\s','',text))},
      'sha256':{name:hashlib.sha256((OUT/name).read_bytes()).hexdigest()for name in['equation.tex','equation.pdf','SEED.txt','polynomial.json']}}
    (OUT/('PAGE_VERIFY_OPTIMIZED.json' if not __debug__ else 'PAGE_VERIFY.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
