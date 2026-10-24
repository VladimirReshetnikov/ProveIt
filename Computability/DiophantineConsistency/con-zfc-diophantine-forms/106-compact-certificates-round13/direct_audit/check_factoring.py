#!/usr/bin/env python3
"""Static, non-executing source-factorization binding audit."""
import ast
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
DIRECT=ROOT.parent/'direct'
def need(x,msg):
    if not x:raise ValueError(msg)
def dump(x):return ast.dump(x,include_attributes=False)
def assignment_name(x):
    return x.targets[0].id if isinstance(x,ast.Assign) and isinstance(x.targets[0],ast.Name) else None
def main():
    compact=ast.parse((DIRECT/'build_compact.py').read_text())
    f=next(n for n in compact.body if isinstance(n,ast.FunctionDef) and n.name=='compact_source')
    original=ast.parse((DIRECT/'build_direct.py').read_text())
    cls=next(n for n in original.body if isinstance(n,ast.ClassDef) and n.name=='Circuit')
    g=next(n for n in cls.body if isinstance(n,ast.FunctionDef) and n.name=='source')
    olddefs={n.name:n for n in g.body if isinstance(n,ast.FunctionDef)}
    newdefs={n.name:n for n in f.body if isinstance(n,ast.FunctionDef)}
    for name in ['I','A','M','E','neg','X','req','clos','bundle']:
        need(dump(olddefs[name])==dump(newdefs[name]),'constructor changed '+name)
    a=next(n for n in f.body if assignment_name(n)=='axioms')
    b=next(n for n in g.body if assignment_name(n)=='axioms')
    need(dump(a)==dump(b),'axiom expressions changed')
    start=next(i for i,n in enumerate(f.body) if assignment_name(n)=='ordinary')
    end=next(i for i,n in enumerate(f.body) if assignment_name(n)=='carrier')
    # This is the independently reviewed mathematical zero-set factorization.
    expected=ast.parse('''
ordinary=(v,Z)
for f in axioms[:-1]:ordinary=self.p_mul(ordinary,(v,f))
ordinary=self.p_add((sq(p),Z),self.p_sq(ordinary))
gp,gn=self.p_sq((ad(sq(c),mu(a,b)),mu(c,ad(a,b))))
guard=self.p_sq((gp,ad(gn,sq(ad(d,O)))))
bundled=self.p_add((sq(p),Z),self.p_add(self.p_sq((v,axioms[-1])),guard))
generalized=self.p_sq((v,A(a,p)))
non_mp=self.p_add((sq(q),Z),self.p_mul(generalized,self.p_mul(ordinary,bundled)))
total=self.p_mul(self.p_sq((q,I(p,v))),non_mp)
''').body
    need([dump(n) for n in f.body[start:end]]==[dump(n) for n in expected],'factored source changed')
    oldend=next(i for i,n in enumerate(g.body) if assignment_name(n)=='carrier')
    need([dump(n) for n in f.body[end:]]==[dump(n) for n in g.body[oldend:]],'accumulator or beta source tail changed')
    result={'status':'PASS','constructor_AST_identities':9,'axiom_expression_identity':True,'factored_source_AST_binding':True,
            'accumulator_and_beta_tail_identity':True,'scope':'static AST source binding plus separate zero-set proof; no source execution',
            'sha256':{name:hashlib.sha256((DIRECT/name).read_bytes()).hexdigest() for name in ['build_direct.py','build_compact.py','build_forward.py','build_parametric.py']}}
    (ROOT/'FACTORED_SOURCE_CHECK.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
