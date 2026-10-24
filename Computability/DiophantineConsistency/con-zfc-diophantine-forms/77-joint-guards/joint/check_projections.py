#!/usr/bin/env python3
"""Standard-library exact projection and leading-form verifier.

Large final polynomials are not expanded. Complete source identities and deleted
rows are expanded; inlined retained rows are compared structurally, and their
degree bounds and homogeneous leading forms are propagated exactly.
"""
from pathlib import Path
import ast, copy, hashlib, json, sys
ROOT=Path(__file__).resolve().parent
sys.setrecursionlimit(20000)

def need(ok,message):
    if not ok:raise ValueError(message)

def main():
    base=json.loads((ROOT/'joint24_degree12.json').read_text())
    compact=json.loads((ROOT/'COMPACT_BASE24.json').read_text())
    extra=['zeta']
    names=sorted(base['variables']+base['fixed_numerals']+extra)
    ni={n:i for i,n in enumerate(names)};zero=(0,)*len(names);one={zero:1}
    def add(a,b,sign=1):
        r=dict(a)
        for e,c in b.items():
            r[e]=r.get(e,0)+sign*c
            if not r[e]:del r[e]
        return r
    def mul(a,b):
        r={}
        for e,c in a.items():
            for f,d in b.items():
                g=tuple(x+y for x,y in zip(e,f));r[g]=r.get(g,0)+c*d
        return {e:c for e,c in r.items() if c}
    def power(p,n):
        r=one
        while n:
            if n&1:r=mul(r,p)
            n//=2
            if n:p=mul(p,p)
        return r
    atoms={}
    for n,i in ni.items():
        e=list(zero);e[i]=1;atoms[n]={tuple(e):1}
    def tree(expression,definitions=None):
        env=definitions or {}
        def visit(n,stack=()):
            if isinstance(n,ast.Name) and n.id in env:
                need(n.id not in stack,'noncyclic definitions')
                return visit(ast.parse(env[n.id],mode='eval').body,stack+(n.id,))
            for key,val in ast.iter_fields(n):
                if isinstance(val,ast.AST):setattr(n,key,visit(val,stack))
                elif isinstance(val,list):setattr(n,key,[visit(v,stack) if isinstance(v,ast.AST) else v for v in val])
            return n
        return visit(ast.parse(expression,mode='eval').body)
    def eval_poly(node,weights=None):
        # If weights are present, return an upper degree and the exact homogeneous
        # component at that upper degree. A zero leading component is allowed.
        if isinstance(node,ast.Name):
            need(node.id in atoms,'declared symbol '+node.id)
            return (weights.get(node.id,0),atoms[node.id]) if weights is not None else atoms[node.id]
        if isinstance(node,ast.Constant) and type(node.value)==int:
            p={zero:node.value} if node.value else {}
            return (0,p) if weights is not None else p
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):
            a=eval_poly(node.operand,weights)
            return (a[0],{e:-c for e,c in a[1].items()}) if weights is not None else {e:-c for e,c in a.items()}
        if isinstance(node,ast.BinOp):
            a=eval_poly(node.left,weights)
            if isinstance(node.op,ast.Pow):
                need(isinstance(node.right,ast.Constant) and type(node.right.value)==int and 0<=node.right.value<=256,'ordinary fixed exponent')
                n=node.right.value
                return (a[0]*n,power(a[1],n)) if weights is not None else power(a,n)
            b=eval_poly(node.right,weights)
            if isinstance(node.op,ast.Mult):return (a[0]+b[0],mul(a[1],b[1])) if weights is not None else mul(a,b)
            sign=-1 if isinstance(node.op,ast.Sub) else 1
            need(isinstance(node.op,(ast.Add,ast.Sub)),'allowed arithmetic')
            if weights is None:return add(a,b,sign)
            if a[0]>b[0]:return a
            if b[0]>a[0]:return (b[0],{e:sign*c for e,c in b[1].items()})
            return (a[0],add(a[1],b[1],sign))
        raise ValueError('Disallowed expression '+ast.dump(node))
    def poly(e,env=None):return eval_poly(tree(e,env))
    def norm(n):return ast.dump(n,include_attributes=False)
    regs=compact['registers'];rows=compact['rows']
    need(len(rows)==12,'compact row count')
    need([poly(e,regs) for e in rows]==[poly(e) for e in base['residuals']],'complete compact base equals exact source')
    need([poly(e) for e in compact['fully_inlined_residuals']]==[poly(e) for e in base['residuals']],'saved compact expansion')
    strong='I**2-Delta*(f**2-1)'
    old_aux='I**2*(V**2-y**2)+y**2-1'
    new_aux='Delta*(f**2-1)*(V**2-y**2)+y**2-1'
    need(poly('('+old_aux+')-('+new_aux+')-(V**2-y**2)*('+strong+')',regs)=={},'two-sided auxiliary row identity')
    cases=[
        ('joint23_degree12',{'V':'f*o-c'},{7},False),
        ('joint22_degree16',{'V':'f*o-c','I':'(2*r+1)*c**2'},{7,8},True),
        ('joint23_degree12_eliminate_I',{'I':'(2*r+1)*c**2'},{8},True),
        ('joint21_degree20',{'V':'f*o-c','I':'(2*r+1)*c**2','a':'E+Y'},{7,8,0},False),
        ('joint20_degree32',{'V':'f*o-c','I':'(2*r+1)*c**2','E':'X*Y','a':'(X+1)*Y'},{7,8,0,1},False),
        ('joint19_degree88',{'V':'f*o-c','I':'(2*r+1)*c**2','E':'X*Y','eta':'c-Y*k','a':'(X+1)*Y'},{7,8,0,2,1},False),
    ]
    results=[]
    for name,maps,deleted,reduce_aux in cases:
        p=json.loads((ROOT/(name+'.json')).read_text());defs=dict(regs);defs.update(maps)
        expected_vars=[n for n in base['variables'] if n not in maps]
        need(p['variables']==expected_vars and p['variable_count']==len(expected_vars),'projection variables '+name)
        need(p['fixed_numerals']==base['fixed_numerals'] and p['coefficient_binding']==base['coefficient_binding'],'unchanged actual fixed tuple '+name)
        source_rows=list(rows)
        if reduce_aux:source_rows[10]=new_aux
        expected=[tree(e,defs) for i,e in enumerate(source_rows) if i not in deleted]
        actual=[tree(e) for e in p['residuals']]
        if 'restoration_abbreviations' in p:
            need(p['restoration_abbreviations']==maps,'recorded exact restoration maps')
            need(p['parent_sha256']==hashlib.sha256((ROOT/'joint24_degree12.json').read_bytes()).hexdigest(),'exact parent packet pin')
            need(p['deleted_parent_rows_zero_based']==sorted(deleted),'recorded deleted rows')
            need([norm(e) for e in expected]==[norm(e) for e in actual],'literal retained-row substitution '+name)
        else:
            need([eval_poly(e) for e in expected]==[eval_poly(e) for e in actual],'expanded retained-row substitution '+name)
        need(p['residual_count']==len(expected)==12-len(deleted),'projected residual count')
        for i in deleted:need(poly(source_rows[i],defs)=={},'deleted defining row restored '+name+'/'+str(i))
        for n,e in p['full_parent_restoration'].items():
            need(n in maps and poly(e)==poly(maps[n],defs),'fully inlined restoration '+name+'/'+n)
        live={n.id for e in actual for n in ast.walk(e) if isinstance(n,ast.Name)}
        need(live==set(expected_vars+base['fixed_numerals']),'closed literal declarations '+name)
        weights={n:1 for n in expected_vars}
        ld=[eval_poly(e,weights) for e in actual]
        top=max(d for d,p0 in ld)
        need(2*top==p['exact_degree'],'sum-of-squares degree upper bound '+name)
        lead={}
        for d,p0 in ld:
            if d==top:lead=add(lead,mul(p0,p0))
        mon=poly(p['degree_witness']['monomial']);need(len(mon)==1,'single certificate monomial')
        target=next(iter(mon));vi=[ni[n] for n in expected_vars]
        coefficient={}
        for e,c0 in lead.items():
            if all(e[i]==target[i] for i in vi):
                ep=tuple(0 if i in vi else e[i] for i in range(len(names)))
                coefficient[ep]=coefficient.get(ep,0)+c0
        recorded=poly(p['degree_witness'].get('coefficient_expression',str(p['degree_witness'].get('coefficient'))))
        need(coefficient==recorded and recorded,'exact nonzero selected coefficient '+name)
        need(all(c0>0 for c0 in recorded.values()) and all(all(not e[i] or names[i]=='beta' for i in range(len(names))) for e in recorded),'positive authentic coefficient '+name)
        results.append({'name':name,'variables':len(expected_vars),'rows':len(actual),'degree':p['exact_degree'],'residual_degree_upper_bounds':[d for d,p0 in ld],'degree_witness':p['degree_witness'],'status':'PASS'})
    result={'status':'PASS','packets':results,'source_compact_identity':True,'auxiliary_ideal_identity':True,'all_deleted_monic_rows_restored':True,'literal_inlined_substitution_check':True,'full_high_degree_SOS_expansion':'not required; exact homogeneous components certify degree','scope':'Exact finite polynomial identities and selected coefficients; unbounded existence equivalence is proved in PROOF.md relative to the stated inherited theorems.'}
    out=ROOT/('PROJECTION_CHECK_optimized.json' if not __debug__ else 'PROJECTION_CHECK_normal.json')
    out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
