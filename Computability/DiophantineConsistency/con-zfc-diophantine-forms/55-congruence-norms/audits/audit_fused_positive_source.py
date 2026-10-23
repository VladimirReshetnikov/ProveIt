#!/usr/bin/env python3
"""Independent original-source/extraction audit; no builder imports."""
import ast
import hashlib
import itertools
import json
import math
from collections import defaultdict
from functools import lru_cache
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent/'nine_fast'

def need(ok,why):
    if not ok:raise ValueError(why)

def add(a,b,sign=1):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+sign*c
        if not out[m]:del out[m]
    return out

def mul(a,b):
    out=defaultdict(int)
    for m,c in a.items():
        for n,d in b.items():out[tuple(x+y for x,y in zip(m,n))]+=c*d
    return {m:c for m,c in out.items() if c}

def main():
    sp=ROOT/'upstream/upstream_parent_quartic31.json';cp=ROOT/'upstream/code_positive.json'
    gp=ROOT/'generated/calibrated_positive.json'
    s=json.loads(sp.read_text());code=json.loads(cp.read_text());circuit=json.loads(gp.read_text())
    need(hashlib.sha256(sp.read_bytes()).hexdigest()=='1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287','source pin')
    names=s['variables']+s['constants'];zero=(0,)*len(names);n=len(s['variables'])
    def parse(node):
        if isinstance(node,ast.Constant):return {zero:node.value} if node.value else {}
        if isinstance(node,ast.Name):
            if node.id in s['affine_abbreviations']:
                return parse(ast.parse(s['affine_abbreviations'][node.id].replace('^','**'),mode='eval').body)
            e=list(zero);e[names.index(node.id)]=1;return {tuple(e):1}
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return {e:-c for e,c in parse(node.operand).items()}
        if isinstance(node,ast.BinOp):
            a=parse(node.left)
            if isinstance(node.op,ast.Pow):
                out={zero:1}
                for _ in range(node.right.value):out=mul(out,a)
                return out
            b=parse(node.right)
            if isinstance(node.op,ast.Mult):return mul(a,b)
            if isinstance(node.op,ast.Add):return add(a,b)
            if isinstance(node.op,ast.Sub):return add(a,b,-1)
        raise ValueError('unrecognized source expression')
    blocks={};allone={}
    for eq in s['equations']:
        poly=parse(ast.parse(eq['residual'].replace('^','**'),mode='eval').body)
        need(poly=={tuple(t['powers']):t['coefficient'] for t in eq['terms']},'source text/sparse equality')
        block=defaultdict(dict)
        for powers,coef in poly.items():
            alpha=powers[:n];need(sum(alpha)<=2,'quadratic degree')
            padded=tuple([0]*(2-sum(alpha))+[j+1 for j,e in enumerate(alpha) for _ in range(e)])
            factor=math.factorial(2-sum(alpha))*math.prod(math.factorial(e) for e in alpha)
            block[padded][powers[n:]]=coef*factor
        blocks[eq['number']]=dict(block)
        v=defaultdict(int)
        for powers,coef in poly.items():v[powers[n:]]+=coef
        allone[eq['number']]={e:c for e,c in v.items() if c}
    w=code['weights'];pairs=list(itertools.combinations_with_replacement(range(n+1),2))
    targetrows=dict(zip(code['targets'],code['order']));D={};checks=hits=0;weighted={}
    for row,target in zip(code['order'],code['targets']):
        for pair,coeff in blocks[row].items():
            exponent=target-sum(w[j] for j in pair)
            need(exponent>=0 and exponent not in D,'negative or colliding reversed exponent')
            D[exponent]=coeff
            for e,c in coeff.items():weighted[(exponent,)+e]=c
            for inp in pairs:
                land=exponent+sum(w[j] for j in inp);checks+=1
                if land in targetrows:
                    need(targetrows[land]==row and inp==pair,
                         f'target contamination: source row={row}, pair={pair}, input={inp}, landing={land}, target row={targetrows[land]}')
                    factor=1 if inp[0]==inp[1] else 2
                    expected=2 if pair[0]==pair[1] else 1
                    need(factor*expected==2,'factorial cancellation')
                    hits+=1
    need(len(D)==94 and checks==49632 and hits==94,'certificate cardinality')
    need(max(D)==5102 and D[5102]=={(0,0,0,0):1},'new D leading term')
    need(allone[5]=={(0,0,0,0):1},'all-one source vector excluded')
    # Reconstruct the actual emitted Dcode from the DAG, cutting at B.
    # Its monomials have coordinates (B exponent, four port exponents).
    z=(0,)*5;Bnode=circuit['named_nodes']['B'];nodes=circuit['nodes']
    recipes={r['name']:{(0,)+tuple(t['powers']):t['coefficient'] for t in r['terms']} for r in circuit['coefficient_recipes']}
    @lru_cache(None)
    def eval_dag(idx):
        if idx==Bnode:return {(1,0,0,0,0):1}
        node=nodes[idx];kind=node['kind']
        if kind=='literal':return {z:node['value']} if node['value'] else {}
        if kind=='fixed':return recipes[node['name']]
        need(kind in ('add','sub','mul'),'unexpected Dcode variable')
        a,b=eval_dag(node['left']),eval_dag(node['right'])
        return mul(a,b) if kind=='mul' else add(a,b,1 if kind=='add' else -1)
    need(eval_dag(circuit['named_nodes']['Dcode'])==weighted,'emitted Dcode matches independently parsed source')
    bits=(1064921,1070004,1064921,1064922)
    bound=max(sum(abs(c)*(1<<sum(e*b for e,b in zip(p,bits))) for p,c in v.items()) for v in D.values())
    need(bound<1<<2134927,'retained coefficient bound')
    need(circuit['base_scale_exponent']==2134940,'base scale equals8192M')
    result={'status':'PASS','source_sha256':hashlib.sha256(sp.read_bytes()).hexdigest(),
            'code_sha256':hashlib.sha256(cp.read_bytes()).hexdigest(),
            'circuit_sha256':hashlib.sha256(gp.read_bytes()).hexdigest(),
            'builder_sha256':hashlib.sha256((ROOT/'build_nine.py').read_bytes()).hexdigest(),
            'parsed_residuals':22,'padded_pairs':528,'reversed_terms':94,
            'checked_interactions':checks,'correct_target_hits':hits,
            'D_degree':5102,'D_leading_coefficient':1,'max_target':5190,
            'weights_max':183,'emitted_D_matches_independent_AST_derivation':True,
            'retained_M_exponent':2134927,'actual_bound_bit_length':bound.bit_length(),
            'all_one_residual5':1,'analytic_review':'fused_positive_source_review.md',
            'scope':'Changed positive-source layer only; downstream arithmetic bridge/finalizer not reviewed here.'}
    (HERE/'fused_positive_source_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
