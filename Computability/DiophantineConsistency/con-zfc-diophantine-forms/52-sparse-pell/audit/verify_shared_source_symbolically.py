#!/usr/bin/env python3
"""Exact symbolic audit of shared homogeneous source evaluation.
No numerical specialization, builder import, or modular equality is used.
"""
from pathlib import Path
from collections import defaultdict
from math import factorial
import ast, hashlib, json
ROOT=Path(__file__).resolve().parents[1]
PORTS=['beta','K0','MC','MF']


def const(n,d):return {(0,)*d:n} if n else {}
def var(i,d):return {tuple(int(j==i) for j in range(d)):1}
def add(a,b,s=1):
    z=dict(a)
    for e,c in b.items():z[e]=z.get(e,0)+s*c
    return {e:c for e,c in z.items() if c}
def mul(a,b):
    z=defaultdict(int)
    for ea,ca in a.items():
        for eb,cb in b.items():z[tuple(x+y for x,y in zip(ea,eb))]+=ca*cb
    return {e:c for e,c in z.items() if c}
def power(a,n,d):
    assert isinstance(n,int) and 0<=n<=8
    z=const(1,d)
    for _ in range(n):z=mul(z,a)
    return z

def expression(s,env,d):
    def go(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return const(n.value,d)
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return {e:-c for e,c in go(n.operand).items()}
        if isinstance(n,ast.BinOp):
            a=go(n.left)
            if isinstance(n.op,ast.Pow):
                assert isinstance(n.right,ast.Constant)
                return power(a,n.right.value,d)
            b=go(n.right)
            if isinstance(n.op,ast.Add):return add(a,b)
            if isinstance(n.op,ast.Sub):return add(a,b,-1)
            if isinstance(n.op,ast.Mult):return mul(a,b)
        raise ValueError(ast.dump(n))
    return go(ast.parse(s,mode='eval').body)

def canonical(p):return [[list(e),c] for e,c in sorted(p.items())]
def digest(p):return hashlib.sha256(json.dumps(canonical(p),separators=(',',':')).encode()).hexdigest()

def source_rows(raw):
    """Re-evaluate the original 60-gate source at each old coordinate n_i+1."""
    n=len(raw['variables']);d=n+4
    env={name:add(var(i,d),const(1,d)) for i,name in enumerate(raw['variables'])}
    env.update({p:var(n+i,d) for i,p in enumerate(PORTS)})
    def get(x):return const(x,d) if isinstance(x,int) else env[x]
    zero=[]
    for name,op,a,b in raw['source']:
        a,b=get(a),get(b)
        env[name]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
        if not env[name]:zero.append(name)
        assert all(sum(e[:n])<=2 for e in env[name]),('Source coordinate degree exceeds two',name)
    rows=[add(get(a),get(b),-1) for a,b in raw['comparisons']]
    return rows,zero


def expected_source(cert,rawrows):
    n=31;out={};ports={p:var(i,4) for i,p in enumerate(PORTS)};rowchecks=0
    for row in cert['rows']:
        rawpoly={};weightedpoly={}
        for term in row['terms']:
            alpha=tuple(term['alpha']);degree=sum(alpha);assert degree<=2
            co=expression(term['coefficient'],ports,4)
            weighted=expression(term['weighted_coefficient'],ports,4)
            factor=factorial(2-degree)
            for a in alpha:factor*=factorial(a)
            assert weighted=={e:factor*c for e,c in co.items()}
            rawpoly=add(rawpoly,{alpha+e:c for e,c in co.items()})
            weightedpoly=add(weightedpoly,{alpha+e:c for e,c in weighted.items()})
            exponent=term['encoding_exponent'];assert exponent>=0
            out=add(out,{(exponent,)+e:c for e,c in weighted.items()})
        assert rawpoly==rawrows[row['original_row_one_based']-1],('Affine source mismatch',row['original_row_one_based'])
        # Degree-two polarization weights double only constants and pure squares.
        correction={e:c for e,c in rawpoly.items() if sum(e[:n])==0 or 2 in e[:n]}
        assert weightedpoly==add(rawpoly,correction),('Diagonal correction mismatch',row['original_row_one_based'])
        rowchecks+=1
    return out,rowchecks


def evaluate_cut(obj,basekey,fixed):
    nodes=obj['nodes'];outidx=obj['named_nodes']['Dcode'];baseidx=obj['named_nodes'][basekey]
    need=set();todo=[outidx]
    while todo:
        ix=todo.pop()
        if ix in need:continue
        need.add(ix)
        if ix==baseidx:continue
        node=nodes[ix]
        if 'left'in node:todo.extend([node['left'],node['right']])
    values={};zeros=0;ops=0;peak=0
    for ix in sorted(need):
        node=nodes[ix];kind=node['kind']
        if ix==baseidx:z=var(0,5)
        elif kind=='literal':z=const(node['value'],5)
        elif kind=='fixed':z=fixed[node['name']]
        elif kind in ['add','sub','mul']:
            a,b=values[node['left']],values[node['right']]
            z=mul(a,b) if kind=='mul' else add(a,b,1 if kind=='add' else -1);ops+=1
        else:raise AssertionError(('Unexpected non-base variable in Dcode',ix,node))
        values[ix]=z;peak=max(peak,len(z));zeros+=not bool(z)
    return values[outidx],dict(source_ancestor_nodes=len(need),source_ancestor_operations=ops,exact_zero_registers=zeros,peak_sparse_terms=peak,base_node=baseidx,Dcode_node=outidx)


def main():
    if not __debug__:raise RuntimeError('Assertions required')
    sourcepath=ROOT/'nine/data/source_system60.json';raw=json.loads(sourcepath.read_text());rows,zero=source_rows(raw)
    sourcehash=hashlib.sha256(sourcepath.read_bytes()).hexdigest()
    assert sourcehash=='ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48'
    files=sorted((ROOT/'nine/generated').glob('nine_*.json'))+sorted((ROOT/'integer/generated').glob('sun10_*.json'))
    canon={};results=[];portvars={p:var(i+1,5) for i,p in enumerate(PORTS)}
    integer_binding=json.loads((ROOT/'integer/FIXED_BINDING.json').read_text())
    for path in files:
        obj=json.loads(path.read_text())
        if path.parent.parent.name=='nine':
            certpath=ROOT/obj['target_file'];cert=json.loads(certpath.read_text());base='B'
            fixed={r['name']:{(0,)+tuple(t['powers']):t['coefficient'] for t in r['terms']} for r in obj['coefficient_recipes']}
        else:
            certpath=(path.parent.parent/obj['positional_certificate']).resolve();cert=json.loads(certpath.read_text());base='base'
            fixed={name:expression(rec['expression'],portvars,5) for name,rec in integer_binding['leaves'].items() if 'expression'in rec}
        assert cert['source_sha256']==sourcehash
        expected,rowchecks=expected_source(cert,rows)
        actual,stats=evaluate_cut(obj,base,fixed)
        assert actual==expected,('Exact Dcode mismatch',str(path),canonical(add(actual,expected,-1))[:6])
        key=str(certpath.relative_to(ROOT));h=digest(expected)
        canon[key]=dict(symbols=['B']+PORTS,source_polynomial_sha256=h,monomials=canonical(expected))
        results.append(dict(file=str(path.relative_to(ROOT)),file_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),source_mode=obj.get('encoding',obj.get('source_mode')),positional_certificate=key,coefficient_monomials=len(actual),affine_source_rows_checked=rowchecks,source_polynomial_sha256=h,**stats))
    report=dict(status='PASS',method='Exact sparse polynomial equality in Z[B,beta,K0,MC,MF], with no numerical specialization.',original_source_sha256=sourcehash,original_source_gates=len(raw['source']),original_source_exact_zero_gates=zero,shifted_coordinate_count=len(raw['variables']),all_source_rows_checked=len(rows),circuits_verified=len(results),results=results,limitations='Certifies algebraic source compilation and diagonal corrections; does not prove the imported compiler semantics or Con(ZFC).')
    (ROOT/'audit/SHARED_SOURCE_SYMBOLIC_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'audit/CANONICAL_SOURCE_POLYNOMIALS.json').write_text(json.dumps(canon,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2))
    for r in results:print(r['file'],r['source_mode'],r['coefficient_monomials'],r['source_ancestor_operations'])
if __name__=='__main__':main()
