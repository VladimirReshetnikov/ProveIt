"""Independent exact-affine and complete-DAG review of U15 grouped621.

Only the final JSON requested at the command line is written. All compiler
sources and receipts are read-only; roots and source paths are explicit.
"""
import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys
from types import ModuleType

SOURCE_SHA = '8cadeb24c695b1956cd5cb25f93d41261065ddc45c116d7c9b0d0e3d7e4906d3'
PARENT_SHA = 'd2ec28b859b43e93396f66395866b3f18098a959da22c1a5559fc4c1be2cdeb7'
CUTS = ('J', 'Q', 'S', 'N', 'Dir', 'W', 'WD')
PAIRS = tuple((i, i+1) for i in range(0,18,2)) + tuple((i,i+1) for i in range(19,29,2))


def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def affine_vectors(packet):
    # Coordinates are the 29 positive edge hats followed by the constant 1.
    # A projection containing another input or variable product is rejected.
    rows={name:(op,a,b) for name,op,a,b in packet['source']}
    memo={}
    def form(x):
        if type(x) is int:return (0,)*29+(x,)
        if x in memo:return memo[x]
        if x.startswith('edge') and x[4:].isdigit():
            i=int(x[4:]);assert 0<=i<29
            return tuple(int(j==i) for j in range(30))
        op,a,b=rows[x];av,bv=form(a),form(b)
        if op=='+':value=tuple(a+b for a,b in zip(av,bv))
        elif op=='-':value=tuple(a-b for a,b in zip(av,bv))
        elif not any(av[:29]):value=tuple(av[29]*b for b in bv)
        else:
            assert not any(bv[:29]);value=tuple(bv[29]*a for a in av)
        memo[x]=value;return value
    out={name:form(packet['registers'][name]) for name in CUTS}
    rules=packet['rules']
    for name,column in zip(CUTS,(None,0,1,2,3,4,None)):
        weights=([1]*29 if name=='J' else [r[3]*r[4] for r in rules] if name=='WD' else [r[column] for r in rules])
        assert out[name]==tuple(weights)+(-sum(weights),)
    return out


def circuit_fingerprints(packet, nodes):
    # Shared structural interning is exact, without hash-digest equality as a
    # mathematical assumption. Cut names stand for proved affine identities.
    def node(parts):
        if parts not in nodes:nodes[parts]=len(nodes)
        return nodes[parts]
    e={n:node(('var',n)) for n in packet['parameters']+packet['auxiliaries']}
    cut={packet['registers'][name]:name for name in CUTS}
    assert len(cut)==7
    def at(x):return e[x] if type(x) is str else node(('constant',x))
    for n,op,a,b in packet['polynomial_source']:
        aa,bb=at(a),at(b)
        if op in ('+','*'):aa,bb=sorted((aa,bb))
        e[n]=node(('projection',cut[n])) if n in cut else node((op,aa,bb))
    return ([tuple(at(x) for x in row) for row in packet['comparisons']],
            {n:at(x) for n,x in packet['registers'].items()},
            {n:at(x) for n,x in packet['tag_registers'].items()},
            {n:at(n) for n in ('native__F0','native__F1','native__F2')},at(packet['output']))


def inspect_source(p):
    # Independently rebuild the entire finalizer, then account for every gate.
    full=list(p['source']);squares=[]
    for i,(a,b) in enumerate(p['comparisons']):
        n=f'poly_res{i}';s=f'poly_sq{i}'
        full.extend([(n,'-',a,b),(s,'*',n,n)]);squares.append(s)
    out=squares[0]
    for i,s in enumerate(squares[1:],1):
        n=f'poly_sum{i}';full.append((n,'+',out,s));out=n
    assert exact(full,p['polynomial_source']) and out==p['output']
    inputs=p['parameters']+p['auxiliaries'];known=set(inputs)
    assert len(known)==len(inputs)
    degree={n:0 if n in p['fixed_parameters'] else 1 for n in inputs}
    for n,op,a,b in full:
        assert type(n) is str and n not in known and op in ('+','-','*')
        assert all(type(x) is int or type(x) is str and x in known for x in (a,b))
        aa=degree[a] if type(a) is str else 0;bb=degree[b] if type(b) is str else 0
        degree[n]=aa+bb if op=='*' else max(aa,bb);known.add(n)
    assert degree[out]==1936
    live={out}
    for n,op,a,b in reversed(full):
        if n in live:live.update(x for x in (a,b) if type(x) is str)
    assert all(n in live for n,op,a,b in full)
    for name,rows in (('certificate',p['source']),('polynomial',full)):
        assert p['ledger'][name]=={'operations':len(rows),'M':sum(op=='*' for n,op,a,b in rows),'A':sum(op!='*' for n,op,a,b in rows)}
    assert p['ledger']['equations']==len(p['comparisons']) and p['ledger']['positive_witnesses']==len(p['auxiliaries'])


def execute(rows,values):
    e=dict(values)
    for n,op,a,b in rows:
        aa=e[a] if type(a) is str else a;bb=e[b] if type(b) is str else b
        e[n]={'*':lambda:aa*bb,'+':lambda:aa+bb,'-':lambda:aa-bb}[op]()
    return e


def at(e,x):return e[x] if type(x) is str else x


def verify(source,root):
    assert hashlib.sha256(source.read_bytes()).hexdigest()==SOURCE_SHA
    parent=source.parent/'u15_packed_composed_truth646.py'
    if not parent.is_file():parent=root/parent.name
    assert hashlib.sha256(parent.read_bytes()).hexdigest()==PARENT_SHA
    m=module(source,'_independent621');oldm=module(parent,'_independent646_for621')
    assert not hasattr(m,'context'),'Mutable holder must remain private'
    counts=Counter();rng=random.Random(16210378);records=[]
    def reject(f):
        try:f()
        except (TypeError,ValueError,KeyError):counts['malformed_rejections']+=1;return
        raise AssertionError('Malformed public input accepted')
    for ordinary in (False,True):
        p=m.build(ordinary,root=root);old=oldm.build(ordinary,root=root)
        assert exact(m.canonical_parent(ordinary,root=root),old)
        assert tuple(tuple(x) for x in p['grouping_pairs'])==PAIRS
        assert p['parameters']==old['parameters'] and p['auxiliaries']==old['auxiliaries']
        assert p['rules']==old['rules'] and p['table']==old['table']
        assert affine_vectors(p)==affine_vectors(old);counts['exact_affine_projections']+=7
        nodes={};fingerprint=circuit_fingerprints(p,nodes)
        assert fingerprint==circuit_fingerprints(old,nodes)
        counts['exact_residual_pair_DAGs']+=len(p['comparisons'])
        counts['exact_semantic_register_DAGs']+=len(p['registers'])+len(p['tag_registers'])+3
        counts['exact_complete_output_DAGs']+=1
        inspect_source(p);counts['source_finalizer_ledger_degree_liveness_checks']+=1
        for section in ('certificate','polynomial'):
            assert old['ledger'][section]['A']-p['ledger'][section]['A']==25
            assert old['ledger'][section]['M']==p['ledger'][section]['M']
        for k in ('equations','positive_witnesses','formal_degree_upper_bound','exact_degree_claimed'):
            assert old['ledger'][k]==p['ledger'][k]
        # Count paid additions in each emitted prefix, not by an informal
        # replacement count. All 14 first pair gates must feed the final SOS.
        def prefix_a(q,cut):
            idx=next(i for i,row in enumerate(q['source']) if row[0]==q['registers'][cut])
            return sum(row[1]!='*' for row in q['source'][:idx+1])
        savings=[prefix_a(old,c)-prefix_a(p,c) for c in CUTS]
        assert savings==[0,13,13,15,19,23,25]
        counts['exact_projection_prefix_costs']+=7
        edge_rows=[r for r in p['source'] if r[1]=='+' and {r[2],r[3]} in [{f'edge{i}',f'edge{j}'} for i,j in PAIRS]]
        assert len(edge_rows)==14;counts['paid_pair_gates']+=14
        names=p['parameters']+p['auxiliaries']
        for case in range(48):
            signed=case>=24
            v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in names}
            if not ordinary and case<4:v.update(L0=case%2,R0=case//2)
            a=execute(p['polynomial_source'],v);b=execute(old['polynomial_source'],v)
            residuals=[at(a,x)-at(a,y) for x,y in p['comparisons']]
            assert residuals==[at(b,x)-at(b,y) for x,y in old['comparisons']]
            assert sum(r*r for r in residuals)==a[p['output']]==b[old['output']]
            assert m.evaluate(p,v,signed=signed,root=root)==a[p['output']]
            assert m.identity(p,v,signed=signed,root=root)=={'output':a[p['output']],'residuals':residuals}
            counts['independent_integer_full_SOS_checks']+=1
            counts['signed_cases']+=signed;counts['individual_residual_checks']+=len(residuals)
        # Algebraic identity really extends beyond the integer evaluator domain.
        for case in range(4):
            v={n:Fraction(rng.randrange(-2,4),2) for n in names}
            a=execute(p['polynomial_source'],v);b=execute(old['polynomial_source'],v)
            assert a[p['output']]==b[old['output']]
            counts['rational_full_polynomial_checks']+=1
        one={n:1 for n in names}
        for n in names:
            for bad in (True,1.0,Fraction(1),0 if ordinary or n in p['auxiliaries'] else -1):
                v=dict(one);v[n]=bad;reject(lambda v=v:m.evaluate(p,v,root=root))
        for flag in (0,1,1.0,None,'True'):
            for f in (m.build,m.canonical_parent):reject(lambda f=f,flag=flag:f(flag,root=root))
            reject(lambda flag=flag:m.evaluate(p,one,signed=flag,root=root))
            reject(lambda flag=flag:m.identity(p,one,signed=flag,root=root))
        reject(lambda:m.evaluate(p,dict(one,extra=1),root=root))
        missing=dict(one);del missing['edge0'];reject(lambda:m.evaluate(p,missing,root=root))
        for field in p:
            bad=deepcopy(p);del bad[field];reject(lambda bad=bad:m.checked(bad,root=root))
        for field in ('source','polynomial_source'):
            bad=deepcopy(p);bad[field]=tuple(bad[field]);reject(lambda bad=bad:m.checked(bad,root=root))
            for i,row in enumerate(p[field]):
                for slot in (2,3):
                    if type(row[slot]) is int:
                        for val in (bool(row[slot]),float(row[slot])):
                            bad=deepcopy(p);r=list(row);r[slot]=val;bad[field][i]=tuple(r)
                            reject(lambda bad=bad:m.checked(bad,root=root))
        bad=deepcopy(p);bad['polynomial_source'][-1]=(bad['output'],'-',0,0)
        reject(lambda:m.checked(bad,root=root));reject(lambda:m.evaluate(bad,one,root=root))
        for f in (m.build,m.canonical_parent):
            wanted=f(ordinary,root=root);changed=f(ordinary,root=root)
            changed['source'].clear();changed['ledger'].clear();changed['registers'].clear()
            assert exact(f(ordinary,root=root),wanted);counts['nested_defensive_copies']+=1
        rows=m.polynomial_source(p,root=root);rows.clear()
        assert exact(m.polynomial_source(p,root=root),p['polynomial_source']);counts['nested_defensive_copies']+=1
        records.append({'ordinary':ordinary,'ledger':p['ledger'],'affine_forms':affine_vectors(p),'prefix_savings':savings})
    # Cold import isolation, including caller-owned fake module restoration.
    key='u15_raw_half_tape_loader';prior=sys.modules.get(key);wanted=m.build(True,root=root)
    try:
        for origin in (None,'/unrelated/u15_raw_half_tape_loader.py'):
            fake=ModuleType(key)
            if origin:fake.__file__=origin
            fake.build=lambda *a,**k:(_ for _ in ()).throw(AssertionError('Foreign loader consumed'))
            sys.modules[key]=fake;m._bundle.cache_clear()
            assert exact(m.build(True,root=root),wanted) and sys.modules[key] is fake
            counts['cold_import_isolation_checks']+=1
    finally:
        if prior is None:sys.modules.pop(key,None)
        else:sys.modules[key]=prior
    return {'status':'PASS','source_sha256':SOURCE_SHA,'parent_sha256':PARENT_SHA,'counts':dict(counts),'forms':records,
            'scope':'Complete all-value polynomial identity by exact affine expansions and downstream DAGs; full source, costs, public guards and cache boundaries. No materialized native Pell witness; exact degree transfers from the reviewed parent proof.'}


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--source',type=Path,required=True);parser.add_argument('--root',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();result=verify(args.source.resolve(),args.root.resolve());args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'counts':result['counts']},indent=2))
