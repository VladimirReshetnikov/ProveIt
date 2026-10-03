#!/usr/bin/env python3
"""Exact wire projection for external-horizon sparse lattice certificates."""
import argparse, hashlib, importlib.util, json
from pathlib import Path
import random, sys, tempfile, zipfile
from collections import defaultdict
from itertools import product

ARCHIVE_SHA='90c9dadeccad7c70c777b141b0c65029b992048fd69448f0f8e035ec522cdc68'
SOURCE_SHA='1c35e0104730dfe99c9be4c350b49d66646d8e0dd7c7580b262367f1070d02c8'

def exact(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,(list,tuple)):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def require(ok,msg):
    if not ok:raise AssertionError(msg)

def project(m,old):
    """Return actual substituted residuals, canonical tuple and restoration map.

    Generic fixed-initial-history only. Loader/observer circuits are not counted.
    No assumption about witness values is used in symbolic substitution.
    """
    defs=dict(zip(old.residual_names,old.residuals));expressions=[];values=[];names=[];removed=set()
    def substitute(p):
        out=m.Poly.constant(0)
        for mon,c in p.terms:
            term=m.Poly.constant(c)
            for index in mon:
                require(index>=0,'generic history has no free parameter wires')
                term=term*expressions[index]
            out=out+term
        return out
    for index,name in enumerate(old.names):
        eliminate=('.stream.' in name or '.mass.' in name or '.g.' in name and '.out.' in name
                   or '.sort.' in name and name.endswith(('.xmax','.zmax')))
        if eliminate:
            # Each selected wire has the exact defining row variable-expression.
            relation=defs[name];var=m.Poly.variable(index)
            require(dict(relation.terms).get((index,))==1,'wire leading coefficient')
            expression=var-relation
            require(all(i<index for mon,_ in expression.terms for i in mon),'definition not topological')
            expressions.append(substitute(expression));removed.add(name)
        else:
            expressions.append(m.Poly.variable(len(values)));values.append(old.values[index]);names.append(name)
    allrows=[substitute(r) for r in old.residuals]
    require(all(not r.terms for name,r in zip(old.residual_names,allrows) if name in removed),'discarded rows not identically zero')
    residuals=[r for name,r in zip(old.residual_names,allrows) if name not in removed]
    require(all(r.degree<=2 for r in residuals),'projection raised residual degree')
    rows=[[(substitute(x),substitute(z)) for x,z in row] for row in old.rows]
    return dict(names=names,values=values,residuals=residuals,restore=expressions,rows=rows,removed=sorted(removed))

def verify(archive):
    require(hashlib.sha256(Path(archive).read_bytes()).hexdigest()==ARCHIVE_SHA,'archive pin')
    with tempfile.TemporaryDirectory(prefix='sparse-projection-') as tmp:
        with zipfile.ZipFile(archive) as z:data=z.read('sparse-lattice-release/replay/core/sparse_mass.py')
        require(hashlib.sha256(data).hexdigest()==SOURCE_SHA,'source pin')
        path=Path(tmp)/'sparse_mass.py';path.write_bytes(data)
        spec=importlib.util.spec_from_file_location('sparse_projection_producer',path);m=importlib.util.module_from_spec(spec);sys.modules[spec.name]=m;spec.loader.exec_module(m)
        rng=random.Random(626801);counts=defaultdict(int);instances=[]
        def check(key,ok):require(ok,key);counts[key]+=1
        for K in (1,2):
            for seed in range(4):
                fibers=defaultdict(list)
                for key in product(range(K+1),repeat=3):fibers[sum(key)].append(key)
                table={}
                for f in fibers.values():
                    targets=f.copy();rng.shuffle(targets);table.update(zip(f,targets))
                rule=m.LocalTable.from_mapping(K,table)
                conf={0:(0,0,1),3:(1,0,0)} if seed%2 else {0:(1,1,1)}
                if seed==3:conf={-10**80:(1,0,0),10**80:(0,0,1)}
                for T,orthant in product((0,1,2),(False,True)):
                    old,meta=m.compile_history(rule,conf,T,orthant_exact=orthant);new=project(m,old)
                    M=meta['M'];S=(K+1)**3;wantv=T*(M*(S+7)+4*M*(M-1));wantr=T*(10*M+4*M*(M-1)+2*M*orthant)
                    check('literal_projected_counts',len(new['values'])==wantv and len(new['residuals'])==wantr)
                    check('natural_canonical_restoration',[p.evaluate(new['values']) for p in new['restore']]==old.values)
                    check('all_projected_rows_zero',all(r.evaluate(new['values'])==0 for r in new['residuals']))
                    check('row_alias_decoder_preserved',[[tuple(p.evaluate(new['values']) for p in record) for record in row] for row in new['rows']]==[[tuple(p.evaluate(old.values) for p in record) for record in row] for row in old.rows])
                    for _ in range(3):
                        v=[rng.randrange(-2,4) for _ in new['values']];restored=[p.evaluate(v) for p in new['restore']]
                        check('complete_signed_graph_identity',sum(r.evaluate(restored)**2 for r in old.residuals)==sum(r.evaluate(v)**2 for r in new['residuals']))
                    for i in range(len(new['values'])):
                        v=new['values'].copy();v[i]+=1
                        check('false_witness_mutation',any(r.evaluate(v) for r in new['residuals']))
                    instances.append(dict(K=K,M=M,T=T,orthant=orthant,old_V=len(old.values),old_R=len(old.residuals),V=wantv,R=wantr,max_degree=max((r.degree for r in new['residuals']),default=0),old_terms=sum(len(r.terms) for r in old.residuals),new_terms=sum(len(r.terms) for r in new['residuals'])))
        # Restricted-table contract and rejecting endpoint survive the same projection.
        rule=m.LocalTable.from_mapping(2,{k:k for k in product(range(3),repeat=3)})
        for T in (1,2,3):
            for endpoint in (None,{999:(1,0,0)}):
                old,meta=m.compile_history(rule,{0:(0,0,1)},T,endpoint=endpoint,allowed_inputs=[(0,0,0),(1,0,0),(0,0,1)])
                new=project(m,old);check('restricted_endpoint_zero_equivalence',old.validate_witness()==all(r.evaluate(new['values'])==0 for r in new['residuals']))
                check('restricted_actual_counts',len(new['values'])==T*10 and len(new['residuals'])==T*10+(2 if endpoint else 0))
        return dict(status='PASS',archive_sha256=ARCHIVE_SHA,producer_sha256=SOURCE_SHA,review_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),counts=dict(counts),instances=instances,
                    variables='T[M(S+7)+4M(M-1)]',residuals='T[10M+4M(M-1)]',saved_each='T[7M+M(M-1)]',
                    scope='Natural-zero bijection and exact graph SOS identity for fixed initial data and external T. Quadratic residuals retained. Orthant adds2MT rows. No gate saving, universal fixed-arity transfer, or optimality claim.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archive',required=True,type=Path);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.archive)
    if a.expect and not exact(r,json.loads(a.expect.read_text())):raise AssertionError('receipt mismatch')
    if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(r['counts'],sort_keys=True))
