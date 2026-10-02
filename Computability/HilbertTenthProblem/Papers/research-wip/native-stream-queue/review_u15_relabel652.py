"""Independent exact-source, signed-SOS and public-API review of U15 relabel652."""
import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys
import tempfile
import types

PARENT_SHA='ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318'

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def execute(rows,values):
    env=dict(values)
    for name,op,a,b in rows:
        assert name not in env
        a=env[a] if type(a) is str else a;b=env[b] if type(b) is str else b
        assert type(a) is int and type(b) is int
        env[name]={'*':lambda:a*b,'+':lambda:a+b,'-':lambda:a-b}[op]()
    return env

def value(env,x):return env[x] if type(x) is str else x

def residuals(p,env):return [value(env,a)-value(env,b) for a,b in p['comparisons']]

def exact_residual_dags(old,new):
    # Shared interning gives complete finite proof objects without expanding powers.
    terms={}
    def term(kind,*args):
        key=(kind,*args)
        if key not in terms:terms[key]=len(terms)
        return terms[key]
    def source(p):
        env={n:term('input',n) for n in p['parameters']+p['auxiliaries']}
        def get(v):return env[v] if type(v) is str else term('integer',v)
        for name,op,a,b in p['source']:
            a,b=get(a),get(b)
            if op in ('+','*'):a,b=sorted((a,b))
            env[name]=term(op,a,b)
        return [(get(a),get(b)) for a,b in p['comparisons']]
    x,y=source(old),source(new)
    changed=[i for i,(a,b) in enumerate(zip(x,y)) if a!=b]
    assert len(x)==len(y) and changed==[old.get('loader_comparison_count',0)+2]
    return len(x)-1

def verify(module_path,root):
    module_path=Path(module_path).resolve();root=Path(root).resolve()
    assert hashlib.sha256((root/'u15_packed_two_tape_history.py').read_bytes()).hexdigest()==PARENT_SHA
    mod=load(module_path,'independent_u15_relabel_target')
    counts=Counter();rng=random.Random(20261002652)
    def reject(f):
        try:f()
        except (ValueError,TypeError,KeyError):counts['malformed_rejections']+=1;return
        raise AssertionError('Malformed public input accepted')
    with mod.parent_module(root) as (parent,tree,sha):
        for ordinary in (False,True):
            old=parent.build(ordinary);new=mod.build(ordinary,root=root)
            assert new['parameters']==old['parameters'] and new['auxiliaries']==old['auxiliaries']
            assert new['table']==old['table']
            assert new['rules']==tuple((mod.SWAP[q],s,mod.SWAP[n],d,w) for q,s,n,d,w in old['rules'])
            counts['rules']+=len(old['rules'])
            counts['exact_unchanged_residual_dags']+=exact_residual_dags(old,new)
            state=old.get('loader_comparison_count',0)+2
            for packet in (old,new):
                ops=Counter(row[1] for row in packet['polynomial_source'])
                assert sum(ops.values())==packet['ledger']['polynomial']['operations']
                assert ops['*']==packet['ledger']['polynomial']['M']
                assert ops['+']+ops['-']==packet['ledger']['polynomial']['A']
            assert len(old['polynomial_source'])==len(new['polynomial_source'])+1
            assert new['ledger']['polynomial']['A']==old['ledger']['polynomial']['A']
            for case in range(48):
                signed=case>=24
                values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in old['parameters']+old['auxiliaries']}
                if not ordinary and case<4:values['L0']=case%2;values['R0']=case//2
                a=execute(old['polynomial_source'],values);b=execute(new['polynomial_source'],values)
                ra,rb=residuals(old,a),residuals(new,b)
                B=value(a,old['registers']['B']);P=value(a,old['registers']['P'])
                E=lambda i:values['edge'+str(i)]-1
                changeQ=8*(E(2)+E(3)-E(18));changeN=8*(E(0)+E(23)-E(17))
                assert value(b,new['registers']['Q'])-value(a,old['registers']['Q'])==changeQ
                assert value(b,new['registers']['N'])-value(a,old['registers']['N'])==changeN
                delta=B*changeN-changeQ+8*P
                assert all(y==x+(delta if i==state else 0) for i,(x,y) in enumerate(zip(ra,rb)))
                assert a[old['output']]==sum(r*r for r in ra)
                assert b[new['output']]==sum(r*r for r in rb)
                correction=b[new['output']]-a[old['output']]
                assert correction==delta*(2*ra[state]+delta)
                assert mod.evaluate(new,values,signed=signed,root=root)==b[new['output']]
                counts['complete_corrections']+=1;counts['signed_corrections']+=signed
                counts['individual_residual_comparisons']+=len(ra)
            values={n:1 for n in new['parameters']+new['auxiliaries']}
            for name in new['parameters']+new['auxiliaries']:
                for bad in (False,1.0):
                    altered=dict(values);altered[name]=bad
                    reject(lambda altered=altered:mod.evaluate(new,altered,root=root))
            for key in new:
                bad=deepcopy(new);del bad[key]
                reject(lambda bad=bad:mod.checked(bad,root=root))
            for field in ('source','polynomial_source','comparisons','parameters','auxiliaries'):
                bad=deepcopy(new);bad[field]=tuple(bad[field])
                reject(lambda bad=bad:mod.checked(bad,root=root))
            bad=dict(values,extra=1);reject(lambda:mod.evaluate(new,bad,root=root))
            bad=dict(values);del bad['edge0'];reject(lambda:mod.evaluate(new,bad,root=root))
            for signed in (0,1,None,1.0,'yes'):reject(lambda signed=signed:mod.evaluate(new,values,signed=signed,root=root))
            p=mod.build(ordinary,root=root);p['source'].clear();p['ledger']['polynomial']['M']=-1;p['registers'].clear()
            assert mod.build(ordinary,root=root)==new;counts['defensive_copy_checks']+=1
            rows=mod.polynomial_source(new,root=root);rows.clear()
            assert mod.polynomial_source(new,root=root)==new['polynomial_source'];counts['defensive_copy_checks']+=1
    # Full type and warm-root guard checks, distinct from source algebra.
    for flag in (0,1,None,1.0,'yes'):reject(lambda flag=flag:mod.build(flag,root=root))
    with tempfile.TemporaryDirectory() as temporary:
        changed=Path(temporary)/'u15_packed_two_tape_history.py'
        changed.write_bytes((root/changed.name).read_bytes()+b'\n')
        reject(lambda:mod.build(root=temporary))
    # Reproduce stale/foreign cached loader problem; fixed implementation must
    # isolate both a module without __file__ and one claiming another root.
    with mod.parent_module(root) as (parent,_,_):loader_packet=parent.loader.build(False)
    i=next(i for i,row in enumerate(loader_packet['source']) if row[0]=='raw_Q_term')
    row=list(loader_packet['source'][i]);row[2]='program_B';loader_packet['source'][i]=tuple(row)
    original=sys.modules.get('u15_raw_half_tape_loader')
    try:
        for file in (None,'/different/project/u15_raw_half_tape_loader.py'):
            fake=types.ModuleType('u15_raw_half_tape_loader');fake.build=lambda scaled=False:deepcopy(loader_packet)
            if file is not None:fake.__file__=file
            sys.modules['u15_raw_half_tape_loader']=fake
            cold=load(module_path,'cold_relabel_test')
            p=cold.build(True,root=root)
            assert next(r for r in p['source'] if r[0]=='input__raw_Q_term')[2]=='program_A'
            assert sys.modules['u15_raw_half_tape_loader'] is fake
            counts['cold_import_isolation_checks']+=1
    finally:
        if original is None:sys.modules.pop('u15_raw_half_tape_loader',None)
        else:sys.modules['u15_raw_half_tape_loader']=original
    receipt=json.loads(module_path.with_suffix('.json').read_text())
    assert receipt['source_sha256']==hashlib.sha256(module_path.read_bytes()).hexdigest()
    return {'status':'PASS','source_sha256':receipt['source_sha256'],'parent_sha256':PARENT_SHA,
            'counts':dict(counts),'scope':'Independent structural residual identities, signed full SOS correction, unchanged ports and rules, public guards/cache isolation. Positive-zero equivalence is separately proved in companion review; no materialized native Pell zero.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--module',type=Path,required=True);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);a=ap.parse_args()
    result=verify(a.module,a.root);wire=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(wire)
    print(wire)
