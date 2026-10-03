"""Guarded U15 B/J state relabel: complete 409/652-operation sources.

The baseline is read and SHA256 checked before importing it. Public packets
are defensive copies; default CLI replay is read-only. No search runs here.
"""
import ast
from contextlib import contextmanager
from copy import deepcopy
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
from functools import lru_cache
import random
import sys

PARENT_SHA256='ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318'
SWAP=(0,9,2,3,4,5,6,7,8,1,10,11,12,13,14)

def source_guard(root):
    path=(Path(__file__).resolve().parent if root is None else Path(root).resolve())/'u15_packed_two_tape_history.py'
    if hashlib.sha256(path.read_bytes()).hexdigest()!=PARENT_SHA256:
        raise ValueError('Pinned parent compiler changed')
    return path.parent

@contextmanager
def parent_module(root):
    root=source_guard(root);path=root/'u15_packed_two_tape_history.py'
    before=set(sys.modules);oldpath=list(sys.path)
    data=path.read_bytes();tree=ast.parse(data)
    name='_u15_packed_state_relabel652_parent'
    # Import the actual sibling sources even if a caller has loaded another
    # root's modules or installed stubs without __file__ under these names.
    sibling_names={p.stem for p in root.glob('*.py')}|{name}
    saved={n:sys.modules[n] for n in sibling_names if n in sys.modules}
    for n in sibling_names:sys.modules.pop(n,None)
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec)
    sys.path.insert(0,str(root));sys.modules[name]=m
    try:
        spec.loader.exec_module(m)
        yield m,tree,hashlib.sha256(data).hexdigest()
        assert path.read_bytes()==data,'parent changed during bounded experiment'
    finally:
        sys.path[:]=oldpath
        for key in sibling_names:sys.modules.pop(key,None)
        for key in set(sys.modules)-before:
            mod=sys.modules.get(key);filename=getattr(mod,'__file__',None)
            if filename and Path(filename).resolve().is_relative_to(root):
                sys.modules.pop(key,None)
        sys.modules.update(saved)


def variant(m,tree,codes):
    assert tuple(sorted(codes))==tuple(range(15)) and codes[0]==0
    env=dict(m.__dict__)
    env['RULES']=tuple((codes[q],s,codes[r],d,w) for q,s,r,d,w in m.RULES)
    f=deepcopy(next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='raw_build'))
    changes=[]
    for n in ast.walk(f):
        if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='mul' and len(n.args)==2:
            a,b=n.args
            if isinstance(a,ast.Constant) and type(a.value) is int and a.value==9 and isinstance(b,ast.Name) and b.id=='P':
                n.args[0]=ast.Constant(codes[9]);changes.append(n)
    assert len(changes)==1
    ast.fix_missing_locations(f);exec(compile(ast.Module(body=[f],type_ignores=[]),'<guarded copied raw_build>','exec'),env)
    # Copy the actual wrapper too, so loader gates and final SOS are all emitted.
    full=deepcopy(next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='_build'))
    ast.fix_missing_locations(full);exec(compile(ast.Module(body=[full],type_ignores=[]),'<guarded copied _build>','exec'),env)
    raw=env['_build'](False);ordinary=env['_build'](True)
    for p in (raw,ordinary):p['state_relabel']=list(codes)
    return raw,ordinary



@lru_cache(None)
def _bundle(root):
    # Private mutable cache; public packet access always copies.
    with parent_module(root) as (m,tree,sha):
        raw,ordinary=variant(m,tree,SWAP)
        return {False:raw,True:ordinary},m.exact,m.assignment,m.execute

def build(ordinary=False,*,root=None):
    if type(ordinary) is not bool:raise ValueError('ordinary must be Boolean')
    root=source_guard(root)
    return deepcopy(_bundle(str(root))[0][ordinary])

def checked(packet,*,root=None):
    root=source_guard(root)
    if type(packet) is not dict or type(packet.get('ordinary')) is not bool:
        raise ValueError('Canonical relabel packet required')
    canonical,exact,_,_=_bundle(str(root))
    if not exact(packet,canonical[packet['ordinary']]):
        raise ValueError('Noncanonical relabel packet')
    return packet

def evaluate(packet,values,*,signed=False,root=None):
    root=source_guard(root)
    p=checked(packet,root=root)
    _,_,assignment,execute=_bundle(str(root))
    v=assignment(p,values,signed)
    return execute(p['polynomial_source'],v)[p['output']]


def polynomial_source(packet,*,root=None):
    return deepcopy(checked(packet,root=root)['polynomial_source'])


def _symbolic_rows(old,new):
    """Exact expression DAG identities, modulo only commutative argument order."""
    nodes={}
    def intern(key):
        if key not in nodes:nodes[key]=len(nodes)
        return nodes[key]
    def source(packet):
        env={}
        def get(v):
            if type(v) is int:return intern(('constant',v))
            return env[v] if v in env else intern(('variable',v))
        for name,op,a,b in packet['source']:
            x,y=get(a),get(b)
            if op in ('+','*') and x>y:x,y=y,x
            env[name]=intern((op,x,y))
        return [(get(a),get(b)) for a,b in packet['comparisons']]
    a,b=source(old),source(new)
    index=old.get('loader_comparison_count',0)+2
    assert len(a)==len(b)
    assert all(x==y for i,(x,y) in enumerate(zip(a,b)) if i!=index)
    assert a[index]!=b[index]
    return dict(unchanged_comparisons=len(a)-1,state_comparison_index=index,
                shared_expression_nodes=len(nodes))


def _linear_columns(packet):
    rows={n:(op,a,b) for n,op,a,b in packet['source']};cache={}
    def add(a,b,sign=1):
        out=dict(a)
        for k,v in b.items():out[k]=out.get(k,0)+sign*v
        return {k:v for k,v in out.items() if v}
    def poly(v):
        if type(v) is int:return {'':v} if v else {}
        if v in cache:return cache[v]
        if v not in rows:return {v:1}
        op,x,y=rows[v];a,b=poly(x),poly(y)
        if op in ('+','-'):out=add(a,b,1 if op=='+' else -1)
        elif set(a)<={''}:out={k:a.get('',0)*c for k,c in b.items() if a.get('',0)*c}
        elif set(b)<={''}:out={k:b.get('',0)*c for k,c in a.items() if b.get('',0)*c}
        else:raise AssertionError('State form was not affine')
        cache[v]=out;return out
    return {n:poly(packet['registers'][n]) for n in ('Q','N')}


def verify(root=None):
    if not __debug__:raise RuntimeError('Assertions required for research replay')
    root=source_guard(root)
    with parent_module(root) as (m,tree,sha):
        originals={ordinary:m.build(ordinary) for ordinary in (False,True)}
        packets={ordinary:build(ordinary,root=root) for ordinary in (False,True)}
        rng=random.Random(6521502)
        counts=dict(actual_rules=0,adjacency_cases=0,unchanged_symbolic_comparisons=0,
                    exact_affine_state_differences=0,complete_offzero_corrections=0,
                    genuine_outer_AND_fixtures=0,public_guard_rejections=0,public_cache_copy_checks=0,cold_import_isolation_checks=0)
        for old,new in zip(m.RULES,packets[False]['rules']):
            q,s,r,d,w=old
            assert new==(SWAP[q],s,SWAP[r],d,w);counts['actual_rules']+=1
        assert tuple(sorted(SWAP))==tuple(range(15)) and SWAP[0]==0 and SWAP[9]==1
        for a,b in itertools.product(m.RULES,repeat=2):
            assert (a[2]==b[0])==(SWAP[a[2]]==SWAP[b[0]])
            counts['adjacency_cases']+=1
        symbolic={}
        def reject(f):
            try:f()
            except (ValueError,TypeError,KeyError):return
            raise AssertionError('Malformed public input accepted')
        for ordinary in (False,True):
            old,new=originals[ordinary],packets[ordinary]
            assert old['parameters']==new['parameters'] and old['auxiliaries']==new['auxiliaries']
            expected=652 if ordinary else 409
            assert new['ledger']['polynomial']['operations']==expected
            for part in ('certificate','polynomial'):
                assert old['ledger'][part]['operations']==new['ledger'][part]['operations']+1
                assert old['ledger'][part]['M']==new['ledger'][part]['M']+1
                assert old['ledger'][part]['A']==new['ledger'][part]['A']
            for k in ('equations','positive_witnesses','formal_degree_upper_bound','exact_degree_claimed'):
                assert old['ledger'][k]==new['ledger'][k]
            symbolic[ordinary]=_symbolic_rows(old,new)
            counts['unchanged_symbolic_comparisons']+=symbolic[ordinary]['unchanged_comparisons']
            a,b=_linear_columns(old),_linear_columns(new)
            for name,wanted in (('Q',{'':-8,'edge2':8,'edge3':8,'edge18':-8}),
                                ('N',{'':-8,'edge0':8,'edge23':8,'edge17':-8})):
                actual={k:b[name].get(k,0)-a[name].get(k,0) for k in set(a[name])|set(b[name])}
                actual={k:v for k,v in actual.items() if v}
                assert actual==wanted;counts['exact_affine_state_differences']+=1
            index=symbolic[ordinary]['state_comparison_index']
            for i in range(32):
                v={n:rng.randrange(-2,4) if i>=16 else rng.randrange(1,4)
                   for n in old['parameters']+old['auxiliaries']}
                oe=m.execute(old['polynomial_source'],v);ne=m.execute(new['polynomial_source'],v)
                B=m.get(oe,old['registers']['B']);P=m.get(oe,old['registers']['P'])
                E=lambda j:v['edge'+str(j)]-1
                delta=8*(B*(E(0)+E(23)-E(17))-(E(2)+E(3)-E(18))+P)
                R=m.get(oe,old['comparisons'][index][0])-m.get(oe,old['comparisons'][index][1])
                assert ne[new['output']]-oe[old['output']]==2*R*delta+delta*delta
                assert evaluate(new,v,signed=True,root=root)==ne[new['output']]
                counts['complete_offzero_corrections']+=1
            v={n:1 for n in new['parameters']+new['auxiliaries']}
            for n in v:
                for badval in (True,1.0,0 if n in new['auxiliaries'] or ordinary else -1):
                    bad=dict(v);bad[n]=badval
                    reject(lambda bad=bad:evaluate(new,bad,root=root));counts['public_guard_rejections']+=1
            for field in ('source','polynomial_source'):
                for i,row in enumerate(new[field]):
                    for slot in (2,3):
                        if type(row[slot]) is int:
                            for corrupted in ([float(row[slot]),bool(row[slot])] if row[slot] in (0,1) else [float(row[slot])]):
                                bad=deepcopy(new);rr=list(row);rr[slot]=corrupted;bad[field][i]=tuple(rr)
                                reject(lambda bad=bad:checked(bad,root=root));counts['public_guard_rejections']+=1
            for key,val in (('state_relabel',[float(x) for x in SWAP]),('ordinary',int(ordinary)),
                            ('source',tuple(new['source']))):
                bad=deepcopy(new);bad[key]=val
                reject(lambda bad=bad:checked(bad,root=root));counts['public_guard_rejections']+=1
            for badflag in (0,1,'yes',None):
                reject(lambda badflag=badflag:build(badflag,root=root));counts['public_guard_rejections']+=1
                reject(lambda badflag=badflag:evaluate(new,v,signed=badflag,root=root));counts['public_guard_rejections']+=1
            changed=build(ordinary,root=root);changed['rules']=(('poison',),);changed['ledger']['equations']=999
            assert m.exact(build(ordinary,root=root),new);counts['public_cache_copy_checks']+=1
            exposed=polynomial_source(new,root=root);exposed.pop()
            assert polynomial_source(new,root=root)==new['polynomial_source'];counts['public_cache_copy_checks']+=1
        # A cold cache must not trust a preloaded loader even when the parent
        # file's bytes are correct. Restore the caller's exact module object.
        import types
        loader_name='u15_raw_half_tape_loader'
        real_loader=sys.modules[loader_name]
        poison=deepcopy(m.loader.build(False))
        slot=next(i for i,r in enumerate(poison['source']) if r[0]=='raw_Q_term')
        altered=list(poison['source'][slot]);altered[2]='program_B';poison['source'][slot]=tuple(altered)
        for foreign_file in (None,'/foreign/root/u15_raw_half_tape_loader.py'):
            fake=types.ModuleType(loader_name)
            if foreign_file is not None:fake.__file__=foreign_file
            fake.build=lambda scaled=False:deepcopy(poison)
            _bundle.cache_clear();sys.modules[loader_name]=fake
            try:
                rebuilt=build(True,root=root)
                assert m.exact(rebuilt,packets[True])
                assert sys.modules[loader_name] is fake
                counts['cold_import_isolation_checks']+=1
            finally:
                sys.modules[loader_name]=real_loader;_bundle.cache_clear()
        fixtures=[];raw=packets[False]
        prefix=[row for row in raw['source'] if not row[0].startswith('native__')]
        for L,R in itertools.product(range(16),range(12)):
            result=m.trace(L,R,40)
            if result is not None:
                v,meta=m.outer_fixture(L,R,40)
                env=m.execute(prefix,v)
                assert all(m.get(env,a)==m.get(env,b) for a,b in raw['comparisons'][:5])
                assert m.get(env,raw['registers']['Hjoin']) & m.get(env,raw['registers']['Mjoin']) == m.get(env,raw['registers']['Zjoin'])
                fixtures.append(dict(L=L,R=R,duration=meta['t'],original_final=meta['final'],
                    relabelled_final=(SWAP[meta['final'][0]],)+tuple(meta['final'][1:])))
                counts['genuine_outer_AND_fixtures']+=1
        return dict(status='PASS',parent_sha256=sha,state_relabel=list(SWAP),counts=counts,
                    ledgers=[dict(ordinary=o,ledger=packets[o]['ledger']) for o in (False,True)],
                    symbolic_source_audit=[dict(ordinary=o,**symbolic[o]) for o in (False,True)],
                    complete_raw_compiler=packets[False],complete_ordinary_compiler=packets[True],
                    outer_examples=fixtures,
                    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    scope='Complete fixed-arity sources with the same supplied positive zero sets as the pinned 410/653 baseline (raw half-tape parameters natural). Exact off-zero SOS correction; finite outer fixtures do not materialize native Pell coordinates. The baseline formal degree bound is retained, with no exact degree claim.')


def main():
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path);ap.add_argument('--write',action='store_true');a=ap.parse_args()
    result=verify(a.root);path=Path(__file__).with_suffix('.json');wire=json.dumps(result,indent=2)+'\n'
    if a.write:path.write_text(wire)
    else:
        _,exact,_,_=_bundle(str(source_guard(a.root)))
        assert exact(json.loads(path.read_text()),json.loads(wire))
    print(json.dumps({k:result[k] for k in ('status','parent_sha256','counts','ledgers','symbolic_source_audit')},indent=2))


if __name__=='__main__':main()
