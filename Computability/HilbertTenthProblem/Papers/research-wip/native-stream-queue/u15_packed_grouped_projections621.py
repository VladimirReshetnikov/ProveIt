"""Share paid two-edge source-state sums in the complete U15 polynomial.

All seven affine projection identities and every downstream residual/output
are checked symbolically. The full polynomial equals the frozen646 parent
on all integer tuples, with the same ordinary input and supplied witnesses.
"""
if not __debug__:
    raise RuntimeError('u15_packed_grouped_projections621 requires enabled assertions')

import argparse
import ast
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import importlib.util
import json
from pathlib import Path
import random
from types import SimpleNamespace
import sys

PINS={
 'u15_packed_two_tape_history.py':'ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318',
 'u15_packed_state_relabel652.py':'cd3904fb083d1a254461ffde87636a6b9014bcdecb1db48cfcf2f30f41493879',
 'u15_packed_computed_truth647.py':'c363ea0679825559d5247608f748d877e75146dbb997b159db42294d9d676eb7',
 'u15_packed_composed_truth646.py':'d2ec28b859b43e93396f66395866b3f18098a959da22c1a5559fc4c1be2cdeb7',
}
BASELINE='u15_packed_two_tape_history.py'
PARENT='u15_packed_composed_truth646.py'
TRUTH='u15_packed_computed_truth647.py'
CUTS=('J','Q','S','N','Dir','W','WD')


def require(ok,message):
    if not ok:raise ValueError(message)


def flag(value,name='ordinary'):
    require(type(value) is bool,name+' must be Boolean');return value


def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
    if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def paths(root=None):
    here=Path(__file__).resolve().parent;root=here if root is None else Path(root).resolve()
    found={name:root/name if name==BASELINE or not (here/name).is_file() else here/name for name in PINS}
    for name,path in found.items():
        require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest()==PINS[name],'Pinned source changed or missing: '+name)
    return root,found


def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module);return module


def affine_forms(packet):
    rows={n:(op,a,b) for n,op,a,b in packet['source']};memo={}
    def add(a,b,sign=1):
        out=dict(a)
        for n,c in b.items():out[n]=out.get(n,0)+sign*c
        return {n:c for n,c in out.items() if c}
    def form(v):
        if type(v) is int:return {'':v} if v else {}
        if v in memo:return memo[v]
        if v not in rows:return {v:1}
        op,a,b=rows[v];a,b=form(a),form(b)
        if op in ('+','-'):result=add(a,b,1 if op=='+' else -1)
        elif set(a)<={''}:result={n:a.get('',0)*c for n,c in b.items() if a.get('',0)*c}
        elif set(b)<={''}:result={n:b.get('',0)*c for n,c in a.items() if b.get('',0)*c}
        else:raise ValueError('Projection is not affine')
        memo[v]=result;return result
    return {name:form(packet['registers'][name]) for name in CUTS}


def identity_certificate(old,new):
    require(old['parameters']==new['parameters'] and old['auxiliaries']==new['auxiliaries'],'Coordinate interface changed')
    require(old['rules']==new['rules'] and old['table']==new['table'],'Machine or rule indices changed')
    a,b=affine_forms(old),affine_forms(new)
    require(a==b,'An affine projection changed')
    weights={'J':[1]*29,**{n:[row[c] for row in old['rules']] for n,c in (('Q',0),('S',1),('N',2),('Dir',3),('W',4))},
             'WD':[row[3]*row[4] for row in old['rules']]}
    for name,cs in weights.items():
        expected={f'edge{i}':c for i,c in enumerate(cs) if c}
        if sum(cs):expected['']=-sum(cs)
        require(a[name]==expected,'Projection does not equal its literal table formula')
    nodes={}
    def intern(key):
        if key not in nodes:nodes[key]=len(nodes)
        return nodes[key]
    def source(packet):
        cuts={packet['registers'][name]:name for name in CUTS}
        require(len(cuts)==len(CUTS),'Projection cut registers collided')
        env={n:intern(('input',n)) for n in packet['parameters']+packet['auxiliaries']}
        def get(v):return env[v] if type(v) is str else intern(('constant',v))
        known=set(env)
        for name,op,a,b in packet['polynomial_source']:
            require(name not in known and op in ('+','-','*'),'Malformed complete arithmetic source')
            require(all(type(v) is int or type(v) is str and v in known for v in (a,b)),'Unpaid or inexact source operand')
            x,y=get(a),get(b)
            if op in ('+','*') and x>y:x,y=y,x
            env[name]=intern(('cut',cuts[name])) if name in cuts else intern((op,x,y))
            known.add(name)
        pairs=[(get(x),get(y)) for x,y in packet['comparisons']]
        public={name:get(v) for name,v in packet['registers'].items()}
        return pairs,public,get(packet['output'])
    x,y=source(old),source(new)
    require(x==y,'A downstream residual, semantic register or full output changed after proven cuts')
    return dict(exact_affine_forms=a,proved_projection_cuts=list(CUTS),identical_residuals=len(x[0]),
                identical_semantic_registers=len(x[1]),complete_polynomial_identity=True,expression_nodes=len(nodes))


@lru_cache(None)
def _bundle(root_text,path_texts):
    root,found=paths(root_text)
    require(tuple(str(found[name]) for name in PINS)==path_texts,'Pinned path selection changed')
    composed=load(found[PARENT],'_u15_grouped621_composed')
    _,oldbundle=composed._context(root)
    base=oldbundle['baseline'];relabel=oldbundle['relabel'];truth=oldbundle['truth']
    groups=tuple(tuple(i for i,row in enumerate(base.RULES) if row[0]==q) for q in range(15))
    require(sorted(map(len,groups))==[1]+[2]*14,'Expected fourteen pairs and one singleton')
    pair_groups=tuple(group for group in groups if len(group)==2)
    class GroupedDAG(base.DAG):
        def __init__(self):
            super().__init__();self.source_groups=[]
            for ids in pair_groups:
                value=super().add(*(f'edge{i}' for i in ids));self.source_groups.append((ids,value))
        def add(self,*terms):
            if len(terms)>1 and all(type(v) is str and v.startswith('edge') and v[4:].isdigit() for v in terms):
                active=list(terms)
                for ids,value in self.source_groups:
                    group=[f'edge{i}' for i in ids]
                    if all(active.count(n)==1 for n in group):
                        first=min(active.index(n) for n in group)
                        active=[n for n in active if n not in group];active.insert(first,value)
                terms=tuple(active)
            return super().add(*terms)
    modified=SimpleNamespace(**dict(base.__dict__,DAG=GroupedDAG))
    raw,ordinary=relabel.variant(modified,ast.parse(found[BASELINE].read_bytes()),composed.SWAP)
    grouped={False:raw,True:ordinary}
    adapter=SimpleNamespace(build=lambda ordinary=False:deepcopy(grouped[flag(ordinary)]),finish=base.finish)
    env=dict(truth.__dict__,_parent_module=lambda:adapter,PARENT_SHA256=PINS[BASELINE],
             PARENT_PACKET_SHA256=tuple(truth._packet_hash(grouped[o]) for o in (False,True)))
    tree=ast.parse(found[TRUTH].read_bytes())
    definitions=[deepcopy(next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name==name)) for name in ('_tagged','_child')]
    module=ast.Module(body=definitions,type_ignores=[]);ast.fix_missing_locations(module)
    exec(compile(module,'<pinned truth transforms on grouped relabel source>','exec'),env)
    packets={};certificates={};parents={}
    for ordinary in (False,True):
        p=deepcopy(env['_child'](ordinary));old=composed.build(ordinary,root=root)
        # These new schedules are compared directly with the complete646 parent;
        # inherited graph-parent descriptors are not current-source provenance.
        for key in ('parent_source_sha256','parent_packet_sha256','baseline_relation','graph_relation',
                    'positive_graph_helper_domain','baseline_native_source_sha256'):
            p.pop(key,None)
        p.update(kind='grouped_computed_truth',grouped_projection_compiler=True,
            grouping_pairs=[list(g) for g in pair_groups],projection_cuts=list(CUTS),
            canonical_parent={'file':PARENT,'sha256':PINS[PARENT]},
            source_lineage={name:sha for name,sha in PINS.items()},
            parent_relation='Exact complete polynomial identity on all integer supplied assignments, including signed tuples; same parameters and supplied witnesses.',
            scope='Complete first-halt polynomial with ordinary input on unchanged valid fixed-program slices; source sharing only, no new87 bound.')
        cert=identity_certificate(old,p)
        for section in ('certificate','polynomial'):
            require(old['ledger'][section]['operations']==p['ledger'][section]['operations']+25,'Expected25 saved operations')
            require(old['ledger'][section]['A']==p['ledger'][section]['A']+25,'Expected25 saved additions')
            require(old['ledger'][section]['M']==p['ledger'][section]['M'],'Multiplication count changed')
        for key in ('equations','positive_witnesses','formal_degree_upper_bound','exact_degree_claimed'):
            require(old['ledger'][key]==p['ledger'][key],'Nonarithmetic interface ledger changed')
        require(p['ledger']['polynomial']['operations']==(621 if ordinary else 378),'Unexpected final operation count')
        packets[ordinary]=p;parents[ordinary]=old;certificates[ordinary]=cert
    return dict(packets=packets,parents=parents,certificates=certificates,composed=composed,truth=truth,base=base)


def _context(root=None):
    root,found=paths(root);return root,_bundle(str(root),tuple(str(found[name]) for name in PINS))


def build(ordinary=False,*,root=None):
    ordinary=flag(ordinary);_,bundle=_context(root);return deepcopy(bundle['packets'][ordinary])


def canonical_parent(ordinary=False,*,root=None):
    ordinary=flag(ordinary);_,bundle=_context(root);return deepcopy(bundle['parents'][ordinary])


def checked(packet,*,root=None):
    _,bundle=_context(root)
    require(type(packet) is dict,'Canonical compiler packet required');ordinary=flag(packet.get('ordinary'))
    require(exact(packet,bundle['packets'][ordinary]),'Noncanonical grouped compiler packet');return packet


def polynomial_source(packet,*,root=None):return deepcopy(checked(packet,root=root)['polynomial_source'])


def evaluate(packet,values,*,signed=False,root=None):
    p=checked(packet,root=root);_,bundle=_context(root);t=bundle['truth']
    v=t._assignment(p,values,signed);return t._execute(p['polynomial_source'],v)[p['output']]


def identity(packet,values,*,signed=False,root=None):
    p=checked(packet,root=root);_,bundle=_context(root);t=bundle['truth'];v=t._assignment(p,values,signed)
    old=bundle['parents'][p['ordinary']]
    newenv=t._execute(p['polynomial_source'],v);oldenv=t._execute(old['polynomial_source'],v)
    require(newenv[p['output']]==oldenv[old['output']],'Complete polynomial identity failed')
    before=[t._at(oldenv,a)-t._at(oldenv,b) for a,b in old['comparisons']]
    after=[t._at(newenv,a)-t._at(newenv,b) for a,b in p['comparisons']]
    require(before==after,'A comparison residual changed')
    return dict(output=newenv[p['output']],residuals=after)


def verify(root=None):
    root,bundle=_context(root);rng=random.Random(62120261002);counts=Counter();records=[]
    require('context' not in globals(),'Private cache holder must not have a public alias')
    counts['unexposed_cache_holder_checks']=1
    def reject(f):
        try:f()
        except (ValueError,TypeError,KeyError):counts['guard_rejections']+=1;return
        raise AssertionError('Malformed input accepted')
    for ordinary in (False,True):
        p=build(ordinary,root=root);old=canonical_parent(ordinary,root=root)
        records.append(dict(ordinary=ordinary,ledger=p['ledger'],parent_ledger=old['ledger'],
                            identity=bundle['certificates'][ordinary],compiler=p))
        for case in range(64):
            signed=case>=32
            v={n:rng.randrange(-3,5) if signed else rng.randrange(1,6) for n in p['parameters']+p['auxiliaries']}
            if not ordinary and case<4:v.update(L0=case%2,R0=case//2)
            proof=identity(p,v,signed=signed,root=root)
            require(proof['output']==evaluate(p,v,signed=signed,root=root),'Public evaluator changed output')
            counts['complete_polynomial_identities']+=1;counts['signed_identities']+=signed
            counts['individual_residual_identities']+=len(proof['residuals'])
        v={n:1 for n in p['parameters']+p['auxiliaries']}
        for n in v:
            for bad in (True,1.0,0 if ordinary or n in p['auxiliaries'] else -1):
                values=dict(v);values[n]=bad
                reject(lambda values=values:evaluate(p,values,root=root))
        for field in p:
            bad=deepcopy(p);del bad[field];reject(lambda bad=bad:checked(bad,root=root))
        for field in ('source','polynomial_source'):
            for i,row in enumerate(p[field]):
                for j in (2,3):
                    if type(row[j]) is int:
                        for badvalue in (float(row[j]),bool(row[j])):
                            bad=deepcopy(p);changed=list(row);changed[j]=badvalue;bad[field][i]=tuple(changed)
                            reject(lambda bad=bad:checked(bad,root=root))
        for badflag in (0,1,1.0,None,'yes'):
            reject(lambda badflag=badflag:build(badflag,root=root))
            reject(lambda badflag=badflag:canonical_parent(badflag,root=root))
            reject(lambda badflag=badflag:evaluate(p,v,signed=badflag,root=root))
        for badvalues in (dict(v,extra=1),{n:a for n,a in v.items() if n!='edge0'}):
            reject(lambda badvalues=badvalues:evaluate(p,badvalues,root=root))
        exposed=build(ordinary,root=root);exposed['source'].clear();exposed['registers'].clear();exposed['ledger'].clear()
        require(exact(build(ordinary,root=root),p),'Public packet poisoned cache');counts['defensive_copy_checks']+=1
        exposed=canonical_parent(ordinary,root=root);exposed['source'].clear();exposed['ledger'].clear()
        require(exact(canonical_parent(ordinary,root=root),old),'Public parent poisoned cache');counts['defensive_copy_checks']+=1
        exposed=polynomial_source(p,root=root);exposed.clear()
        require(polynomial_source(p,root=root)==p['polynomial_source'],'Public source poisoned cache');counts['defensive_copy_checks']+=1
    # Cold parents must isolate even no-file and foreign-root loader stubs.
    original=sys.modules.get('u15_raw_half_tape_loader')
    try:
        for origin in (None,'/foreign/u15_raw_half_tape_loader.py'):
            fake=SimpleNamespace(build=lambda *a,**kw:(_ for _ in ()).throw(AssertionError('foreign loader was used')))
            if origin is not None:fake.__file__=origin
            sys.modules['u15_raw_half_tape_loader']=fake
            _bundle.cache_clear()
            require(build(True,root=root)['ledger']['polynomial']['operations']==621,'Cold compiler changed')
            require(sys.modules['u15_raw_half_tape_loader'] is fake,'Caller module was not restored')
            counts['cold_import_isolation_checks']+=1
    finally:
        if original is None:sys.modules.pop('u15_raw_half_tape_loader',None)
        else:sys.modules['u15_raw_half_tape_loader']=original
    return dict(status='PASS_GROUPED_PROJECTIONS621',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      pins=PINS,counts=dict(counts),forms=records,
      scope='All-value complete polynomial identity with frozen646; exact seven affine cuts and identical downstream residual/output DAGs. Same positive witnesses, ordinary inputs and valid program slices. No new87 bound.')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path);ap.add_argument('--write',action='store_true');a=ap.parse_args()
    result=verify(a.root);path=Path(__file__).with_suffix('.json');wire=json.dumps(result,indent=2)+'\n'
    if a.write:path.write_text(wire)
    else:require(exact(json.loads(path.read_text()),json.loads(wire)),'Saved receipt differs')
    print(json.dumps({k:result[k] for k in ('status','counts')},indent=2))
    print([f['ledger'] for f in result['forms']])
