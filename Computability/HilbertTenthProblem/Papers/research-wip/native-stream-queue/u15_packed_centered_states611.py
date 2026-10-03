"""Exact centered-state arithmetic sharing: complete U15 polynomials368/611.

The center is fixed at7. All supplied coordinates and complete polynomial
values are preserved; state projection registers are explicitly deviations.
"""
if not __debug__:raise RuntimeError('u15_packed_centered_states611 requires enabled assertions')
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
import sympy as sp

PARENT_FILE='u15_packed_grouped_projections621.py'
PARENT_SHA256='8cadeb24c695b1956cd5cb25f93d41261065ddc45c116d7c9b0d0e3d7e4906d3'
BASELINE_FILE='u15_packed_two_tape_history.py'
TRUTH_FILE='u15_packed_computed_truth647.py'
CENTER=7
COMMON_CUTS=('J','S','Dir','W','WD')


def _require(ok,message):
    if not ok:raise ValueError(message)


def _flag(value,name='ordinary'):
    _require(type(value) is bool,name+' must be Boolean');return value


def _exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(type(k) is str and _exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple):return len(a)==len(b) and all(_exact(x,y) for x,y in zip(a,b))
    return a==b


def _source_guard(root=None):
    here=Path(__file__).resolve().parent;root=here if root is None else Path(root).resolve()
    path=here/PARENT_FILE if (here/PARENT_FILE).is_file() else root/PARENT_FILE
    _require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest()==PARENT_SHA256,'Pinned grouped621 source changed or missing')
    return root,path


def _load(path):
    spec=importlib.util.spec_from_file_location('_u15_center611_grouped_parent',path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


def _emit(parent,root):
    _,bundle=parent._context(root);base=bundle['base'];truth=bundle['truth'];_,paths=parent.paths(root)
    groups=tuple(tuple(i for i,row in enumerate(base.RULES) if row[0]==q) for q in range(15))
    _require(sorted(map(len,groups))==[1]+[2]*14,'Unexpected source-state partition')
    pairs=tuple(g for g in groups if len(g)==2)
    class CenteredDAG(base.DAG):
        def __init__(self):
            super().__init__();self.source_groups=[]
            for ids in pairs:self.source_groups.append((ids,super().add(*(f'edge{i}' for i in ids))))
            # The parent's first J computation repeats these exact gates and
            # reuses them by CSE; no extra uncharged J node is introduced.
            self.shared_J=self.sub(self.add(*(f'edge{i}' for i in range(29))),29)
        def add(self,*terms):
            if len(terms)>1 and all(type(v) is str and v.startswith('edge') and v[4:].isdigit() for v in terms):
                active=list(terms)
                for ids,value in self.source_groups:
                    names=[f'edge{i}' for i in ids]
                    if all(active.count(n)==1 for n in names):
                        first=min(active.index(n) for n in names)
                        active=[n for n in active if n not in names];active.insert(first,value)
                terms=tuple(active)
            return super().add(*terms)
        def linear(self,weights):
            if max(weights)<=1:return super().linear(weights)
            _require(all(type(w) is int and 0<=w<=14 for w in weights),'State code domain changed')
            bins={q:self.add(*(f'edge{i}' for i,w in enumerate(weights) if w==q)) for q in range(15) if q!=CENTER}
            terms=[self.mul(k,self.sub(bins[CENTER+k],bins[CENTER-k])) for k in range(1,8)]
            return self.sub(self.add(*terms),sum(w-CENTER for w in weights))
    oldraw=parent.build(root=root)
    env=dict(base.__dict__,DAG=CenteredDAG,RULES=oldraw['rules'])
    tree=ast.parse(paths[BASELINE_FILE].read_bytes())
    raw=deepcopy(next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='raw_build'))
    changes=0
    for node in ast.walk(raw):
        if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='pairs' for t in node.targets):
            _require(isinstance(node.value,ast.List) and len(node.value.elts)==5,'Outer comparison layout changed')
            expected="(d.mul(B, r['N']), d.add(r['Q'], d.mul(9, P)))"
            _require(ast.unparse(node.value.elts[2])==expected,'Baseline state comparison layout changed')
            node.value.elts[2]=ast.parse("(d.add(d.mul(B,r['N']),d.mul(6,P)),d.add(r['Q'],7))",mode='eval').body
            changes+=1
    _require(changes==1,'Expected one state comparison')
    ast.fix_missing_locations(raw);exec(compile(ast.Module(body=[raw],type_ignores=[]),'<center7 raw arithmetic>','exec'),env)
    wrapper=deepcopy(next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='_build'))
    ast.fix_missing_locations(wrapper);exec(compile(ast.Module(body=[wrapper],type_ignores=[]),'<complete ordinary composition>','exec'),env)
    ports={o:env['_build'](o) for o in (False,True)}
    adapter=SimpleNamespace(build=lambda ordinary=False:deepcopy(ports[_flag(ordinary)]),finish=base.finish)
    transform=dict(truth.__dict__,_parent_module=lambda:adapter)
    tree=ast.parse(paths[TRUTH_FILE].read_bytes())
    defs=[deepcopy(next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name==name)) for name in ('_tagged','_child')]
    tree=ast.Module(body=defs,type_ignores=[]);ast.fix_missing_locations(tree)
    exec(compile(tree,'<pinned paid tag and truth-field transforms>','exec'),transform)
    packets={}
    for ordinary in (False,True):
        emitted=transform['_child'](ordinary);p=parent.build(ordinary,root=root)
        # Start with the reviewed arithmetic-sharing metadata, replacing every
        # register/source/interface entry with the actual newly emitted values.
        for key in ('source','comparisons','parameters','auxiliaries','registers','tag_registers','computed_definitions',
                    'polynomial_source','output','ledger'):
            p[key]=deepcopy(emitted[key])
        p['registers']['Qdev']=p['registers'].pop('Q');p['registers']['Ndev']=p['registers'].pop('N')
        p.pop('projection_cuts',None)
        p.update(kind='centered_grouped_computed_truth',state_center=CENTER,
            state_deviation_fields=['Qdev','Ndev'],common_affine_cuts=list(COMMON_CUTS),
            centered_state_equation='B*Ndev+6P=Qdev+7',
            canonical_parent={'file':PARENT_FILE,'sha256':PARENT_SHA256},
            source_lineage=dict(p['source_lineage'],**{PARENT_FILE:PARENT_SHA256}),
            parent_relation='Exact complete polynomial identity on every integer supplied assignment; centered signed state intermediates, unchanged supplied coordinates.',
            scope='Complete first-halt polynomial on unchanged ordinary valid-program slices; exact arithmetic regrouping only, no new87 bound.')
        packets[ordinary]=p
    return packets,bundle


def _affine(packet,register):
    rows={n:(op,a,b) for n,op,a,b in packet['source']};memo={}
    def add(a,b,sign=1):
        result=dict(a)
        for n,c in b.items():result[n]=result.get(n,0)+sign*c
        return {n:c for n,c in result.items() if c}
    def form(v):
        if type(v) is int:return {'':v} if v else {}
        if v in memo:return memo[v]
        if v not in rows:return {v:1}
        op,a,b=rows[v];a,b=form(a),form(b)
        if op in ('+','-'):result=add(a,b,1 if op=='+' else -1)
        elif set(a)<={''}:result={n:a.get('',0)*c for n,c in b.items() if a.get('',0)*c}
        elif set(b)<={''}:result={n:b.get('',0)*c for n,c in a.items() if b.get('',0)*c}
        else:raise ValueError('Expected an affine projection')
        memo[v]=result;return result
    return form(register)


def _identity_certificate(old,new):
    _require(old['parameters']==new['parameters'] and old['auxiliaries']==new['auxiliaries'],'Coordinate domain changed')
    _require(old['rules']==new['rules'] and old['table']==new['table'] and old['state_relabel']==new['state_relabel'],'Machine changed')
    forms={}
    for name in COMMON_CUTS:
        a=_affine(old,old['registers'][name]);b=_affine(new,new['registers'][name]);_require(a==b,'Common affine form changed');forms[name]=b
    for name,column in (('Qdev',0),('Ndev',2)):
        weights=[r[column]-CENTER for r in old['rules']]
        expected={f'edge{i}':w for i,w in enumerate(weights) if w}
        if sum(weights):expected['']=-sum(weights)
        actual=_affine(new,new['registers'][name]);_require(actual==expected,'State deviation changed');forms[name]=actual
    nodes={}
    def intern(key):
        if key not in nodes:nodes[key]=len(nodes)
        return nodes[key]
    def expressions(packet):
        cuts={packet['registers'][name]:name for name in COMMON_CUTS};env={}
        def get(x):return intern(('constant',x)) if type(x) is int else env.get(x,intern(('variable',x)))
        for n,op,a,b in packet['source']:
            if n in cuts:env[n]=intern(('cut',cuts[n]));continue
            a,b=get(a),get(b)
            if op in ('+','*') and a>b:a,b=b,a
            env[n]=intern((op,a,b))
        return env,[(get(a),get(b)) for a,b in packet['comparisons']]
    oe,op=expressions(old);ne,np=expressions(new);index=old.get('loader_comparison_count',0)+2
    _require(len(op)==len(np) and all(a==b for i,(a,b) in enumerate(zip(op,np)) if i!=index),'A nonstate comparison changed')
    for name in set(old['registers'])-{'Q','N'}:
        a=old['registers'][name];b=new['registers'][name]
        _require((oe.get(a,intern(('variable',a))) if type(a) is str else intern(('constant',a)))==(ne.get(b,intern(('variable',b))) if type(b) is str else intern(('constant',b))),'A common semantic register changed')
    B,J,P,Q,N=sp.symbols('B J P Q N')
    def expression(packet,node,cuts):
        rows={n:(op,a,b) for n,op,a,b in packet['source']};memo={}
        def get(x):
            if type(x) is int:return sp.Integer(x)
            if x in cuts:return cuts[x]
            if x in memo:return memo[x]
            op,a,b=rows[x];a,b=get(a),get(b);memo[x]=a+b if op=='+' else a-b if op=='-' else a*b;return memo[x]
        return get(node)
    r=new['registers'];left,right=new['comparisons'][index]
    cuts={r['B']:B,r['P']:P,r['Qdev']:Q,r['Ndev']:N}
    residual=sp.expand(expression(new,left,cuts)-expression(new,right,cuts))
    _require(residual==B*N-Q+6*P-7,'Actual centered state residual changed')
    geometry=expression(new,r['P'],{r['B']:B,r['J']:J})
    _require(sp.expand(geometry-((B-1)*J+1))==0,'Computed repunit identity changed')
    before=B*(N+7*J)-(Q+7*J)-P
    _require(sp.expand((before-residual).subs(P,(B-1)*J+1))==0,'State residual polynomial identity failed')
    for packet in (old,new):
        rows=list(packet['source']);squares=[]
        for i,(a,b) in enumerate(packet['comparisons']):
            n=f'poly_res{i}';s=f'poly_sq{i}';rows.extend([(n,'-',a,b),(s,'*',n,n)]);squares.append(s)
        out=squares[0]
        for i,s in enumerate(squares[1:],1):n=f'poly_sum{i}';rows.append((n,'+',out,s));out=n
        _require(rows==packet['polynomial_source'] and out==packet['output'],'Complete SOS finalizer changed')
    return dict(exact_affine_forms=forms,unchanged_nonstate_residuals=len(op)-1,
        actual_state_residual='B*Ndev-Qdev+6P-7',computed_geometry_identity=True,
        complete_polynomial_identity=True,expression_nodes=len(nodes))


@lru_cache(None)
def _bundle(root_text,parent_text):
    root,path=_source_guard(root_text);_require(str(path)==parent_text,'Pinned path changed')
    parent=_load(path);packets,prior=_emit(parent,root);certificates={};parents={}
    for ordinary,p in packets.items():
        old=parent.build(ordinary,root=root);certificates[ordinary]=_identity_certificate(old,p);parents[ordinary]=old
        for kind in ('certificate','polynomial'):
            _require(old['ledger'][kind]['operations']==p['ledger'][kind]['operations']+10,'Expected ten saved operations')
            _require(old['ledger'][kind]['M']==p['ledger'][kind]['M']+13,'Expected thirteen saved multiplications')
            _require(old['ledger'][kind]['A']+3==p['ledger'][kind]['A'],'Expected three additional additions/subtractions')
        for key in ('equations','positive_witnesses','formal_degree_upper_bound','exact_degree_claimed'):
            _require(old['ledger'][key]==p['ledger'][key],'Semantic interface ledger changed')
        _require(p['ledger']['polynomial']['operations']==(611 if ordinary else 368),'Unexpected complete operation count')
    return dict(packets=packets,parents=parents,certificates=certificates,parent=parent,truth=prior['truth'],base=prior['base'])


def _context(root=None):
    root,path=_source_guard(root);bundle=_bundle(str(root),str(path));bundle['parent'].paths(root)
    return root,bundle


def build(ordinary=False,*,root=None):
    ordinary=_flag(ordinary);_,bundle=_context(root);return deepcopy(bundle['packets'][ordinary])


def canonical_parent(ordinary=False,*,root=None):
    ordinary=_flag(ordinary);_,bundle=_context(root);return deepcopy(bundle['parents'][ordinary])


def checked(packet,*,root=None):
    _,bundle=_context(root);_require(type(packet) is dict,'Complete canonical packet required');ordinary=_flag(packet.get('ordinary'))
    _require(_exact(packet,bundle['packets'][ordinary]),'Noncanonical centered-state packet');return packet


def polynomial_source(packet,*,root=None):return deepcopy(checked(packet,root=root)['polynomial_source'])


def evaluate(packet,values,*,signed=False,root=None):
    p=checked(packet,root=root);_,bundle=_context(root);t=bundle['truth'];v=t._assignment(p,values,signed)
    return t._execute(p['polynomial_source'],v)[p['output']]


def identity(packet,values,*,signed=False,root=None):
    p=checked(packet,root=root);_,bundle=_context(root);t=bundle['truth'];v=t._assignment(p,values,signed);old=bundle['parents'][p['ordinary']]
    a=t._execute(p['polynomial_source'],v);b=t._execute(old['polynomial_source'],v)
    rr=[t._at(a,x)-t._at(a,y) for x,y in p['comparisons']];prior=[t._at(b,x)-t._at(b,y) for x,y in old['comparisons']]
    _require(rr==prior and a[p['output']]==b[old['output']],'Complete polynomial identity failed')
    return dict(output=a[p['output']],residuals=rr)


def verify(root=None):
    root,bundle=_context(root);rng=random.Random(611700);counts=Counter();records=[]
    def reject(f):
        try:f()
        except (ValueError,TypeError,KeyError):counts['malformed_rejected']+=1;return
        raise AssertionError('Malformed input accepted')
    for ordinary in (False,True):
        p=build(ordinary,root=root);old=canonical_parent(ordinary,root=root)
        _require('Q' not in p['registers'] and 'N' not in p['registers'] and p['state_center']==7,'Stale projection interface')
        for case in range(64):
            signed=case>=32;v={n:rng.randrange(-3,5) if signed else rng.randrange(1,7) for n in p['parameters']+p['auxiliaries']}
            if not ordinary and case<4:v.update(L0=case%2,R0=case//2)
            result=identity(p,v,signed=signed,root=root)
            _require(result['output']==evaluate(p,v,signed=signed,root=root),'Public evaluator changed output')
            counts['complete_polynomial_identities']+=1;counts['signed_identities']+=signed;counts['individual_residual_identities']+=len(result['residuals'])
        v={n:1 for n in p['parameters']+p['auxiliaries']}
        for n in v:
            for bad in (True,1.0,0 if ordinary or n in p['auxiliaries'] else -1):
                values=dict(v);values[n]=bad;reject(lambda values=values:evaluate(p,values,root=root))
        for key in p:
            bad=deepcopy(p);del bad[key];reject(lambda bad=bad:checked(bad,root=root))
        for field in ('source','polynomial_source'):
            for i,row in enumerate(p[field]):
                for j in (2,3):
                    if type(row[j]) is int:
                        for value in (float(row[j]),bool(row[j])):
                            bad=deepcopy(p);rr=list(row);rr[j]=value;bad[field][i]=tuple(rr);reject(lambda bad=bad:checked(bad,root=root))
        for value in (0,1,None,1.0,'False'):
            reject(lambda value=value:build(value,root=root));reject(lambda value=value:canonical_parent(value,root=root))
            reject(lambda value=value:evaluate(p,v,signed=value,root=root))
        for values in (dict(v,extra=1),{n:x for n,x in v.items() if n!='edge0'}):reject(lambda values=values:evaluate(p,values,root=root))
        for getter,wanted in ((build,p),(canonical_parent,old)):
            exposed=getter(ordinary,root=root);exposed['source'].clear();exposed['registers'].clear();exposed['ledger'].clear()
            _require(_exact(getter(ordinary,root=root),wanted),'Export poisoned cache');counts['defensive_copy_cases']+=1
        exposed=polynomial_source(p,root=root);exposed.clear();_require(polynomial_source(p,root=root)==p['polynomial_source'],'Exported source poisoned cache');counts['defensive_copy_cases']+=1
        records.append(dict(ordinary=ordinary,ledger=p['ledger'],parent_ledger=old['ledger'],identity=bundle['certificates'][ordinary],compiler=p))
    original=sys.modules.get('u15_raw_half_tape_loader')
    try:
        for origin in (None,'/foreign/u15_raw_half_tape_loader.py'):
            fake=SimpleNamespace(build=lambda *a,**kw:(_ for _ in ()).throw(AssertionError('foreign loader used')))
            if origin is not None:fake.__file__=origin
            sys.modules['u15_raw_half_tape_loader']=fake;_bundle.cache_clear()
            _require(build(True,root=root)['ledger']['polynomial']['operations']==611,'Cold source changed')
            _require(sys.modules['u15_raw_half_tape_loader'] is fake,'Caller module was not restored');counts['cold_import_isolation_cases']+=1
    finally:
        if original is None:sys.modules.pop('u15_raw_half_tape_loader',None)
        else:sys.modules['u15_raw_half_tape_loader']=original
    return dict(status='PASS_CENTERED_STATES611',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        parent_source_sha256=PARENT_SHA256,state_center=7,counts=dict(counts),forms=records,
        scope='Exact whole-polynomial identity on all integer supplied tuples; same coordinates and valid-program positive relation as621. Signed computed state deviations are declared explicitly. Upper degree1936, no exact-degree or optimum claim.')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path);ap.add_argument('--write',action='store_true');a=ap.parse_args()
    result=verify(a.root);path=Path(__file__).with_suffix('.json');wire=json.dumps(result,indent=2)+'\n'
    if a.write:path.write_text(wire)
    else:_require(_exact(json.loads(path.read_text()),json.loads(wire)),'Saved receipt differs')
    print(json.dumps({k:result[k] for k in ('status','counts')},indent=2));print([x['ledger'] for x in result['forms']])
