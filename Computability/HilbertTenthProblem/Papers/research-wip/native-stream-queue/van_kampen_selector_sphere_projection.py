"""Guarded integer-zero projection of the imported bounded-area compiler.

One sphere residual replaces each selector block; V1=U1 is eliminated.
This is an area-indexed family, not a fixed-arity universal equation.
"""
import argparse
from copy import deepcopy
from functools import lru_cache
import hashlib
import io
from itertools import product
import json
from math import prod
from pathlib import Path
import random
import subprocess
import sys
from types import ModuleType
import zipfile
import sympy as sp

ROOT = Path(__file__).resolve().parents[5]
ARCHIVE = 'docs/incoming/arithmetic_van_kampen.zip'
ARRIVAL = '6914ccca6'
ARCHIVE_SHA256 = 'c29f2918b5cddda37ca4a0190fbeba1930015c7d8e4a3fa55f13b5dd233e6ed9'
MEMBER = 'arithmetic_van_kampen/code/van_kampen.py'
SOURCE_SHA256 = '976def6231c12f50ff9336a9c1bd604bf2fb6a96de4dffad4b29121c362625f3'


def archive_bytes():
    path = ROOT/ARCHIVE
    if path.is_file(): data = path.read_bytes()
    else:
        data = subprocess.run(['git','show',f'{ARRIVAL}:{ARCHIVE}'],cwd=ROOT,
                              check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
    assert hashlib.sha256(data).hexdigest() == ARCHIVE_SHA256, 'frozen incoming archive mismatch'
    return data


@lru_cache(None)
def _parent():
    with zipfile.ZipFile(io.BytesIO(archive_bytes())) as z: code = z.read(MEMBER)
    assert hashlib.sha256(code).hexdigest() == SOURCE_SHA256
    name = '_van_kampen_frozen_6914ccca6'; module = ModuleType(name)
    module.__file__ = f'{ARCHIVE}!{MEMBER}'; previous = sys.modules.get(name)
    sys.modules[name] = module
    try: exec(compile(code,module.__file__,'exec'),module.__dict__)
    finally:
        if previous is None: del sys.modules[name]
        else: sys.modules[name] = previous
    return module


def flags(relators,m):
    assert type(m) is int and m >= 0
    assert type(relators) in (tuple,list) and len(relators) >= 1
    assert all(type(word) is str and all(c in 'aAbB' for c in word) for word in relators)
    return tuple(relators),m


def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict:
        return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
    if type(a) in (tuple,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def sparse(expr,names):
    assert not sp.sympify(expr).atoms(sp.Float), 'floating polynomial coefficient'
    raw = sp.Poly(expr,*names)
    assert all(coef.is_Integer for coef in raw.coeffs()), 'noninteger polynomial coefficient'
    p = sp.Poly(expr,*names,domain=sp.ZZ)
    return tuple((tuple(int(e) for e in mon),int(coef)) for mon,coef in p.terms() if coef)


def expression(poly,names):
    return sp.Add(*(coef*sp.Mul(*(n**e for n,e in zip(names,mon))) for mon,coef in poly))


def degree(poly): return max((sum(mon) for mon,coef in poly),default=0)


@lru_cache(None)
def _parent_packet(relators,m):
    system = _parent().compile_budget(relators,m)
    names = system.parameters+system.variables
    assert type(system.parameters) is type(system.variables) is type(system.residuals) is tuple
    assert all(type(n) is sp.Symbol and n.is_integer for n in names)
    assert len(set(names))==len(names)
    assert system.metadata['kind']=='budget' and system.metadata['budget']==m
    assert tuple(system.metadata['relators'])==relators
    q=2*len(relators)+1
    assert len(system.variables)==((q+12)*m-4 if m else 0)
    assert len(system.residuals)==((q+10)*m if m else 4)
    return dict(kind='frozen_integer_budget',domain='integers',relators=relators,budget=m,
        parameters=tuple(str(n) for n in system.parameters),variables=tuple(str(n) for n in system.variables),
        residuals=tuple(sparse(r,names) for r in system.residuals),
        archive_sha256=ARCHIVE_SHA256,source_sha256=SOURCE_SHA256,arrival=ARRIVAL)


def canonical_parent(relators=('abAB',),m=1):
    return deepcopy(_parent_packet(*flags(relators,m)))


def rewrite(old):
    assert type(old) is dict
    relators,m=flags(old.get('relators'),old.get('budget'))
    assert exact(old,_parent_packet(relators,m)), 'complete exact canonical imported packet required'
    q=2*len(relators)+1
    oldnames=tuple(sp.Symbol(n,integer=True) for n in old['parameters']+old['variables'])
    by={str(n):n for n in oldnames}; oldrows=[expression(r,oldnames) for r in old['residuals']]
    substitution={}; removed=[]
    if m:
        for i in range(m):
            e0=by[f'e{i}_0']; substitution[e0]=1-sum(by[f'e{i}_{j}'] for j in range(1,q));removed.append(str(e0))
        u=[by['u0_'+n] for n in ('x','y','z','t')]
        values=(1+4*u[0],2*u[1],2*u[2],1+4*u[3])
        for n,value in zip(('00','01','10','11'),values):
            name='v0_'+n;substitution[by[name]]=value;removed.append(name)
    variables=tuple(n for n in old['variables'] if n not in removed)
    names=tuple(by[n] for n in old['parameters']+variables)
    mapped=[sp.expand(r.xreplace(substitution)) for r in oldrows]
    newrows=[]; row_map=[]; selector_blocks=[]; identity_rows=[]
    if not m:
        newrows=mapped;row_map=[dict(new_index=i,parent_indices=(i,),kind='retained') for i in range(4)]
    for i in range(m):
        start=(q+10)*i;e=[by[f'e{i}_{j}'] for j in range(q)]
        assert all(sp.expand(oldrows[start+1+j]-e[j]*(e[j]-1))==0 for j in range(q))
        assert sp.expand(oldrows[start+q+1]-sum(e)+1)==0
        assert mapped[start+q+1]==0;identity_rows.append(start+q+1)
        if i==0:
            assert all(mapped[j]==0 for j in range(start+q+2,start+q+6))
            identity_rows.extend(range(start+q+2,start+q+6))
        boolean_indices=tuple(range(start+1,start+q+1))
        sphere=sp.expand(sum(x*x for x in e[1:])+(sum(e[1:])-1)**2-1)
        assert sp.expand(sphere-sum(mapped[j] for j in boolean_indices))==0
        selector_blocks.append(dict(parent_indices=boolean_indices,residual=sparse(sphere,names)))
        indices=[start]+([] if i==0 else list(range(start+q+2,start+q+6)))+list(range(start+q+6,start+q+10))
        for j in indices:
            row_map.append(dict(new_index=len(newrows),parent_indices=(j,),kind='retained'));newrows.append(mapped[j])
        row_map.append(dict(new_index=len(newrows),parent_indices=boolean_indices,kind='selector_sum'));newrows.append(sphere)
    assert len(variables)==((q+11)*m-8 if m else 0)
    assert len(newrows)==(10*m-4 if m else 4)
    residuals=tuple(sparse(r,names) for r in newrows)
    assert max(map(degree,residuals))==(2 if m else 1)
    return dict(kind='integer_selector_sphere_projection',domain='integers',relators=relators,budget=m,
        parameters=old['parameters'],variables=variables,residuals=residuals,
        eliminated_variables=tuple(removed),
        lift_formulas={str(n):sparse(r,names) for n,r in substitution.items()},
        row_map=tuple(row_map),selector_blocks=tuple(selector_blocks),parent_identity_rows=tuple(identity_rows),
        witnesses=len(variables),residual_count=len(residuals),residual_degree_bound=2 if m else 1,
        exact_sos_degree=4 if m else 2,integer_zero_bijection=True,offzero_polynomial_identity=False,
        archive_sha256=ARCHIVE_SHA256,source_sha256=SOURCE_SHA256,arrival=ARRIVAL,
        scope='Full integer-zero bijection with the supplied fixed-area parent. External budget; no arithmetic-operation or universal fixed-arity claim.')


@lru_cache(None)
def _build(relators,m): return rewrite(_parent_packet(relators,m))


def build(relators=('abAB',),m=1): return deepcopy(_build(*flags(relators,m)))


def checked(packet):
    assert type(packet) is dict
    key=flags(packet.get('relators'),packet.get('budget'))
    assert exact(packet,_build(*key)), 'complete type-sensitive canonical projected packet required'


def assignment(values,names):
    assert type(values) is dict and all(type(n) is str and type(v) is int for n,v in values.items())
    assert set(values)==set(names), 'exact complete assignment required'


def scalar(poly,values): return sum(coef*prod(v**e for v,e in zip(values,mon)) for mon,coef in poly)


def lift_assignment(packet,values):
    checked(packet);names=packet['parameters']+packet['variables'];assignment(values,names)
    result=dict(values);ordered=[values[n] for n in names]
    result.update({n:scalar(poly,ordered) for n,poly in packet['lift_formulas'].items()})
    return result


def project_assignment(packet,values):
    checked(packet);old=_parent_packet(packet['relators'],packet['budget'])
    assignment(values,old['parameters']+old['variables'])
    return {n:values[n] for n in packet['parameters']+packet['variables']}


def evaluate(packet,values):
    checked(packet);names=packet['parameters']+packet['variables'];assignment(values,names)
    ordered=[values[n] for n in names]
    return sum(scalar(r,ordered)**2 for r in packet['residuals'])


def correction(packet,values):
    lifted=lift_assignment(packet,values);old=_parent_packet(packet['relators'],packet['budget'])
    ordered=[lifted[n] for n in old['parameters']+old['variables']]
    oldvalues=[scalar(r,ordered) for r in old['residuals']]
    delta=sum(sum(oldvalues[j] for j in block['parent_indices'])**2
              -sum(oldvalues[j]**2 for j in block['parent_indices']) for block in packet['selector_blocks'])
    assert all(oldvalues[j]==0 for j in packet['parent_identity_rows'])
    assert delta>=0 and evaluate(packet,values)-sum(v*v for v in oldvalues)==delta
    return delta


def ledger(packet=None):
    if packet is None:packet=build()
    checked(packet);old=_parent_packet(packet['relators'],packet['budget'])
    return dict(parent_witnesses=len(old['variables']),witnesses=len(packet['variables']),
        parent_residuals=len(old['residuals']),residuals=len(packet['residuals']),
        exact_sos_degree=packet['exact_sos_degree'],arithmetic_operations='not counted')


def guards(packet):
    count=0
    def reject(fn):
        nonlocal count
        try:fn()
        except (AssertionError,KeyError,TypeError,ValueError,sp.PolynomialError):count+=1
        else:raise AssertionError('malformed caller accepted')
    for relators,m in ((('abAB',),True),(('abAB',),1.0),(('abAB',),-1),
                       ((),1),(['c'],1),([True],1),('abAB',1)):
        reject(lambda relators=relators,m=m:build(relators,m))
    old=canonical_parent(packet['relators'],packet['budget'])
    for value in (True,1.0):
        for base,api in ((packet,checked),(old,rewrite)):
            bad=deepcopy(base);rows=list(bad['residuals'])
            i,j=next((i,j) for i,row in enumerate(rows) for j,(_,coef) in enumerate(row) if coef==1)
            row=list(rows[i]);mon,coef=row[j];row[j]=(mon,value);rows[i]=tuple(row);bad['residuals']=tuple(rows)
            reject(lambda bad=bad,api=api:api(bad))
    for key,value in (('variables',('bad',)),('row_map',()),('integer_zero_bijection',1),('exact_sos_degree',4.0)):
        reject(lambda key=key,value=value:checked(dict(packet,**{key:value})))
    values={n:1 for n in packet['parameters']+packet['variables']}
    for value in (True,1.0):
        bad=dict(values);bad[next(iter(bad))]=value
        for api in (evaluate,lift_assignment,correction):reject(lambda api=api,bad=bad:api(packet,bad))
    reject(lambda:evaluate(packet,{}))
    reject(lambda:project_assignment(packet,{}))
    reject(lambda:sparse(sp.Float(1)*sp.Symbol('x'),(sp.Symbol('x'),)))
    reject(lambda:sparse(sp.Rational(1,2)*sp.Symbol('x'),(sp.Symbol('x'),)))
    # Neither public builder exposes a mutable canonical cache reference.
    frozen=deepcopy(packet)
    damaged=build(packet['relators'],packet['budget']);damaged['lift_formulas'].clear();checked(frozen)
    assert exact(build(packet['relators'],packet['budget']),frozen)
    old['residuals']=();assert canonical_parent(packet['relators'],packet['budget'])['residuals']
    return count


def verify():
    rng=random.Random(691406);records=[];counts=dict(offzero_corrections=0,signed_cases=0,
        parent_zeros=0,wrong_boundaries=0,selector_integer_tuples=0,rejected_callers=0)
    examples=[];source=_parent()
    for relators in (('abAB',),('aa','bbb'),('','abAB','abAB')):
        for m in range(5):
            p=build(relators,m);old=_parent_packet(relators,m)
            records.append(dict(ledger=ledger(p),packet=p,parent=old))
            for case in range(12):
                values={n:rng.randrange(-3,4) for n in p['parameters']+p['variables']}
                correction(p,values);counts['offzero_corrections']+=1;counts['signed_cases']+=1
                assert project_assignment(p,lift_assignment(p,values))==values
            for case in range(6):
                labels=[rng.randrange(2*len(relators)+1) for _ in range(m)]
                conjugators=[source.evaluate_word(''.join(rng.choice('aAbB') for _ in range(6))) for _ in range(m)]
                witness=source.make_budget_witness(relators,labels,conjugators)
                system=source.compile_budget(relators,m)
                values={str(n):int(v) for n,v in source.symbolic_budget_assignment(system,witness).items()}
                projected=project_assignment(p,values)
                assert evaluate(p,projected)==0 and lift_assignment(p,projected)==values
                counts['parent_zeros']+=1
                bad=dict(projected);bad['w00']+=1;assert evaluate(p,bad)>0;counts['wrong_boundaries']+=1
                if relators==('abAB',) and m==1 and case==0:examples.append(dict(parent=values,projected=projected))
            if m in (0,1):counts['rejected_callers']+=guards(p)
    for dimension in range(1,7):
        for e in product(range(-2,3),repeat=dimension):
            S=sum(x*x for x in e)+(sum(e)-1)**2-1
            good=all(x in (0,1) for x in e) and sum(e)<=1
            assert (S==0)==good;counts['selector_integer_tuples']+=1
    rational=(sp.Rational(2,3),)*2
    assert sum(x*x for x in rational)+(sum(rational)-1)**2-1==0
    return dict(status='PASS_VAN_KAMPEN_SELECTOR_SPHERE_PROJECTION',records=records,examples=examples,
        counts=counts,source=dict(archive=ARCHIVE,arrival=ARRIVAL,archive_sha256=ARCHIVE_SHA256,
                                 member=MEMBER,source_sha256=SOURCE_SHA256),
        rational_counterexample=['2/3','2/3'],
        scope='Fixed-area integer-zero bijection; degrees and residual/witness counts only. No full unbounded universal source or gate count.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['counts'])
