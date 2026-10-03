"""Complete paid U15 history with disjoint tags and computed truth fields.

Public packets are canonical and copied. The exact graph relation is to the
new tagged parent; equivalence to the 653-operation baseline forgets all
private native coordinates and uses fresh positive native extensions.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys

HERE=Path(__file__).resolve().parent
PARENT_FILE='u15_packed_two_tape_history.py'
PARENT_SHA256='ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318'
PARENT_PACKET_SHA256=('88bece7a25db1454f0c81574bbe40c3bb3d1a46bf5942fa0ccd62ffa0625e40a',
                      '43f6def9967bbbf36931386e66717f2c6a53c4488512cd3a47d6ccde9013634f')
TRUTH_FIELDS=('native__F0','native__F1','native__F2')
REMOVED_ROWS=('native__input_A','native__shared_sum02','native__bs_Q','native__bs_q','native__input_B')
REMOVED_COMPARISONS=(('native__bs_q','native__q'),('native__input_A','native__padded_A'),('native__input_B','native__padded_B'))


def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:
        return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def flag(v,name='ordinary'):
    if type(v) is not bool:raise ValueError(name+' must be Boolean')
    return v


def _typed(value):
    if type(value) is dict:
        if any(type(k) is not str for k in value):raise ValueError('Exact string packet keys required')
        return ['dict',[(k,_typed(value[k])) for k in sorted(value)]]
    if type(value) in (list,tuple):return [type(value).__name__,[_typed(v) for v in value]]
    if type(value) in (str,int,bool,type(None)):return [type(value).__name__,value]
    raise ValueError('Unexpected packet scalar/container type')


def _packet_hash(packet):
    return hashlib.sha256(json.dumps(_typed(packet),separators=(',',':')).encode()).hexdigest()


@lru_cache(None)
def _parent_module():
    path=HERE/PARENT_FILE
    if not path.is_file():
        spec=importlib.util.find_spec(PARENT_FILE[:-3])
        if spec is None or spec.origin is None:raise ValueError('Place compiler beside its pinned parent or add that directory to PYTHONPATH')
        path=Path(spec.origin)
    if hashlib.sha256(path.read_bytes()).hexdigest()!=PARENT_SHA256:
        raise ValueError('Pinned complete baseline source changed')
    spec=importlib.util.spec_from_file_location('_u15_truth647_parent',path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    # Authenticate actual consumed packets as well as the parent file. A cached
    # foreign/stale loader cannot replace its arithmetic behind a source pin.
    for ordinary in (False,True):
        if _packet_hash(module.build(ordinary))!=PARENT_PACKET_SHA256[int(ordinary)]:
            raise ValueError('Actual complete baseline packet changed')
    return module


def _execute(rows,values):
    env=dict(values)
    for n,op,a,b in rows:
        x=env[a] if type(a) is str else a;y=env[b] if type(b) is str else b
        env[n]=x*y if op=='*' else x+y if op=='+' else x-y
    return env


def _at(env,v):return env[v] if type(v) is str else v


@lru_cache(None)
def _tagged(ordinary):
    flag(ordinary);parent=_parent_module();p=parent.build(ordinary);r=p['registers']
    prefix=[];native=[];found=False
    for row in p['source']:
        if row[0].startswith('native__'):found=True
        (native if found else prefix).append(row)
    scale=next(row for row in prefix if row[0]==r['scale'])
    if scale[1]!='*' or r['B'] not in scale[2:]:raise ValueError('Scale factor interface changed')
    T=scale[3] if scale[2]==r['B'] else scale[2]
    tags=[('tag_twice_T','*',2,T),('tag_A','+',r['Hjoin'],'tag_twice_T'),('tag_M','+',r['Mjoin'],T)]
    aliases={r['Hjoin']:'tag_A',r['Mjoin']:'tag_M'}
    renamed=lambda x:aliases.get(x,x)
    rows=prefix+tags+[(n,op,renamed(a),renamed(b)) for n,op,a,b in native]
    p.update(source=rows,kind='tagged_parent',parent_source_sha256=PARENT_SHA256,
        parent_packet_sha256=PARENT_PACKET_SHA256[int(ordinary)],
        tag_registers={'T':T,'A':'tag_A','M':'tag_M','Z':r['Zjoin'],'cap':r['scale']},
        tagged_ports='A=Hjoin+2T, M=Mjoin+T, Z=Zjoin, cap=B*T, T=P^34',
        baseline_relation='Same outer positive zero relation after forgetting all native coordinates; native extensions are refreshed.',
        scope='Complete tagged positive AND composition, unbounded first halt and paid ordinary loader on valid fixed-program slices.')
    p['baseline_native_source_sha256']=p.pop('native_packet_sha256')
    p['imported_native_descriptor_sha256']=p.pop('native_descriptor_sha256')
    for key in ('polynomial_source','output','ledger'):p.pop(key)
    return parent.finish(p)


@lru_cache(None)
def _child(ordinary):
    flag(ordinary);parent=_parent_module();p=deepcopy(_tagged(ordinary))
    rows=p['source'];pairs=p['comparisons']
    if any(sum(n==name for n,op,a,b in rows)!=1 for name in REMOVED_ROWS):raise ValueError('Native checksum/input row layout changed')
    if any(pairs.count(pair)!=1 for pair in REMOVED_COMPARISONS):raise ValueError('Native graph comparison layout changed')
    defs=[('native__F1','-','native__padded_A','native__F3'),
          ('native__F2','-','native__padded_B','native__F3'),
          ('computed_q_minus_A','-','native__q','native__padded_A'),
          ('computed_F0_plus_one','-','computed_q_minus_A','native__F2'),
          ('native__F0','-','computed_F0_plus_one',1)]
    out=[]
    for row in rows:
        if row[0] not in REMOVED_ROWS:out.append(row)
        if row[0]=='native__F3':out.extend(defs)
    p.update(source=out,comparisons=[pair for pair in pairs if pair not in REMOVED_COMPARISONS],
        auxiliaries=[n for n in p['auxiliaries'] if n not in TRUTH_FIELDS],kind='computed_truth',
        computed_truth_fields=TRUTH_FIELDS,computed_definitions=defs,
        removed_comparisons=REMOVED_COMPARISONS,
        graph_relation='Bijection with the newly tagged parent positive zeros. Signed restoration preserves its entire polynomial off zero.',
        positive_graph_helper_domain='Exact declared natural/positive coordinates satisfying the retained head and aggregate-bound equations.',
        scope='Complete fixed-arity U15 first-halt polynomial with paid tagged AND and three computed truth fields; ordinary interface requires a valid fixed program slice.')
    for key in ('polynomial_source','output','ledger'):p.pop(key)
    return parent.finish(p)


def build(ordinary=False):return deepcopy(_child(flag(ordinary)))


def tagged_parent(ordinary=False):return deepcopy(_tagged(flag(ordinary)))


def checked(packet):
    if type(packet) is not dict:raise ValueError('Complete canonical packet required')
    ordinary=flag(packet.get('ordinary'))
    if not exact(packet,_child(ordinary)):raise ValueError('Noncanonical computed-truth packet')
    return packet


def checked_tagged_parent(packet):
    if type(packet) is not dict:raise ValueError('Complete canonical tagged-parent packet required')
    ordinary=flag(packet.get('ordinary'))
    if not exact(packet,_tagged(ordinary)):raise ValueError('Noncanonical tagged-parent packet')
    return packet


def _assignment(packet,values,signed):
    flag(signed,'signed');names=packet['parameters']+packet['auxiliaries']
    if type(values) is not dict or set(values)!=set(names):raise ValueError('Wrong coordinate set')
    for n,v in values.items():
        if type(n) is not str or type(v) is not int:raise ValueError('Exact integer coordinates required')
        lower=0 if not packet['ordinary'] and n in ('L0','R0') else 1
        if not signed and v<lower:raise ValueError('Coordinate outside declared domain')
    return dict(values)


def _pretyping_guard(packet,env):
    offset=packet.get('loader_comparison_count',0)
    for a,b in packet['comparisons'][offset+3:offset+5]:
        if _at(env,a)!=_at(env,b):raise ValueError('Positive graph helpers require the retained head and aggregate-bound equations')


def evaluate(packet,values,*,signed=False):
    p=checked(packet);v=_assignment(p,values,signed)
    return _execute(p['polynomial_source'],v)[p['output']]


def evaluate_tagged_parent(packet,values,*,signed=False):
    p=checked_tagged_parent(packet);v=_assignment(p,values,signed)
    return _execute(p['polynomial_source'],v)[p['output']]


def lift_to_tagged_parent(packet,values,*,signed=False):
    p=checked(packet);v=_assignment(p,values,signed);env=_execute(p['source'],v)
    if not signed:_pretyping_guard(p,env)
    restored=dict(v,**{n:env[n] for n in TRUTH_FIELDS})
    return _assignment(_tagged(p['ordinary']),restored,signed)


def project_from_tagged_parent(packet,values,*,signed=False):
    p=checked(packet);old=_tagged(p['ordinary']);v=_assignment(old,values,signed);env=_execute(old['source'],v)
    if not signed:_pretyping_guard(old,env)
    if any(_at(env,a)!=_at(env,b) for a,b in REMOVED_COMPARISONS):
        raise ValueError('Tagged parent assignment is outside the computed truth-field graph')
    return {n:v[n] for n in p['parameters']+p['auxiliaries']}


def _manual_raw(v,rules):
    E=[v[f'edge{i}']-1 for i in range(29)];J=sum(E);D=v['L0']+v['R0']+v['height'];B=64*D;P=(B-1)*J+1
    H,G,U,ZL,ZR,ZU=(v[n] for n in ('H','G','U','ZL','ZR','ZU'))
    Q,S,N,Dir,W=[sum(t[c]*e for t,e in zip(rules,E)) for c in range(5)];WD=sum(t[3]*t[4]*e for t,e in zip(rules,E))
    Ec=sum(e*P**i for i,e in enumerate(E));K=sum(P**i for i in range(29));T=P**34
    A=H+P*G+P**2*U+P**3*H+P**4*G+P**5*Ec+2*T
    M=(B-1)*Dir*(1+P)+P**2*Dir+(P**3+P**4)*(D-1)*J+P**5*J*K+T
    Z=ZL+P*ZR+P**2*ZU+P**3*H+P**4*G+P**5*Ec;cap=B*T;mix=2*WD+ZU
    out=[2*(H-v['L0']+P*(v['Lfhat']-1))-B*(4*H-3*ZL+2*W-mix),
         2*(G-v['R0']+P*v['Rf'])-B*(G+3*ZR+mix-U),B*N-Q-9*P,B*U-S-P,H+G+ZL+ZR+ZU+v['bound']-P]
    q=16*cap;F3=16*Z+8;F1=16*(A-Z)+4;F2=16*(M-Z)+2;F0=16*(cap-A-M+Z)-15
    at=lambda n:v['native__'+n]
    r=F0+q*F1+q*q*F2+q*q*q*F3;s=2*at('odd_half')+1;k=at('eta')+at('zeta')
    X=q*(r+at('bound_beta'));Y=s*q;a=Y*(X+1);c=k*Y+at('eta');d=X+a*c+at('ga')*(4*a+3)
    delta=a*a+4*a+3;u=at('j')*c-(2*r+1);ic22=(at('i')*c*c)**2;y=at('y_aux')
    out += [((X*Y)**2+X)*(Y*k)**2-at('tau')*(at('tau')+1),k-r-1-at('h')*X*Y,
            d*d-1-delta*c*c,ic22-delta*(at('f')**2-1),ic22*(u*u-y*y)-(1-y*y),u+c-at('o')*at('f')]
    return out,dict(zip(TRUTH_FIELDS,(F0,F1,F2)))


def verify():
    if not __debug__:raise RuntimeError('Assertions required for research replay')
    parent=_parent_module();rng=random.Random(647102);counts=Counter();records=[]
    primary=parent.loader.nw.transition_table('15,2')
    expected={(int(q[1:])-1,int(s=='b')):(int(n[1:])-1,int(move=='L'),int(w=='b')) for (q,s),(n,w,move) in primary.items()}
    assert {(q,s):(n,d,w) for q,s,n,d,w in parent.RULES}==expected
    counts['fixed_primary_table_instructions']=len(expected)
    def reject(call):
        try:call()
        except (ValueError,TypeError):counts['malformed_rejections']+=1
        else:raise AssertionError('Malformed input accepted')
    for ordinary in (False,True):
        p=build(ordinary);old=tagged_parent(ordinary)
        assert p['ledger']['polynomial']['operations']==(647 if ordinary else 404)
        assert len(p['source'])==len(old['source']) and len(p['comparisons'])==len(old['comparisons'])-3
        assert p['ledger']['positive_witnesses']==(102 if ordinary else 51)
        assert p['ledger']['formal_degree_upper_bound']==1936
        names=p['parameters']+p['auxiliaries']
        for case in range(80):
            v={n:rng.randrange(1,8) if case<40 else rng.randrange(-4,5) for n in names}
            env=_execute(p['polynomial_source'],v);restored=lift_to_tagged_parent(p,v,signed=True);before=_execute(old['polynomial_source'],restored)
            assert project_from_tagged_parent(p,restored,signed=True)==v
            assert env[p['output']]==before[old['output']]==evaluate(p,v,signed=True)==evaluate_tagged_parent(old,restored,signed=True)
            for n,op,a,b in old['source']:
                if n not in REMOVED_ROWS:assert env[n]==before[n]
            assert all(_at(before,a)==_at(before,b) for a,b in REMOVED_COMPARISONS)
            raw={n:v[n] for n in build()['auxiliaries']}
            raw.update(L0=v['program_L'] if ordinary else v['L0'],R0=v['input_R0'] if ordinary else v['R0'])
            rr,truth=_manual_raw(raw,parent.RULES)
            assert all(env[n]==truth[n] for n in TRUTH_FIELDS)
            if ordinary:
                loader=parent.loader.build(False)
                rename=lambda n:{'x':'x','L0':'program_L','R0':'input_R0',**{n:n for n in ('program_L','program_A','program_B','program_D')}}.get(n,'input__'+n)
                lv={n:v[rename(n)] for n in loader['parameters']+loader['auxiliaries']}
                rr=parent.loader.bridge.independent(parent.loader.bridge.recoder(32),lv)+[parent.loader.DENOM*v['input_R0']+v['program_D']-v['program_A']*lv['q']**32-v['program_B']*lv['z']]+rr
            assert rr==[_at(env,a)-_at(env,b) for a,b in p['comparisons']]
            assert env[p['output']]==sum(x*x for x in rr)
            counts['complete_graph_and_manual_SOS_cases']+=1;counts['signed_cases']+=case>=40
        one={n:1 for n in names}
        for n in names:
            for bad in (True,1.0,0 if n in p['auxiliaries'] else -1):
                z=dict(one);z[n]=bad;reject(lambda z=z:evaluate(p,z))
        for field in ('source','comparisons','parameters','auxiliaries','registers','computed_definitions'):
            z=deepcopy(p);z[field]=None;reject(lambda z=z:checked(z))
        z=deepcopy(p);z['ledger']['equations']=float(z['ledger']['equations']);reject(lambda z=z:checked(z))
        z=deepcopy(old);z['ledger']['equations']=float(z['ledger']['equations']);reject(lambda z=z:checked_tagged_parent(z))
        reject(lambda:evaluate(p,one,signed=1));reject(lambda:lift_to_tagged_parent(p,one))
        restored=lift_to_tagged_parent(p,one,signed=True);restored['native__F1']+=1
        reject(lambda:project_from_tagged_parent(p,restored,signed=True))
        for bad in (0,1,None,'False'):reject(lambda bad=bad:build(bad));reject(lambda bad=bad:tagged_parent(bad))
        snapshot=deepcopy(p);_child.cache_clear();_tagged.cache_clear();poison=tagged_parent(ordinary)
        poison['source'].clear();poison['tag_registers']['A']='poison';assert exact(build(ordinary),snapshot)
        poison=build(ordinary);poison['computed_definitions'].clear();poison['ledger'].clear();assert exact(build(ordinary),snapshot)
        counts['cold_parent_and_nested_defensive_copy_cases']+=2
        records.append(dict(ordinary=ordinary,ledger=p['ledger'],tagged_parent_ledger=old['ledger']))
    examples=[]
    for L in range(16):
        for R in range(12):
            result=parent.trace(L,R,40)
            if result is None:continue
            v,meta=parent.outer_fixture(L,R,40);p=build();v={n:v[n] for n in p['parameters']+p['auxiliaries']}
            restored=lift_to_tagged_parent(p,v);assert project_from_tagged_parent(p,restored)==v
            env=_execute(p['source'],v);reg=p['tag_registers'];val=lambda n:_at(env,reg[n])
            assert val('A')&val('M')==val('Z') and max(val('A'),val('M'))<val('cap')
            assert min(restored[n] for n in TRUTH_FIELDS)>0
            for field in ('H','G','ZL','ZR','ZU','U','Lfhat','Rf'):
                bad=dict(v);bad[field]+=1;e=_execute(p['source'],bad)
                assert any(_at(e,a)!=_at(e,b) for a,b in p['comparisons'][:5]) or (_at(e,reg['A'])&_at(e,reg['M']))!=_at(e,reg['Z'])
                counts['outer_corruptions_rejected']+=1
            counts['genuine_outer_positive_graph_restorations']+=1
            if len(examples)<6:examples.append(dict(L=L,R=R,t=meta['t'],final=meta['final']))
    for D in range(1,10):
        B=64*D
        for T in range(1,24):
            for A,M,Z in ((0,0,0),(T-1,T-1,0),(0,0,T-1),(T-1,0,T-1),(0,T-1,T-1)):
                aa=A+2*T;mm=M+T;f=(16*(aa-Z)+4,16*(mm-Z)+2,16*(B*T-aa-mm+Z)-15)
                assert min(f)>0 and max(aa,mm,Z)<B*T;counts['untyped_margin_boundary_cases']+=1
    for exponent in range(7):
        T=1<<exponent
        for A in range(T):
            for M in range(T):
                assert ((A+2*T)&(M+T))==(A&M);counts['typed_tag_AND_cases']+=1
    # Cold imports must reject changed actual loader arithmetic despite a valid
    # baseline file hash. Type-sensitive descriptor pins also reject containers.
    loader=parent.loader;saved=loader.build
    try:
        for change_container in (False,True):
            def poisoned(*args,**kwargs):
                packet=saved(*args,**kwargs)
                if change_container:packet['source'][0]=list(packet['source'][0])
                else:
                    n,op,a,b=packet['source'][0];packet['source'][0]=(n,op,a,99)
                return packet
            loader.build=poisoned;_parent_module.cache_clear()
            # The parent normalizes row containers while composing. Poisoning
            # a list alone can be harmless; change the final scalar type too.
            if change_container:
                def poisoned(*args,**kwargs):
                    packet=saved(*args,**kwargs)
                    packet['parameters']=tuple(packet['parameters'])
                    packet['auxiliaries']=tuple(packet['auxiliaries'])
                    n,op,a,b=packet['source'][0];packet['source'][0]=(n,op,a,99.0)
                    return packet
                loader.build=poisoned
            try:_parent_module()
            except (ValueError,AssertionError):counts['cold_changed_loader_rejections']+=1
            else:raise AssertionError('Preloaded changed loader accepted')
    finally:
        loader.build=saved;_parent_module.cache_clear()
    parent=_parent_module()
    B=64;H=B//2;Lf=B//4-1
    assert 2*(H+B*Lf)==B*(H-1) and H>=B//64;counts['half_radix_alias_excluded_by_range']=1
    return dict(status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        parent_source_sha256=PARENT_SHA256,counts=dict(counts),ledgers=records,examples=examples,
        complete_raw_compiler=build(),complete_ordinary_compiler=build(True),
        complete_raw_tagged_parent=tagged_parent(),complete_ordinary_tagged_parent=tagged_parent(True),
        scope='Full source and exact signed graph identities to the tagged parent. Positive relation proof uses head/bound pretyping and fresh native extensions. Outer fixtures are not full Pell zeros; formal degree1936 is an upper bound.')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write',action='store_true');args=ap.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==json.loads(json.dumps(result)),'Receipt mismatch'
    print(json.dumps({k:result[k] for k in ('status','counts','ledgers','examples')},indent=2))
