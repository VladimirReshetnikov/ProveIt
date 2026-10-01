"""A positive scale coordinate removes one prescribed-AND comparison.

The algebraic rewrite accepts guarded prefixed copies of raw AND64.
Its positive theorem requires the caller's already proved q>=1 domain
and complete parent AND embedding with legitimate positive input ports.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import native_binary_masked_selection63 as native


def checked_source(source, parameters, auxiliaries):
    known=set(parameters+auxiliaries)
    assert len(known)==len(parameters)+len(auxiliaries)
    for n,op,a,b in source:
        assert n not in known and op in ('+','-','*')
        assert all(not isinstance(v,str) or v in known for v in (a,b))
        known.add(n)
    return known


def sort_source(source, inputs):
    pending=list(source);known=set(inputs);answer=[]
    assert len({n for n,_,_,_ in pending})==len(pending)
    while pending:
        next_pending=[]
        for row in pending:
            n,op,a,b=row
            if all(not isinstance(v,str) or v in known for v in (a,b)):
                assert n not in known
                answer.append(row);known.add(n)
            else:next_pending.append(row)
        assert len(next_pending)<len(pending),'cyclic or missing source dependency'
        pending=next_pending
    return answer


def metadata(packet):
    c=Counter('M' if op=='*' else 'A' for _,op,_,_ in packet['source'])
    return dict(packet,operations=len(packet['source']),multiplications=c['M'],
        additions_subtractions=c['A'],equations=len(packet['comparisons']),
        witnesses=len(packet['auxiliaries']))


def rewrite(old, prefix=''):
    """Guarded algebraic rewrite; positivity additionally needs q>=1.

    The full inverse also needs a proved complete parent AND embedding;
    the caller, not these syntactic guards, validates substituted ports.

    q and every other inherited relation retain their caller's semantics.
    The raw core retains supplied positive r, so no packed-index inference
    is used for the forward map. No arbitrary replacement of the kernel
    rows or comparison set is accepted.
    """
    assert not old.get('native_positive_scale')
    known=checked_source(old['source'],old['parameters'],old['auxiliaries'])
    assert all(not isinstance(v,str) or v in known for pair in old['comparisons'] for v in pair)
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    name=lambda n:prefix+n if isinstance(n,str) else n
    template,pairs,_=native.source('and64_prescribed')
    for n,op,a,b in template[7:]:assert rows[name(n)]==(op,name(a),name(b)),n
    q,r,w,beta,X,bound=[name(n) for n in ('q','r','w','bound_beta','wn2','bs_X_bound')]
    assert rows[q][0:2]==('*',16)
    assert r in old['auxiliaries'] and w in old['auxiliaries'] and beta in old['auxiliaries']
    expected=[(name(a),name(b)) for a,b in pairs]
    assert all(old['comparisons'].count(pair)==1 for pair in expected)
    consumers=lambda v:{n for n,_,a,b in old['source'] if v in (a,b)}
    assert consumers(w)=={X} and consumers(beta)=={bound} and consumers(bound)==set()
    removed=(bound,X)
    assert [pair for pair in old['comparisons'] if bound in pair]==[removed]
    assert all(not {w,beta}&set(pair) for pair in old['comparisons'])
    assert not {w,beta,bound}&set(old.get('public_registers',{}).values())
    # The sole query below intersects with {w,beta}; retaining only those
    # names commutes with every union and bounds each dependency set by2.
    dependencies={n:({n} if n in {w,beta} else set())
                  for n in old['parameters']+old['auxiliaries']}
    dep=lambda v:dependencies[v] if isinstance(v,str) else set()
    for n,_,a,b in old['source']:dependencies[n]=dep(a)|dep(b)
    assert not {w,beta}&(dep(q)|dep(r))
    source=[(n,'*',bound,q) if n==X else row for row in old['source'] for n in [row[0]]]
    aux=[n for n in old['auxiliaries'] if n!=w]
    source=sort_source(source,old['parameters']+aux)
    checked_source(source,old['parameters'],aux)
    packet=metadata(dict(old,source=source,
        comparisons=[p for p in old['comparisons'] if p!=removed],auxiliaries=aux,
        native_positive_scale=True,positive_scale_prefix=prefix,positive_scale_parent=old,
        positive_scale_removed_comparison=removed,
        positive_scale_registers=dict(q=q,r=r,w=w,beta=beta,X=X,bound=bound),
        positive_scale_domain='The caller proves pretyping q>=1 and a complete parent AND embedding with legitimate positive ports; r is a positive auxiliary.'))
    assert packet['operations']==len(old['source'])
    assert packet['equations']==len(old['comparisons'])-1
    assert packet['witnesses']==len(old['auxiliaries'])-1
    return packet


def build():
    source,pairs,_=native.source('and64_prescribed')
    parameters,aux=native.domains('and64_prescribed')
    return rewrite(metadata(dict(source=source,comparisons=pairs,parameters=parameters,auxiliaries=aux)))


def polynomial_source(packet):return native.parent.sos_source(packet['source'],packet['comparisons'])
execute=native.parent.execute


def degree_bound(packet):
    degree={n:1 for n in packet['parameters']+packet['auxiliaries']}
    at=lambda v:degree[v] if isinstance(v,str) else 0
    for n,op,a,b in packet['source']:degree[n]=at(a)+at(b) if op=='*' else max(at(a),at(b))
    return 2*max(max(at(a),at(b)) for a,b in packet['comparisons'])


def ledger(packet):
    s,out=polynomial_source(packet);c=Counter('M' if op=='*' else 'A' for _,op,_,_ in s)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(s),multiplications=c['M'],additions_subtractions=c['A'],
                        output=out,degree_upper_bound=degree_bound(packet),exact_degree_claimed=False))


def lift_to_parent(packet,values):
    env=execute(packet['source'],values);r=packet['positive_scale_registers']
    return dict(values,**{r['w']:env[r['bound']],r['beta']:env[r['X']]-env[r['r']]})


def project_from_parent(packet,values):
    r=packet['positive_scale_registers'];old=packet['positive_scale_parent']
    env=execute(old['source'],values)
    result={k:v for k,v in values.items() if k!=r['w']}
    result[r['beta']]=values[r['w']]-env[r['r']]
    return result


def identity_audit(packet,cases=256,seed=1086421):
    rng=random.Random(seed);old=packet['positive_scale_parent']
    source,out=polynomial_source(packet);oldsource,oldout=polynomial_source(old)
    r=packet['positive_scale_registers'];at=lambda e,v:e[v] if isinstance(v,str) else v
    for j in range(cases):
        positive=j<cases//2
        draw=lambda:rng.randrange(1,7) if positive else rng.randrange(-5,6)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        restored=lift_to_parent(packet,values)
        env=execute(source,values);before=execute(oldsource,restored)
        assert all(env[n]==before[n] for n,_,_,_ in packet['source'] if n!=r['bound'])
        a,b=packet['positive_scale_removed_comparison'];assert at(before,a)==at(before,b)
        assert env[out]==before[oldout]
        assert [at(env,a)-at(env,b) for a,b in packet['comparisons']]==[
            at(before,a)-at(before,b) for a,b in old['comparisons'] if (a,b)!=(r['bound'],r['X'])]
        assert project_from_parent(packet,restored)==values
        if positive:assert min(restored.values())>0
    return dict(complete_output_and_residual_identities=cases,signed_cases=cases-cases//2,
                coordinate_round_trips=cases,positive_forward_lifts=cases//2)


def guard_audit():
    original=build()['positive_scale_parent'];bad=[]
    def reject(packet):
        try:rewrite(packet)
        except AssertionError:bad.append(True)
        else:raise AssertionError('guard failed')
    p=copy.deepcopy(original);p['source'].append(('extra_w','+', 'w',1));reject(p)
    p=copy.deepcopy(original);p['source'].append(('extra_beta','+', 'bound_beta',1));reject(p)
    p=copy.deepcopy(original);p['source'].append(('extra_bound','+', 'bs_X_bound',1));reject(p)
    p=copy.deepcopy(original);p['comparisons'].append(('bs_X_bound','r'));reject(p)
    p=copy.deepcopy(original);p['comparisons'].append(('w','r'));reject(p)
    p=copy.deepcopy(original);p['public_registers']={'external':'bs_X_bound'};reject(p)
    p=copy.deepcopy(original);p['source']=[('q','*',16,'w') if n=='q' else row for row in p['source'] for n in [row[0]]];reject(p)
    p=copy.deepcopy(original);p['comparisons'].remove(('bs_q','q'));reject(p)
    p=copy.deepcopy(original);p['source']=[('R11','+', 'r1','r') if n=='R11' else row for row in p['source'] for n in [row[0]]];reject(p)
    p=copy.deepcopy(original);p['source']=[('q','*',8,'P') if n=='q' else row for row in p['source'] for n in [row[0]]];reject(p)
    return len(bad)


def verify():
    p=build();audit=identity_audit(p,512);s,out=polynomial_source(p)
    scalar=0
    for r in range(1,513):
        q=1<<r.bit_count();X=1<<(2*r+1);w=X//q;b=w-r
        assert X%q==0 and w>=1<<(r+1)>r and b>0 and q*(r+b)==X
        scalar+=1
    assert ledger(p)['certificate']['operations']==64
    assert ledger(p)['polynomial']['operations']==108
    return dict(status='PASS_NATIVE_BINARY_POSITIVE_SCALE',ledger=ledger(p),audit=audit,
        inverse_typed_scalar_cases=scalar,rejected_guard_mutations=guard_audit(),
        source_sha256=hashlib.sha256(json.dumps(s,sort_keys=True).encode()).hexdigest(),
        example=dict(source=s,comparisons=p['comparisons'],parameters=p['parameters'],
                     auxiliaries=p['auxiliaries'],output=out),
        scope='Complete prescribed-AND projection and positive-zero bijection. Prefixed algebraic helper '
              'requires the caller\'s pretyping q>=1 domain and unchanged complete native semantics. '
              'Scalar inverse fixtures are not full Pell zeros; no universal compiler claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['ledger'])
