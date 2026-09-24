#!/usr/bin/env python3
"""Fixed-frame native flag projection adapter; no complete-machine count."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import explore_nondeterministic_program_routing as router


def symbolic():
    W,K,g,I,F,C,V,q,J,h,Fk=sp.symbols('W K g I F C V q J h Fk')
    old=(W*K-g)*C+g*I-g*F*q-W*(V+h*(Fk-J))
    new=2*(W*K-g)*C+2*g*I-W*h-(2*g*F-W*h)*q-2*W*(V+h*Fk)
    assert sp.expand(new-2*old-W*h*(q-2*J-1))==0
    hs=sp.symbols('h0:3');flags=sp.symbols('Fk0:3')
    old3=(W*K-g)*C+g*I-g*F*q-W*(V+sum(a*(b-J) for a,b in zip(hs,flags)))
    new3=2*(W*K-g)*C+2*g*I-W*sum(hs)-(2*g*F-W*sum(hs))*q-2*W*(V+sum(a*b for a,b in zip(hs,flags)))
    assert sp.expand(new3-2*old3-W*sum(hs)*(q-2*J-1))==0
    return dict(single_flag_correction=sp.sstr(W*h*(q-2*J-1)),
                three_flag_correction=sp.sstr(W*sum(hs)*(q-2*J-1)))


def constants(m,edges,labels):
    assert len(labels)==m and all(x in (0,1) for x in labels)
    spacing=2
    while 3**spacing<=m or (spacing-m)%2:spacing+=1
    a=[spacing*3**i for i in range(m)]
    b=spacing*3**m;d=b
    positions=[d+a[j]-a[i] for i,j in edges]+[d-a[i] for i in range(m)]
    positions += [d+b-a[i] for i in range(m) if labels[i]]
    assert len(set(positions))==len(positions) and min(positions)>=0
    K=sum(3**e for e in positions);S=sum(3**e for e in a);g=3**d;h=3**(d+b)
    Z=sum(3**(d+j) for j in range(1,spacing))+h
    B=2;W=9
    while W<=max(K*S,g*S,2*S+1,Z):W*=9;B+=2
    return dict(m=m,edges=edges,labels=labels,a=a,d=d,b=b,positions=positions,
                K=K,S=S,g=g,h=h,Z=Z,B=B,W=W,spacing=spacing)


def schedule(c,I,F):
    W,K,g,h=[c[n] for n in ('W','K','g','h')]
    return [('scaled_C','*',2*(W*K-g),'C'),
            ('left','+','scaled_C',2*g*I-W*h),
            ('native_flag','*',h,'Fk'),('projected_junk','+','V','native_flag'),
            ('scaled_q','*',2*g*F-W*h,'q'),
            ('scaled_junk','*',2*W,'projected_junk'),
            ('right','+','scaled_q','scaled_junk')]


def eval_schedule(ops,values):
    env=dict(values)
    for name,op,left,right in ops:
        a=env[left] if isinstance(left,str) else left
        b=env[right] if isinstance(right,str) else right
        env[name]=a*b if op=='*' else a+b
    return env


def regression():
    tables=paths=typed_candidates=accepted=rejected=coefficient_cases=0
    instructions=None
    graphs=[(2,[(0,1),(1,0)]),(3,[(0,1),(0,2),(1,2),(2,0)]),
            (3,[(i,j) for i in range(3) for j in range(3) if i!=j])]
    for m,edges in graphs:
        for labels in product((0,1),repeat=m):
            c=constants(m,edges,labels);tables+=1
            W,K,g,h,S,Z=[c[n] for n in ('W','K','g','h','S','Z')]
            # Full source subsets include malformed rows with multiple states.
            for mask in range(1<<m):
                word=sum(3**c['a'][i] for i in range(m) if mask>>i&1)
                value=K*word
                assert value<W
                assert value//3**c['d']%(3**c['spacing'])==mask.bit_count()
                assert value//h%(3**c['spacing'])==sum(labels[i] for i in range(m) if mask>>i&1)
                coefficient_cases+=2
            for height in range(1,4):
                for path in product(range(m),repeat=height+1):
                    if not all((a,b) in edges for a,b in zip(path,path[1:])):continue
                    paths+=1;q=W**height;H=(q-1)//(W-1);J=(q-1)//2
                    I=3**c['a'][path[0]];F=3**c['a'][path[-1]]
                    C=sum(3**c['a'][s]*W**j for j,s in enumerate(path[:-1]))
                    Next=sum(3**c['a'][s]*W**j for j,s in enumerate(path[1:]))
                    Q=sum(labels[s]*W**j for j,s in enumerate(path[:-1]))
                    V=K*C-g*Next-h*Q
                    TC=C+J-S*H;TV=V+Z*H;alpha=q-TC-TV
                    assert min(C,V,TC,TV,alpha)>0
                    assert all(router.base.old.boolean(z) and z<q for z in (C,V,TC,TV))
                    P=C+q*V+q*q*TC+q**3*TV
                    assert P%2==0 and router.base.old.boolean(P)
                    ops=schedule(c,I,F)
                    if instructions is None:instructions=ops
                    for bits in product((0,1),repeat=height):
                        Qt=sum(b*W**j for j,b in enumerate(bits));Fk=J+Qt
                        typed_candidates+=1
                        env=eval_schedule(ops,dict(C=C,V=V,q=q,Fk=Fk))
                        old=(W*K-g)*C+g*I-g*F*q-W*(V+h*Qt)
                        assert env['left']-env['right']==2*old
                        passes=env['left']==env['right']
                        assert passes==(Qt==Q)
                        if passes:accepted+=1
                        else:rejected+=1
    assert accepted==paths
    return dict(labelled_tables=tables,marker_and_label_subset_checks=coefficient_cases,
                canonical_paths=paths,typed_flag_candidates=typed_candidates,
                accepted_correct_flags=accepted,rejected_false_flags=rejected,
                sample_instructions=instructions)


def verify():
    identity=symbolic();finite=regression()
    counts={'*':sum(row[1]=='*' for row in finite['sample_instructions']),
            '+':sum(row[1]=='+' for row in finite['sample_instructions'])}
    assert counts=={'*':4,'+':3}
    return dict(status='PASS_FIXED_FRAME_NATIVE_OPCODE_PROJECTION',operations=7,
                primitive_histogram=counts,increment_over_unprojected_routing=2,
                symbolic=identity,regression=finite,
                proof='../1980/EXPLORATION_NATIVE_OPCODE_PROJECTION.md',
                scope='Conditional fixed-frame adapter to already typed native flags; not a complete joint counter/router system or universal bound.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['operations'],result['primitive_histogram'])
    print({k:v for k,v in result['regression'].items() if k!='sample_instructions'})
