#!/usr/bin/env python3
"""Degree-two trace certificates for arbitrary reset nets, with optional proved
one-hot finite-control projection. No test/inhibitor arcs; resets may overlap
ordinary input and output arcs. Natural or nonnegative-real witnesses."""
from source_quadratic import affine

def compile_schema(net,T,*,project_controls=False,initial=None,target=None):
    assert type(T) is int and T>=1
    ts=net['transitions']; allp=net['places']
    assert len(set(allp))==len(allp)
    for t in ts:
        assert set(t['pre'])|set(t['post'])|set(t['reset'])<=set(allp)
        assert all(type(v) is int and v>=0 for side in ('pre','post') for v in t[side].values())
        assert len(t['reset'])==len(set(t['reset']))
    initial=net['initial_affine'] if initial is None else initial
    target=net['target'] if target is None else target
    def affmark(x):return {p:({'constant':v} if type(v) is int else v) for p,v in x.items()}
    initial=affmark(initial);target=affmark(target)
    assert set(initial)|set(target)<=set(allp)
    assert all(type(c) is int for end in (initial,target) for terms in end.values() for c in terms.values())
    controls=net.get('control_places',[]) if project_controls else []
    data=[p for p in allp if p not in controls];d=len(data);m=len(ts);stride=m*(d+1)
    code={p:i for i,p in enumerate(controls)};src=[];dst=[]
    if project_controls:
        for t in ts:
            a=[p for p in t['pre'] if p in code];b=[p for p in t['post'] if p in code]
            assert len(a)==len(b)==1 and t['pre'][a[0]]==t['post'][b[0]]==1
            assert not (set(t['reset'])&set(controls))
            src.append(code[a[0]]);dst.append(code[b[0]])
        for endpoint in (initial,target):
            vals=[endpoint.get(p,{}) for p in controls]
            assert all(set(v)<= {'constant'} for v in vals) and sum(v.get('constant',0) for v in vals)==1
            assert all(v.get('constant',0) in (0,1) for v in vals)
        entry=sum(code[p]*initial.get(p,{}).get('constant',0) for p in controls)
        final=sum(code[p]*target.get(p,{}).get('constant',0) for p in controls)
    parameters={k:'natural integer' for end in (initial,target) for v in end.values() for k in v if k!='constant'}
    groups={};squares=[];products=[]
    def e(j,r):return j*stride+r
    def b(j,r,i):return j*stride+m+r*d+i
    def f(j,n):return f'{n}:{j}'
    for j in range(T):
        groups[f(j,'E')]=[[e(j,r),1] for r in range(m)]
        squares.append({'name':f'onehot:{j}','affine':affine(forms=[(f(j,'E'),1)],constant=-1)})
        if project_controls:
            groups[f(j,'Q')]=[[e(j,r),src[r]] for r in range(m) if src[r]]
            groups[f(j,'D')]=[[e(j,r),dst[r]] for r in range(m) if dst[r]]
            squares.append({'name':f'control:{j}','affine':affine(forms=[(f(j,'Q'),1)]+([] if j==0 else [(f(j-1,'D'),-1)]),constant=-entry if j==0 else 0)})
        for i,p in enumerate(data):
            old=[];new=[]
            for r,t in enumerate(ts):
                old.append([b(j,r,i),1])
                if t['pre'].get(p,0):old.append([e(j,r),t['pre'][p]])
                if p not in t['reset']:new.append([b(j,r,i),1])
                if t['post'].get(p,0):new.append([e(j,r),t['post'][p]])
            groups[f(j,f'OLD{i}')]=old;groups[f(j,f'NEW{i}')]=new
            init=initial.get(p,{})
            squares.append({'name':f'place:{j}:{p}','affine':affine(
                forms=[(f(j,f'OLD{i}'),1)]+([] if j==0 else [(f(j-1,f'NEW{i}'),-1)]),
                parameters=[(k,-v) for k,v in init.items() if k!='constant'] if j==0 else [],
                constant=-init.get('constant',0) if j==0 else 0)})
        for r in range(m):
            products.append({'name':f'gate:{j}:{r}',
                'left':affine(forms=[(f(j,'E'),1)],variables=[(e(j,r),-1)]),
                'right':affine(variables=[(e(j,r),1)]+[(b(j,r,i),1) for i in range(d)])})
    for i,p in enumerate(data):
        end=target.get(p,{})
        squares.append({'name':'terminal:'+p,'affine':affine(forms=[(f(T-1,f'NEW{i}'),1)],parameters=[(k,-v) for k,v in end.items() if k!='constant'],constant=-end.get('constant',0))})
    if project_controls:squares.append({'name':'terminal:control','affine':affine(forms=[(f(T-1,'D'),1)],constant=-final)})
    ledger={'natural_witnesses':stride*T,'affine_squares':(d+1+int(project_controls))*T+d+int(project_controls),'quadratic_products':m*T,'degree_at_most':2}
    assert len(squares)==ledger['affine_squares'] and len(products)==ledger['quadratic_products']
    return {'format':'reset-net-affine-orthants-v1','external_firings':T,'projected_controls':project_controls,'data_places':data,
      'parameters':parameters,'variables':{'count':stride*T,'per_step':stride,'transition_count':m,'data_dimension':d},
      'linear_forms':groups,'affine_squares':squares,'quadratic_products':products,'ledger':ledger,
      'indexing':'step j selector of transition r: j*stride+r; base for place i of transition r: j*stride+m+r*d+i',
      'polynomial':'sum of listed affine squares plus listed products; all summands globally nonnegative on the nonnegative orthant',
      'scope':'Exact transition-labelled traces of the given fixed length; one witness per labelled trace. The nonnegative-real zero set equals the natural zero set for natural endpoint parameters.'}

def trace_witness(net,trace,project_controls=False):
    data=[p for p in net['places'] if not(project_controls and p in net['control_places'])]
    d=len(data);m=len(net['transitions']);stride=m*(d+1);w={}
    for j,row in enumerate(trace):
        r=row['transition'];t=net['transitions'][r];w[j*stride+r]=1
        for i,p in enumerate(data):
            v=row['old'].get(p,0)-t['pre'].get(p,0)
            assert v>=0
            if v:w[j*stride+m+r*d+i]=v
    return w
