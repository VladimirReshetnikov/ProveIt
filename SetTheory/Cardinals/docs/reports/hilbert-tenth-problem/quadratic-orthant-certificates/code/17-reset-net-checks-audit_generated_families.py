#!/usr/bin/env python3
"""Exercise reviewed compiler code with independent coefficient and Fraction evaluators."""
from pathlib import Path
from collections import Counter
from itertools import product
from fractions import Fraction
import sys, json, random, os, argparse
sys.dont_write_bytecode=True
A=Path(__file__).resolve().parent
_parser=argparse.ArgumentParser(description=__doc__)
_parser.add_argument('packet_root', nargs='?', default=os.environ.get('RESET_NET_PACKET_ROOT', str(A.parent)), help='Reset-net packet root; defaults to RESET_NET_PACKET_ROOT or the parent of this script directory')
R=Path(_parser.parse_args().packet_root).expanduser().resolve()
if not (R/'reset_net.json').is_file():
    _parser.error('packet_root must contain reset_net.json')
sys.path.insert(0,str(R))
import reset_quadratic, peak_quadratic, source_quadratic
net=json.loads((R/'reset_net.json').read_text());program=json.loads((R/'source/virtual3.json').read_text())
def canonical(terms):
    c=Counter()
    for k,v in terms:c[k]+=v
    return {k:v for k,v in c.items() if v}
def aff(p,a):
    terms=[('constant',a['constant'])]+[(f'v{i}',v) for i,v in a['variables']]+[(f'p{k}',v) for k,v in a['parameters']]
    for f,mult in a['forms']:terms += [(f'v{i}',v*mult) for i,v in p['linear_forms'][f]]
    return canonical(terms)
def val(p,w,params):
    def ev(a):
        c=aff(p,a)
        return sum(v*(1 if k=='constant' else params[k[1:]] if k[0]=='p' else w.get(int(k[1:]),0)) for k,v in c.items())
    total=0
    for a in p['affine_squares']:total+=ev(a['affine'])**2
    for a in p['quadratic_products']:
        x,y=ev(a['left']),ev(a['right']);assert x>=0 and y>=0
        total+=x*y
    return total

def check_reset_coefficients(p,N,T,projected):
    # Independently construct the actual affine maps of each disjoint branch orthant.
    controls=N.get('control_places',[]) if projected else [];data=[x for x in N['places'] if x not in controls]
    trans=N['transitions'];m=len(trans);d=len(data);stride=m*(d+1);q={x:i for i,x in enumerate(controls)}
    sq={x['name']:aff(p,x['affine']) for x in p['affine_squares']}
    oldrows={};newrows={};Q={};D={}
    for j in range(T):
        es=[f'v{j*stride+r}' for r in range(m)]
        assert sq[f'onehot:{j}']==canonical([(e,1) for e in es]+[('constant',-1)])
        for i,place in enumerate(data):
            old=[];new=[]
            for r,t in enumerate(trans):
                b=f'v{j*stride+m+r*d+i}';old += [(b,1),(es[r],t['pre'].get(place,0))]
                if place not in t['reset']:new += [(b,1)]
                new += [(es[r],t['post'].get(place,0))]
            oldrows[j,i]=old;newrows[j,i]=new
            init=N['initial_affine'].get(place,{})
            if type(init) is int:init={'constant':init}
            want=old+([(k,-c) for k,c in newrows[j-1,i]] if j else [(('constant' if k=='constant' else 'p'+k),-c) for k,c in init.items()])
            assert sq[f'place:{j}:{place}']==canonical(want)
        if projected:
            Q[j]=[(es[r],sum(q[x]*c for x,c in t['pre'].items() if x in q)) for r,t in enumerate(trans)]
            D[j]=[(es[r],sum(q[x]*c for x,c in t['post'].items() if x in q)) for r,t in enumerate(trans)]
            old=Q[j]+([(k,-c) for k,c in D[j-1]] if j else [('constant',-sum(q[x]*N['initial_affine'].get(x,{}).get('constant',0) for x in controls))])
            assert sq[f'control:{j}']==canonical(old)
        for r in range(m):
            term=p['quadratic_products'][j*m+r]
            assert aff(p,term['left'])=={e:1 for e in es if e!=es[r]}
            assert aff(p,term['right'])=={k:1 for k in [es[r]]+[f'v{j*stride+m+r*d+i}' for i in range(d)]}
    for i,place in enumerate(data):
        end=N['target'].get(place,{})
        if type(end) is int:end={'constant':end}
        want=newrows[T-1,i]+[(('constant' if k=='constant' else 'p'+k),-c) for k,c in end.items()]
        assert sq['terminal:'+place]==canonical(want)
    if projected:assert sq['terminal:control']==canonical(D[T-1]+[('constant',-sum(q[x]*N['target'].get(x,0) for x in controls))])
    assert p['variables']['count']==stride*T
    assert len(sq)==(d+1+projected)*T+d+projected and len(p['quadratic_products'])==m*T

for T in (1,2,3):
    packet=reset_quadratic.compile_schema(net,T,project_controls=True)
    check_reset_coefficients(packet,net,T,True)
# Generic weighted consumption/reset/production: enabledness precedes reset and output survives.
weighted=disabled=mutations=0
for av,bv,c0,c1,mask in product(range(3),range(3),range(4),range(4),range(4)):
    # Two coordinates with unequal weights; some resets overlap both input and output.
    pre={'x':av,'y':bv};post={'x':bv,'y':av};old={'x':c0,'y':c1}
    resets=[p for i,p in enumerate(['x','y']) if (mask>>i)&1]
    pre={p:v for p,v in pre.items() if v};post={p:v for p,v in post.items() if v}
    t={'name':'t','pre':pre,'post':post,'reset':resets}
    if any(old[p]<v for p,v in pre.items()):disabled+=1;continue
    new={p:post.get(p,0)+(0 if p in resets else old[p]-pre.get(p,0)) for p in old}
    N={'places':['x','y'],'transitions':[t],'initial_affine':old,'target':new}
    p=reset_quadratic.compile_schema(N,1);check_reset_coefficients(p,N,1,False)
    w={0:1,1:c0-av,2:c1-bv};assert val(p,w,{})==0
    for i in range(3):
        b=w.copy();b[i]+=1;assert val(p,b,{})>0;mutations+=1
    wrong=N.copy();wrong['target']={**new,'x':new['x']+1}
    assert val(reset_quadratic.compile_schema(wrong,1),w,{})>0;mutations+=1
    weighted+=1
# Random small, labelled nondeterministic traces with integer and fractional-adversarial witnesses.
rng=random.Random(20261002);random_traces=0;fractional=0
for case in range(120):
    d=rng.randrange(1,5);m=rng.randrange(2,6);T=rng.randrange(1,6);ps=[f'x{i}' for i in range(d)]
    ts=[]
    for r in range(m):
        ts.append({'name':f't{r}','pre':{p:v for p in ps if (v:=rng.randrange(3))},'post':{p:v for p in ps if (v:=rng.randrange(3))},'reset':[p for p in ps if rng.randrange(2)]})
    mark={p:rng.randrange(2,8) for p in ps};initial=mark.copy();w={};trace=[]
    for j in range(T):
        enabled=[r for r,t in enumerate(ts) if all(mark[p]>=v for p,v in t['pre'].items())]
        if not enabled:break
        r=rng.choice(enabled);t=ts[r];stride=m*(d+1);w[j*stride+r]=1
        for i,p in enumerate(ps):w[j*stride+m+r*d+i]=mark[p]-t['pre'].get(p,0)
        trace.append(r);mark={p:t['post'].get(p,0)+(0 if p in t['reset'] else mark[p]-t['pre'].get(p,0)) for p in ps}
    T=len(trace)
    if not T:continue
    N={'places':ps,'transitions':ts,'initial_affine':initial,'target':mark}
    packet=reset_quadratic.compile_schema(N,T);check_reset_coefficients(packet,N,T,False)
    assert val(packet,w,{})==0
    for j,r in enumerate(trace):
        bad=w.copy();bad[j*stride+r]=Fraction(1,2);bad[j*stride+(r+1)%m]=Fraction(1,2)
        assert val(packet,bad,{})>0;fractional+=1
    random_traces+=1
# Source and canonical extension coefficients at several horizons, not just the h=1 export.
labels=list(program['rows'])+['HALT'];codes={q:i for i,q in enumerate(labels)};bs=[]
for q,(op,r,*dst) in program['rows'].items():
    bs.append((codes[q],codes[dst[0]],r,'inc' if op=='ADD' else 'pos'))
    if op=='SUB':bs.append((codes[q],codes[dst[1]],r,'zero'))
nb=len(bs);layout=[];k=nb
for _,_,r,op in bs:
    row=[]
    for i in range(3):
        row.append(None if op=='zero' and i==r else k)
        if row[-1] is not None:k+=1
    layout.append(row)
assert k==2811
for h in (1,2,3):
    p=peak_quadratic.compile_peak(source_quadratic.semantic_table(program),h)
    assert p['variables']['count']==2813*h and len(p['affine_squares'])==6*h+2 and len(p['quadratic_products'])==762*h
    sq={x['name']:aff(p,x['affine']) for x in p['affine_squares']};news={};ds={}
    for j in range(h):
        selectors=[f'v{2811*j+r}' for r in range(nb)]
        assert sq[f'onehot:{j}']==canonical([(x,1) for x in selectors]+[('constant',-1)])
        qs=[(selectors[b],q) for b,(q,z,r,op) in enumerate(bs)];ds[j]=[(selectors[b],z) for b,(q,z,r,op) in enumerate(bs)]
        assert sq[f'control:{j}']==canonical(qs+([(x,-c) for x,c in ds[j-1]] if j else [('constant',-codes[program['entry']])]))
        for i in range(3):
            old=[];new=[]
            for b,(q,z,r,op) in enumerate(bs):
                if layout[b][i] is not None:
                    idx=f'v{2811*j+layout[b][i]}';old.append((idx,1));new.append((idx,1))
                if i==r and op=='pos':old.append((selectors[b],1))
                if i==r and op=='inc':new.append((selectors[b],1))
            news[j,i]=new
            prev=[(x,-c) for x,c in news[j-1,i]] if j else [('pL',-1)] if i==0 else [('pR',-1)] if i==1 else []
            assert sq[f'counter{i}:{j}']==canonical(old+prev)
        peak=sum([news[j-1,i] for i in range(3)],[])+[(f'v{2811*h+2*j-1}',1)] if j else [('pL',1),('pR',1)]
        peak += [(f'v{2811*h+2*j}',1),(f'v{2811*h+2*j+1}',-1)]+[(x,-c) for i in range(3) for x,c in news[j,i]]
        assert sq[f'peak:{j}']==canonical(peak)
        for b,term in enumerate(p['quadratic_products'][j*nb:(j+1)*nb]):
            assert aff(p,term['left'])=={x:1 for i,x in enumerate(selectors) if i!=b}
            assert aff(p,term['right'])=={x:1 for x in [selectors[b]]+[f'v{2811*j+k}' for k in layout[b] if k is not None]}
        term=p['quadratic_products'][nb*h+j]
        assert aff(p,term['left'])=={f'v{2811*h+2*j}':1} and aff(p,term['right'])=={f'v{2811*h+2*j+1}':1}
    assert sq['terminal']==canonical(ds[h-1]+[('constant',-codes['HALT'])])
    duration=[('pN',1),('pL',1),('pR',1),('constant',-h-5),(f'v{2813*h-1}',-2)]+[(x,-3*c) for i in range(3) for x,c in news[h-1,i]]
    assert sq['minimum_reset_duration']==canonical(duration)
result={'status':'PASS','generic_weighted_2place_reset_cases':weighted,'disabled_weighted_inputs_excluded':disabled,'single_coordinate_or_endpoint_mutations_rejected':mutations,'random_nondeterministic_labelled_traces':random_traces,'mixed_fractional_selectors_rejected':fractional,'projected_reset_coefficients_horizons':[1,2,3],'source_and_peak_coefficients_horizons':[1,2,3],'method':'Actual reviewed compilers called; all coefficients and values checked by independent implementations. Fractions use exact rational arithmetic.'}
(A/'GENERATED_FAMILIES_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
