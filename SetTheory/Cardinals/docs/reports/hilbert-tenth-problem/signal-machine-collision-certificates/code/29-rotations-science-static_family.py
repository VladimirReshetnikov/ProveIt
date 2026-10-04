#!/usr/bin/env python3
"""Owned exact symbolic constructor. No trajectory, event-selection, or old-code imports."""
from fractions import Fraction as F
from math import gcd, ceil, isqrt
import json, hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def add(v,w): return tuple(a+b for a,b in zip(v,w))
def sub(v,w): return tuple(a-b for a,b in zip(v,w))
def mul(a,v): return tuple(a*b for b in v)
def dot(v,w): return sum((a*b for a,b in zip(v,w)),F(0))
def mm(a,b): return tuple(tuple(dot(r,c) for c in zip(*b)) for r in a)
def scale(v,a): return mul(a,v)
def ser(v):
    if isinstance(v,F): return str(v)
    if isinstance(v,dict): return {str(k):ser(x) for k,x in v.items()}
    if isinstance(v,(list,tuple)): return [ser(x) for x in v]
    return v
D=(F(1),F(0),F(0)); XX=(F(0),F(1),F(0)); YY=(F(0),F(0),F(1))

def construct(a,b,c,lam=F(1,2)):
    lam=F(lam)
    assert lam>0
    scaled=lam!=1
    assert c>1 and a*a+b*b==c*c and gcd(gcd(abs(a),abs(b)),c)==1
    assert a and b and c%2 and gcd(a,c)==gcd(b,c)==1
    tx=F(-b,c+a); ty=F(b,c)
    nx=max(1,ceil(4*abs(tx))); ny=max(1,ceil(4*abs(ty)))
    dx=tx/nx; dy=ty/ny; K=2*nx+ny
    assert 0<abs(dx)<=F(1,4) and 0<abs(dy)<=F(1,4)
    x=add(mul(F(1,3),D),XX); y=add(mul(F(2,3),D),YY)
    guards=[]; phases=[]; events=[]; temps={}; ell=(F(0),)*3
    def guard(row,name):
        assert row[0]>0, (name,row)
        guards.append({'name':name,'row':row})
    def emit(identity,role,eps,speed=None):
        # eps is incoming messenger direction; roles determine outgoing direction
        out=-eps if role in ('Llaunch','Lrestore','bounce') else eps
        events.append({'marker':identity,'role':role,'in_speed':F(eps),'out_speed':F(out),'target_speed':speed})
        return out
    def L(target,anchor,inner,u,eps,name):
        speed=eps*(u-1)/(u+1)
        temp=target+'_'+name; temps[temp]=speed
        start=len(events); direction=eps
        for z in inner: direction=emit(z,'cross',direction)
        direction=emit(target,'Llaunch',direction,speed); events[-1]['temporary']=temp
        for z in reversed(inner): direction=emit(z,'cross',direction)
        direction=emit(anchor,'bounce',direction)
        for z in inner: direction=emit(z,'cross',direction)
        direction=emit(target,'Lrestore',direction,speed); events[-1]['temporary']=temp
        for z in reversed(inner): direction=emit(z,'cross',direction)
        direction=emit(anchor,'bounce',direction)
        assert direction==eps
        phases.append({'name':name,'kind':'L','start':start,'stop':len(events),'target':target,'parameter':u})
    def H(target,anchor,reflector,between,v,eps,name):
        speed=eps*(1-v)/(1+v)
        temp=target+'_'+name; temps[temp]=speed
        start=len(events); direction=eps
        direction=emit(target,'Hlaunch',direction,speed); events[-1]['temporary']=temp
        for z in between: direction=emit(z,'cross',direction)
        direction=emit(reflector,'bounce',direction)
        for z in reversed(between): direction=emit(z,'cross',direction)
        direction=emit(target,'Hrestore',direction,speed); events[-1]['temporary']=temp
        direction=emit(anchor,'bounce',direction)
        assert direction==eps
        phases.append({'name':name,'kind':'H','start':start,'stop':len(events),'target':target,'parameter':v})
    def translation(t,z,delta,target,anchor,reflector,between,eps,name):
        nonlocal ell
        u=1/(1-delta); v=1-delta
        assert u>0 and v>0
        ell=add(ell,add(mul(2+2*u,t),mul(2,z)))
        L(target,anchor,[],u,eps,name+'_L')
        H(target,anchor,reflector,between,v,eps,name+'_H')
        return add(t,mul(delta,z))
    def shear(axis,n,delta,block):
        nonlocal x,y
        if axis=='x':
            t,z=x,y; target,anchor,near,far,eps='X','L','Y','D',1
        else:
            t,z=sub(D,y),sub(D,x); target,anchor,near,far,eps='Y','D','X','L',-1
        guard(z,block+'_fixed_lower'); guard(sub(D,z),block+'_fixed_upper')
        guard(t,block+'_endpoint0_lower'); guard(sub(z,t),block+'_endpoint0_upper')
        for j in range(n):
            t=translation(t,z,delta,target,anchor,near,[],eps,f'{block}_{j}_near')
            guard(t,f'{block}_endpoint{2*j+1}_lower'); guard(sub(z,t),f'{block}_endpoint{2*j+1}_upper')
            t=translation(t,D,-F(2,3)*delta,target,anchor,far,[near],eps,f'{block}_{j}_far')
            guard(t,f'{block}_endpoint{2*j+2}_lower'); guard(sub(z,t),f'{block}_endpoint{2*j+2}_upper')
        if axis=='x': x=t
        else: y=sub(D,t)
    def transfer(right):
        nonlocal ell
        start=len(events); direction=1 if right else -1
        ids=['X','Y','D'] if right else ['Y','X','L']
        for z in ids[:-1]: direction=emit(z,'cross',direction)
        direction=emit(ids[-1],'bounce',direction)
        ell=add(ell,D)
        phases.append({'name':'transfer_right' if right else 'transfer_left','kind':'transfer','start':start,'stop':len(events)})
    shear('x',nx,dx,'A1'); transfer(True); shear('y',ny,dy,'B'); transfer(False); shear('x',nx,dx,'A2')
    rotation_x=x; rotation_y=y
    assert sub(x,mul(F(1,3),D))==(F(0),F(a,c),F(-b,c))
    assert sub(y,mul(F(2,3),D))==(F(0),F(b,c),F(a,c))
    if scaled:
        ell=add(ell,mul(2*(1+lam),add(add(x,y),D)))
        scale_plan=[('X',[]),('Y',['X']),('D',['X','Y'])]
        if lam>1: scale_plan.reverse()
        for target,inner in scale_plan:
            L(target,'L',inner,lam,1,'scale_'+target)
    m=len(events)
    assert m==18*K+6+24*scaled
    assert len(guards)==4*K+12
    assert len(temps)==4*K+3*scaled
    speeds={**{z+'0':F(0) for z in ['L','X','Y','D']},**temps}
    rules=[]
    for j,e in enumerate(events): speeds['Q'+str(j)]=e['in_speed']
    for j,e in enumerate(events):
        assert e['out_speed']==events[(j+1)%m]['in_speed']
        stat=e['marker']+'0'; temp=e.get('temporary')
        zin=temp if e['role'].endswith('restore') else stat
        zout=temp if e['role'].endswith('launch') else stat
        rule={'in':['Q'+str(j),zin],'out':['Q'+str((j+1)%m),zout]}
        assert speeds[rule['in'][0]]!=speeds[rule['in'][1]]
        assert speeds[rule['out'][0]]!=speeds[rule['out'][1]]
        rules.append(rule)
    assert events[0]['in_speed']==events[-1]['out_speed']==1
    distances=[]
    for g in guards:
        h,v,w=g['row']; norm=v*v+w*w
        if norm: distances.append((h*h/norm,(-h*v/norm,-h*w/norm),g['name']))
    rho2=min(d[0] for d in distances)
    nearest=[d for d in distances if d[0]==rho2]
    points=sorted(set(d[1] for d in nearest))
    for p in points:
        assert dot(p,p)==rho2
        assert all(dot(g['row'],(F(1),)+p)>=0 for g in guards)
    M=tuple(tuple(lam*F(v,3*c) for v in row) for row in [
       [c+2*a-b,c-a-b,c-a+2*b],
       [c-a+3*b,c+2*a,c-a-3*b],
       [c-a-2*b,c-a+b,c+2*a+b]])
    Q=((F(1),F(1),F(1)),(F(2,3),F(-1,3),F(-1,3)),(F(1,3),F(1,3),F(-2,3)))
    N=((lam,F(0),F(0)),(F(0),lam*F(a,c),lam*F(-b,c)),(F(0),lam*F(b,c),lam*F(a,c)))
    assert mm(Q,M)==mm(N,Q)
    return {'parameters':{'a':a,'b':b,'c':c,'lambda':lam,'tx':tx,'ty':ty,'Nx':nx,'Ny':ny},'counts':{'events':m,'meta_signals':len(speeds),'temporary_labels':len(temps),'guards':len(guards),'distinct_speeds':len(set(speeds.values())),'distinct_nearest_points':len(points)},'return_gap_matrix':M,'duration_row':ell,'guards':guards,'rho_squared':rho2,'nearest_guards':nearest,'tangent_points':points,'phases':phases,'speeds':speeds,'rules':rules,'default_rule':'Identity on every other pairwise-distinct-speed collision input set'}

def run():
    fixtures=[(3,4,5),(3,-4,5),(-3,4,5),(-3,-4,5),(4,3,5),(4,-3,5),(-4,3,5),(-4,-3,5),(5,12,13),(-5,12,13),(12,5,13),(-12,5,13),(119,120,169),(-119,120,169),(120,-119,169)]
    summary=[]
    for a,b,c in fixtures:
        for lam in (F(1),F(1,2),F(2)):
            result=construct(a,b,c,lam)
            name=f'a{a}_b{b}_c{c}_scale{lam.numerator}over{lam.denominator}.json'
            data=(json.dumps(ser(result),sort_keys=True,indent=2)+'\n').encode()
            (ROOT/'evidence'/name).write_bytes(data)
            summary.append({'file':name,'sha256':hashlib.sha256(data).hexdigest(),**result['parameters'],**result['counts'],'rho_squared':result['rho_squared'],'tangent_points':result['tangent_points']})
    receipt={'scope':'Exact symbolic endpoint and static rule grammar checks only; no trajectory or event-selection simulation','fixture_count':len(summary),'fixtures':summary}
    (ROOT/'evidence'/'STATIC_RECEIPT.json').write_text(json.dumps(ser(receipt),sort_keys=True,indent=2)+'\n')
    print(json.dumps(ser(receipt),indent=2))
if __name__=='__main__': run()
