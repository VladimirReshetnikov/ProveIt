#!/usr/bin/env python3
"""A complete outer counterexample to omitting the Z mask, even with D typed.

This is a mathematical source-interface regression, not a cheaper SLP claim.
The full positive Pell tuple is supplied by the existing general converse.
"""
from pathlib import Path
import json


def digits(n):
    out=set();i=0
    while n:
        n,r=divmod(n,3)
        assert r in (0,1)
        if r:out.add(i)
        i+=1
    return out


def program():
    offsets=[];sums=set();n=0
    while len(offsets)<20:
        added=[n+a for a in offsets]+[2*n]
        if len(set(added))==len(added) and not set(added)&sums:
            offsets.append(n);sums.update(added)
        n+=1
    ell=3;base=max(offsets)+1
    coordinates=[ell*(base+a) for a in offsets]
    coordinates[1],coordinates[6]=coordinates[6],coordinates[1]
    a=coordinates[:18];bs,bz=coordinates[18:];d=max(coordinates)
    assert min(coordinates)*2>max(coordinates)
    pair_sums=[coordinates[i]+coordinates[j] for i in range(20) for j in range(i,20)]
    assert len(pair_sums)==len(set(pair_sums))
    signs=[1,1,1,-1,-1,-1]*2+[-1,1,1,-1,-1,-1]
    zeros=[0]*18
    for i in (1,2,6,7,8):zeros[i]=1
    edges=[(i,i+1) for i in range(17)]+[(17,12),(17,0)]
    positions=[d+a[j]-a[i] for i,j in edges]+[d-ai for ai in a]
    positions += [d+bs-a[i] for i in range(18) if signs[i]==1]
    positions += [d+bz-a[i] for i in range(18) if zeros[i]==0]
    assert len(positions)==len(set(positions)) and min(positions)>=0
    assert all(e%ell==0 for e in positions)
    K=sum(3**e for e in positions);S=sum(3**e for e in a)
    g=3**d;hs=3**(d+bs);hz=3**(d+bz)
    forbidden={d+1,d+2,d+bs,d+bz}
    Zold=sum(3**e for e in forbidden)
    bound=max(K*S,g*S,6*(hs+hz),Zold,3*S,9)
    e=0;E=1
    while E<=bound:E*=3;e+=1
    assert e not in forbidden
    forbidden.add(e);Zstar=Zold+E
    R=1;width=0
    while R<=max(2*Zstar+1,K*S,g*S):R*=3;width+=1
    return dict(a=a,bs=bs,bz=bz,d=d,ell=ell,signs=signs,zeros=zeros,
                edges=edges,positions=set(positions),K=K,S=S,g=g,hs=hs,hz=hz,
                forbidden=forbidden,Zstar=Zstar,R=R,width=width)


def pack(rows,R):
    value=0
    for row in reversed(rows):value=value*R+row
    return value


def verify():
    c=program();R=c['R'];m=c['width'];h=c['a'][6]-c['a'][0]
    assert h==3 and c['zeros'][0]==0 and c['zeros'][6]==c['zeros'][7]==1
    x=3**h
    path=list(range(12))+list(range(12,18))*x+[0]
    u=len(path)-1;q=R**u;W=R**3;J=(q-1)//2;H=(q-1)//(R-1)
    jr=(R-1)//2;rep=(R-3)//6
    assert u%6==0 and m>h+2 and 2*x<R
    values=[2*x,0,0];rows={n:[] for n in ('A0','A1','T','Kp','Km','D','C','V','TC','TV')}
    oldDs=[];oldVs=[];false=[];native_checks=0
    for b,state in enumerate(path[:-1]):
        nxt=path[b+1];assert (state,nxt) in c['edges'] and state%3==b%3
        n=values[b%3];assert 0<=n<R//3
        aa=bb=0;remaining=n;place=1
        while remaining:
            remaining,trit=divmod(remaining,3)
            if trit:aa+=place
            if trit==2:bb+=place
            place*=3
        assert aa+bb==n
        if c['zeros'][state] and n:false.append(dict(block=b,state=state,value=n))
        D=1-c['zeros'][state];oldDs.append(D)
        T=jr-rep*D
        C=3**c['a'][state]
        support={e+c['a'][state] for e in c['positions']}
        removed={c['d']+c['a'][nxt]}
        if c['signs'][state]==1:removed.add(c['d']+c['bs'])
        if D:removed.add(c['d']+c['bz'])
        assert removed<=support
        Vsupport=support-removed
        if b==6:
            junk=c['d']+c['bz']+h
            assert junk in Vsupport and junk not in c['forbidden']
            Vsupport.remove(junk);D+=3**h
            T-=sum(3**j for j in range(h,m))
        if b==7:T-=sum(3**j for j in range(h-1))
        assert not Vsupport&c['forbidden'] and max(Vsupport)<m
        V=sum(3**j for j in Vsupport)
        oldV=c['K']*C-c['g']*3**c['a'][nxt]-c['hs']*int(c['signs'][state]==1)-c['hz']*oldDs[-1]
        assert V==oldV-(c['hz']*3**h if b==6 else 0)
        oldVs.append(oldV)
        if c['zeros'][state]:Tpositions=set(range(m))
        else:Tpositions={m-1}
        if b==6:Tpositions-=set(range(h,m))
        if b==7:Tpositions-=set(range(h-1))
        # Dense mask Booleanity is checked from this exact interval formula.
        assert T==sum(3**j for j in Tpositions)
        assert not digits(aa)&Tpositions and not digits(bb)&Tpositions
        assert digits(D)==({0} if oldDs[-1] else set())|({h} if b==6 else set())
        assert C<=c['S']<jr
        TC=C+jr-c['S'];TV=V+c['Zstar']
        assert TC>0 and TV>0 and TV<=jr
        # C is a singleton in S. TC is its Boolean support complement.
        assert c['a'][state] in c['a'] and not Vsupport&c['forbidden']
        for name,value in dict(A0=aa,A1=bb,T=T,Kp=int(c['signs'][state]==1),
                               Km=int(c['signs'][state]==-1),D=D,C=C,V=V,TC=TC,TV=TV).items():
            rows[name].append(value)
        native_checks+=11
        values[b%3]+=c['signs'][state];assert min(values)>=0
    assert values==[0,0,0] and false==[dict(block=6,state=6,value=2*x)]
    z={name:pack(v,R) for name,v in rows.items()}
    delta=3**h*R**6;Dold=pack(oldDs,R);Zold=H-Dold;Vold=pack(oldVs,R)
    Z=H-z['D'];Told=J-rep*Dold
    assert Z>0 and Z<Zold and z['D']==Dold+delta and z['V']==Vold-c['hz']*delta
    assert z['T']==Told-rep*delta and 0<z['T']<J
    # The first two ternary positions in row6 show that Z is not Boolean.
    assert Z//R**6%3==1 and Z//(R**6*3**h)%3==2
    I=3**c['a'][0];A=z['A0']+z['A1'];signed=z['Kp']-z['Km']
    equations=[q-2*J-1,q-W*(q//W),W-R**3,H*(R-1)-2*J,
        z['Kp']+z['Km']-H,6*(J-z['T'])-(R-3)*z['D'],Z+z['D']-H,
        W*(A+signed)-(A-2*x),2*x+(R-2*x)-R,
        z['C']+J-c['S']*H-z['TC'],z['TV']-z['V']-c['Zstar']*H,
        (R*c['K']-c['g'])*z['C']-2*c['g']*I*J-R*(z['V']+c['hs']*z['Kp']+c['hz']*z['D'])]
    assert all(v==0 for v in equations)
    assert min(z.values())>0 and Z>0
    common=[z['Kp'],z['A0']+z['T'],z['A0'],z['A1']+z['T'],z['A1'],z['Km']]
    program_fields=[z[n] for n in ('C','V','TC','TV')]
    mask_cases=[]
    for keep_D in (True,False):
        fields=common+([z['D']] if keep_D else [])+program_fields
        f=len(fields);L=q**f;raw=pack(fields,q);r=raw+(L-1)//2;beta=L-r
        assert all(0<v<q for v in fields) and raw%3==1
        assert 2*r+1==L+2*raw and r+beta==L
        assert r%2==0 and beta>0 and q**(f-1)<r<L<r*r
        # Row-wise Boolean proofs above make every field Boolean. Adding the
        # all-one word is carry-free, r has unit2, so every one of f*m*u
        # ternary positions carries when r is doubled (exact Kummer value).
        mask_cases.append(dict(retained_D_mask=keep_D,fields=f,scale_exponent=f,
            packed_bits=r.bit_length(),central_valuation=f*m*u,
            positive_scale=True,even_index=True,positive_slack=True))
    # Exact scaling transports all linear outer relations to doubled words.
    scaled_time=W*(2*A+2*signed)-(2*A-4*x)
    scaled_top=6*(2*J-2*z['T'])-(R-3)*2*z['D']
    scaled_route=(R*c['K']-c['g'])*(2*z['C'])-2*c['g']*I*(2*J) \
        -R*(2*z['V']+c['hs']*2*z['Kp']+c['hz']*2*z['D'])
    assert scaled_time==scaled_top==scaled_route==0 and 4*x<R
    return dict(status='PASS_FULL_OUTER_ZERO_MASK_OMISSION_COUNTEREXAMPLE',
        program_states=18,edges=len(c['edges']),sidon_coordinates=c['a']+[c['bs'],c['bz']],
        coordinate_gap=h,input=x,counter_width=m,serial_blocks=u,false_zero_tests=false,
        exact_common_outer_equations=len(equations),rowwise_retained_mask_checks=native_checks,
        Z_positive_but_nonboolean=True,D_boolean_but_off_head=True,
        packed_cases=mask_cases,doubled_outer_transport=True,
        scope='Exact full positive outer witnesses for the stated fixed cyclic graph, with only Z mask or both zero masks omitted. Every surviving field is Boolean; all guard, route, support, time and boundary equations hold. The generic even-index positive Pell converse applies to each listed scale, but enormous auxiliary coordinates are not instantiated. No optimized SLP or claim about the untouched complete systems is made.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:v for k,v in result.items() if k not in ('scope','sidon_coordinates')})
