#!/usr/bin/env python3
"""Independent ordinary-chart formula/graph/degree controls, stdlib only."""
import contextlib,io,json,random
from collections import Counter
with contextlib.redirect_stdout(io.StringIO()):import check as C
H=C.H;rng=random.Random(1511);out={}
for kind,count,degree in [('uncentered',89,288),('upper',91,283),('sharp',92,278)]:
    a=json.loads((H/('ordinary_'+kind+'.json')).read_text());d=json.loads((H/(kind+'.json')).read_text())
    C.need(a['coefficient_binding']==d['coefficient_binding'],'whole same original tuple')
    old={r[0]:r for r in d['source']};new={r[0]:r for r in a['source']}
    drop={'qK0','qK0X','qK0XC','qF','B','qbJ','lowX','inner0'}
    C.need(set(new)==(set(old)-drop)|{'K0w','K0wC','Bt'},'full ordinary row inventory')
    expected={'X':['X','*','q','w'],'P1':['P1','*','q3','bJ'],'lowY':['lowY','*','bJ','Y'],'inner':['inner','-','lowY','q3WBt'],'LB':['LB','*','cTR','Bt'],'q3WBt':['q3WBt','*','q3','Bt']}
    for n in set(new)&set(old):C.need(new[n]==expected.get(n,old[n]),'retained ordinary row '+n)
    for r in [['K0w','+','K0','w'],['K0wC','*','K0w','C'],['Bt','-','K0wC','F']]:C.need(new[r[0]]==r,'inserted ordinary row')
    deg={n:1 for n in a['witnesses']}|{n:0 for n in a['fixed_numerals']};live={'N'}
    for n,op,x,y in a['source']:
        C.need(n not in deg,'unique DAG node');dx=deg[x] if isinstance(x,str) else 0;dy=deg[y] if isinstance(y,str) else 0;deg[n]=dx+dy if op=='*' else max(dx,dy)
    for n,op,x,y in reversed(a['source']):
        if n in live:live.update(z for z in [x,y] if isinstance(z,str))
    C.need(set(deg)==live and deg==a['register_degrees'],'live degree schedule');C.need(len(new)==count and dict(Counter(r[1] for r in a['source']))==a['operation_breakdown'],'operation count')
    def leading(w,p):
        coeff,pq,pw,py={'uncentered':(-2**10,152,30,62),'upper':(2**11,149,29,61),'sharp':(2**10,146,28,60)}[kind]
        q=p['beta']*w['J'];k=w['eta']+w['zeta'];return coeff*q**pq*w['w']**pw*w['Y']**py*w['i']**10*k**32*(q-w['F'])**2
    toy={'beta':2,'K0':3,'MC':5,'MF':7};w={n:1 for n in a['witnesses']};r=C.ray(a,toy,w)
    C.need(len(r)-1==degree and r[-1]==leading(w,toy),'exact integer ordinary degree ray')
    modular=[]
    for p in [1000000007,1000000009,998244353]:
        pp={n:v%p for n,v in C.ports.items()};w={n:rng.randint(1,9) for n in a['witnesses']};r=C.ray(a,pp,w,p);top=leading(w,pp)%p
        C.need(top!=0 and len(r)-1==degree and r[-1]==top,'actual-port ordinary leading form');modular.append({'prime':p,'degree':degree,'leading_coefficient':top})
    for j in range(24):
        e={n:rng.randint(1,4) for n in a['witnesses']}|{'beta':31,'K0':7,'MC':5,'MF':37};v=C.evaluate(a['source'],e)
        q=e['beta']*e['J']+1;X=q*e['w'];mu=q*q+1;A=mu*e['Y']*(X+1)+1;Delta=A*A-1;k=e['eta']+e['zeta'];c=k*e['Y']+e['eta'];E=e['i']*c*c;vf=X*mu*mu*e['Y']**2;D=vf*(vf+1)*k*k+1
        R=((q-1)*(q-e['F'])+e['alpha'])*(q*q-1)+(e['MC']+q*e['MF'])*e['J'];b=c*(e['T']+e['alpha'])-R;Fs=1+Delta*D*E*E;Q=Delta*Delta*D*E*E;delta=Q-1;V=Fs*b-c;B=(e['K0']+e['w'])*(q-e['F']-e['alpha'])-e['F'];h=4*A-5;P=q**3*(q-1);M=P*mu*mu*h;K=X*(3*c-2*X)+2;S=0 if kind=='uncentered' else (A+(kind=='upper'))*D*E
        Z=P*mu*mu*(h*(e['n']+V+S-b*B)+K)+h*(mu*mu*((q-1)*e['Y']-q**3*B)-P*(k-R-1));u=delta*M*M*D*Fs;vv=M*M*(Q*V*V-1);s=delta*Z*Z
        C.need(v['Znum']==Z and v['N']==(s-vv-u)**2-4*u*vv,'ordinary independent formula')
    out[kind]={'operations':count,'exact_degree':degree,'formula_controls':24,'integer_ray_pass':True,'actual_ports':modular}
print(json.dumps({'status':'PASS','ordinary_chart':out},indent=2))
