#!/usr/bin/env python3
"""Independent formula, norm, degree, payload and provenance checks."""
import json,gzip,hashlib,random,sys
from pathlib import Path
from collections import Counter
from algebra import Poly,variables,evaluate,expand_cut
HERE=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok:raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()

def spec(e):
    J,F,alpha,i,T,w,Y,n,eta,zeta=[e[x] for x in ['J','F','alpha','i','T','w','Y','n','eta','zeta']]
    beta,K0,MC,MF=[e[x] for x in ['beta','K0','MC','MF']]
    q=beta*J+1; C=q-F-alpha;X=w*q;k=eta+zeta;c=k*Y+eta;mu=q*q+1
    A=mu*Y*(X+1)+1;Delta=A*A-1;H=4*A-5;V0=X*mu*mu*Y*Y
    D=1+V0*(V0+1)*k*k
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    ee=k-R-1;Bt=(K0+w)*C-F;I0=i*c*c
    Bf=1+Delta*D*I0*I0;Q=Delta*Delta*D*I0*I0;delta=Q-1
    b=c*(T+alpha)-R;V=Bf*b-c;Cy=Q*V*V-1
    P=A*I0*D;W=1+(q-1)*b;K=X*(3*c-2*X)+2
    P1=q**3*(q-1);M=P1*mu*mu*H
    Z=P1*mu*mu*(H*(n+V+P)+K)+H*(mu*mu*((q-1)*Y-q**3*W*Bt)-P1*ee)
    s=delta*Z*Z;u=delta*M*M*D*Bf;v=M*M*Cy
    N=(s-u-v)**2-4*u*v
    return dict(q=q,C=C,X=X,k=k,c=c,mu=mu,A=A,Am1=A-1,Dp=Delta,Hp=H,V0=V0,Dtau=D,
      R=R,e=ee,Bt=Bt,I=I0,Df=Bf,Q=Q,delta=delta,cTR=b,V=V,Dnum=Cy,
      Pcenter=P,W=W,Kpos=K,P1=P1,Mtot=M,Znum=Z,fs=s,fa=u,fc=v,N=N)

def main():
    p=json.loads((HERE/'equation.json').read_text());rows=p['source']
    initial=p['witnesses']+p['fixed_numerals'];known=set(initial);deps={};d={x:int(x in p['witnesses']) for x in initial}
    for name,op,a,b in rows:
        need(name not in known and op in ['+','-','*'],'fresh ring gate')
        need(all(type(x)is int or x in known for x in [a,b]),'topology')
        da,db=(0 if type(x)is int else d[x] for x in [a,b]);d[name]=da+db if op=='*' else max(da,db)
        known.add(name);deps[name]=[a,b]
    live=set();todo=['N']
    while todo:
        x=todo.pop()
        if type(x)is int or x in live:continue
        live.add(x);todo.extend(deps.get(x,[]))
    need(live==known,'all nodes, ten variables and four ports live')
    need(len(rows)==p['operations']==93 and dict(Counter(r[1] for r in rows))==p['operation_breakdown']=={'*':55,'+':22,'-':16},'operation count')
    need(d==p['register_degrees'] and d['N']==p['syntactic_degree']==316,'complete syntactic degrees')
    need(p['exact_degree']==278 and p['domain']=='strictly positive integers','degree and domain metadata')
    # Complete retained/change boundary against the frozen 99-gate parent.
    parent=json.loads((HERE/'upstream/parent_equation.json').read_text());old=parent['source'];child={r[0]:r[1:] for r in rows}
    changed={'DpI2':['*','Dp','I2D'],'qm1L':['*','bJ','cTR'],'Hn':['*','Hp','nVP']}
    removed={'I2','HI','L'}
    for n,op,a,b in old[:78]:
        if n in removed:need(n not in child,'deleted old definition '+n)
        else:need(child[n]==changed.get(n,[op,a,b]),'whole retained front '+n)
    need([r[0] for r in rows if r[0] not in {x[0] for x in old[:78]}]==[
      'ID','I2D','A','Pcenter','nVP','M2','dM2','Dprod','fa','fc','Z2','fs','sumac','diff','diff2','ac','ac4','N'],'complete new-node inventory')
    # All changed front cuts are checked as exact ring polynomials.
    x,y,z,h,m,n=variables(6)
    cuts=[
      ('ID',{'I':x,'Dtau':y},x*y),('I2D',{'I':x,'Dtau':y},x*x*y),
      ('Df',{'Dp':x,'Dtau':y,'I':z},1+x*y*z*z),
      ('Q',{'Dp':x,'Dtau':y,'I':z},x*x*y*z*z),
      ('Pcenter',{'Am1':x,'I':y,'Dtau':z},(x+1)*y*z),
      ('W',{'bJ':x,'cTR':y},1+x*y),
      ('Znum',{'P1mu2':x,'Hp':h,'n':n,'V':y,'Pcenter':z,'Kpos':m,'brk':0},x*(h*(n+y+z)+m)),
      ('Dprod',{'Dtau':x,'Df':y},x*y)]
    for name,leaves,expected in cuts:need(expand_cut(rows,name,leaves)==expected,'exact front cut '+name)
    # Entire four-conjugate tail, independent expanded product.
    x,r,y,_,_,_=variables(6)
    direct=(x-r-y)*(x-r+y)*(x+r-y)*(x+r+y)
    tail=expand_cut(rows,'N',{'fs':x*x,'fa':r*r,'fc':y*y})
    need(tail==direct,'full two-root norm')
    # Universal double-center identity; a=P²-d, Q=delta+1.
    Q,M,P,V,z,defect=variables(6);delta=Q-1;Dprod=P*P-defect;Z=M*(V+P)+z;Cy=Q*V*V-1
    lhs=expand_cut(rows,'N',{'delta':delta,'Mtot':M,'Dprod':Dprod,'Dnum':Cy,'Znum':Z})
    B=2*M*(P+V)*z+z*z+M*M*defect;CC=delta*B-M*M*(V*V-1)
    terms=[CC*CC,4*delta*M*M*P*V*CC,-4*delta*M**4*P*P*(V*V-1),4*delta*M**4*defect*(Q*V*V-1)]
    need(lhs==sum(terms),'entire double-center identity')
    weights=[48,13,28,42,19,46];maxima=[t.weighted_degree(weights) for t in terms]
    need(maxima==[244,266,240,278],'every centered summand upper degree')
    top={m:c for m,c in lhs.t.items() if sum(a*b for a,b in zip(m,weights))==278}
    need(top=={(2,4,0,2,0,1):4},'unique degree278 leading product')
    # Full scalar P²-Dprod and actual small center z cuts.
    A,I,D,V,M,z=variables(6);Df=1+(A*A-1)*D*I*I
    need((A*I*D)**2-D*Df==(I*D)**2-D,'exact root-center defect')
    x,h,n,V,P,K=variables(6)
    need(expand_cut(rows,'Znum',{'P1mu2':x,'Hp':h,'n':n,'V':V,'Pcenter':P,'Kpos':K,'brk':0})-x*h*(V+P)==x*(h*n+K),'first center cancellation')
    zdegree=max(d['P1mu2']+max(d['Hp']+1,d['Kpos']),d['Zpart2'])
    need(zdegree==19 and d['Pcenter']==28 and d['Q']==48 and d['V']==42 and d['Mtot']==13,'actual centered front degrees')
    # Complete homogeneous leading component, including eta+zeta and F.
    q,i,w,Y,eta,zeta,F=variables(7);k=eta+zeta
    A0=q**3*w*Y;I0=i*k*k*Y*Y;D0=q**10*w*w*Y**4*k*k
    Q0=A0**4*D0*I0*I0;Df0=A0*A0*D0*I0*I0;V0=-Df0*q**3*(q-F)
    M0=4*q**11*w*Y;defect0=I0*I0*D0*D0
    lead=4*Q0*Q0*M0**4*defect0*V0*V0
    want=2**10*q**146*i**10*w**28*Y**60*k**32*(q-F)**2
    need(lead==want and lead.degree()==278,'whole nonzero homogeneous leading form')
    need(lead.t[(146,10,28,60,32,0,2)]==2**10,'explicit nonzero coefficient before q=beta J')
    # Whole numerical coefficients and every pinned source byte.
    ports={};binding=json.loads((HERE/'coefficients/BINDING.json').read_text())
    need(binding==p['coefficient_binding'],'whole coherent BFS binding')
    for name,pin in binding['ports'].items():
        blob=(HERE/'coefficients'/pin['file']).read_bytes();raw=gzip.decompress(blob)
        need(digest(blob)==pin['gzip_sha256'] and digest(raw)==pin['raw_sha256'],'complete coefficient bytes '+name)
        ports[name]=int.from_bytes(raw,'little');need(ports[name].bit_length()==pin['bits'],'bit width '+name)
    need(ports['beta']==2**590069-1 and 0<ports['MC']<ports['beta']<ports['MF']<2*ports['beta'] and ports['K0']>0,'exact port box')
    pins=json.loads((HERE/'upstream/SOURCE_PINS.json').read_text())
    for name,pin in pins['files'].items():need(digest((HERE/'upstream'/name).read_bytes())==pin['sha256'],'source provenance '+name)
    need(digest((HERE/'upstream/parent_equation.json').read_bytes())==p['parent_sha256'],'whole parent binding')
    # Independent full-formula signed evaluations supplement the symbolic cuts.
    rng=random.Random(27893);samples=0
    for prime in [1009,2**127-1]:
        for _ in range(60):
            ins={x:rng.randrange(-8,9) for x in p['witnesses']}|{x:v%prime for x,v in ports.items()}
            actual=evaluate(rows,ins,prime);expected=spec(ins)
            need(all(actual[x]==v%prime for x,v in expected.items()),'full independent modular scalar evaluation');samples+=1
    for _ in range(30):
        ins={x:rng.randrange(-2,3) for x in initial};actual=evaluate(rows,ins);expected=spec(ins)
        need(all(actual[x]==v for x,v in expected.items()),'full independent exact scalar evaluation');samples+=1
    receipt={'status':'PASS','python_optimization':sys.flags.optimize,'positive_variables':10,'operations':93,
      'breakdown':p['operation_breakdown'],'exact_degree':278,'syntactic_degree':316,
      'norm_terms':len(tail.t),'centered_identity_terms':len(lhs.t),'centered_summand_degrees':maxima,
      'leading_component_terms':len(lead.t),'selected_coefficient':'2^10 beta^146',
      'full_independent_evaluation_controls':samples,'source_files':len(pins['files']),
      'scope':'Exact finite polynomial/coefficient checks; ordinary unbounded proof is PROOF.md.'}
    (HERE/('CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
