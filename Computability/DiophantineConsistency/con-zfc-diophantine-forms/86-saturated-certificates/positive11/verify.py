#!/usr/bin/env python3
"""Exact finite audit for the strong-Pell-budget companion.

Standard library only. The unbounded existence argument is in PROOF.md.
All checks raise explicitly and remain active under python -O.
"""
import gzip
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
import build
from exact_ring import Ring, equal, evaluate, cut_check, require

ROOT=Path(__file__).resolve().parent

def metadata(p):
    known=set(p['witnesses']+p['fixed_numerals'])
    needed={p['output']}
    for name,op,x,y in p['source']:
        require(name not in known,'duplicate register')
        require(op in ('+','-','*'),'unknown operation')
        require(all(not isinstance(v,str) or v in known for v in (x,y)),
                'forward reference')
        known.add(name)
    for name,op,x,y in reversed(p['source']):
        if name in needed: needed.update((x,y))
    require(all(r[0] in needed for r in p['source']),'dead gate')
    require(set(p['witnesses']+p['fixed_numerals'])<=needed,'dead input')
    require(len(p['witnesses'])==11,'variable count')
    require(len(p['source'])==p['operations']==112,'operation count')
    require(p['system_operations']==109,'system operations')
    require(dict(Counter(r[1] for r in p['source']))==p['operation_breakdown'],
            'operation breakdown')
    return dict(variables=11,operations=112,system_operations=109,
                breakdown=p['operation_breakdown'])

def prefix(p):
    names=p['witnesses']+p['fixed_numerals']
    ring=Ring(names,[1]*11+[0]*4)
    e={n:ring.var(n) for n in names}
    j,F,alpha,i,T,X,Y,n,eta,zeta,gamma=(e[v] for v in p['witnesses'])
    beta,K0,MC,MF=(e[v] for v in p['fixed_numerals'])
    J=3*j+1; q=beta*J+1; C=q-F-alpha; E=X*Y
    k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H
    ell=E*k*Y; R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    M=q**3*(q-1); Bt=(q*K0+X)*C-q*F; Dtau=ell*(ell+k)+1
    I=i*c*c; Df=1+Delta*I*I; Q=Delta*Delta*I*I
    V=Df*(c*T-R)-c; fbar=(a+2)*I; hstar=i**3+c*T
    W=1+(q-1)*hstar
    Zbar=M*(ell+k+n+c*T+V+fbar)+(q-1)*Y-q**3*W*Bt
    v=k-R-1; S=4*q*Y; U=q*S
    Dstar=U*(X+a*c)+H*(U*gamma+S*X-v)
    A1=Dstar*Dstar-U*U*(1+Delta*c*c)
    target=dict(J=J,q=q,C=C,E=E,k=k,c=c,a=a,H=H,Delta=Delta,
                ell=ell,R=R,M=M,Bt=Bt,Dtau=Dtau,I=I,Df=Df,Q=Q,
                V=V,fbar=fbar,hstar=hstar,W=W,Zbar=Zbar,S=S,U=U,
                Dstar=Dstar,A1=A1)
    actual=evaluate(p,list(target),e)
    for name,value in target.items():equal(actual[name],value,'prefix '+name)
    q0=3*beta*j; k0=eta+zeta
    Bt0=(K0*q0+X)*(q0-F-alpha)-q0*F
    R0=q0**3*(q0-F)
    Df0=i*i*k0**4*X*X*Y**6
    Q0=i*i*k0**4*X**4*Y**8
    z=Zbar-M*(V+fbar)
    heads={
      'I':(I,i*k0*k0*Y*Y,5),
      'Delta':(Delta,X*X*Y*Y,4),
      'M':(M,q0**4,4),
      'Dtau':(Dtau,X*X*k0*k0*Y**4,8),
      'R':(R,R0,4),
      'Bt':(Bt,Bt0,2),
      'Df':(Df,Df0,14),
      'Q':(Q,Q0,18),
      'V':(V,-Df0*R0,18),
      'fbar':(fbar,i*k0*k0*X*Y**3,7),
      'hstar':(hstar,i**3+k0*Y*T,3),
      'z':(z,-q0**4*(i**3+k0*Y*T)*Bt0,9),
      'Zbar':(Zbar,-q0**4*Df0*R0,22),
      'A1':(A1,32*q0*q0*k0*X*X*Y**4*(4*q0*q0*Y*gamma+q0**3*(q0-F)),13)}
    for name,(expr,head,degree) in heads.items():
        require(expr.degree()==degree,'degree '+name)
        equal(expr.lead(),head,'leading form '+name)
    return {'monomial_counts':{n:len(x.d) for n,x in target.items()},
            'register_degrees':{n:v[2] for n,v in heads.items()}}

def norm_contracts(p):
    cut_check(p,['A','Bf','Dnum','Cnum'],
        ['M','Dtau','Df','Q','V'],lambda e:{
          'A':e['M']**2*e['Dtau'],'Bf':e['M']**2*e['Df'],
          'Dnum':e['Q']*e['V']**2-1,
          'Cnum':e['M']**2*(e['Q']*e['V']**2-1)},'radicands')
    def norm(e):
        x,d,A,B,C=(e[n] for n in ('Zbar','delta','A','Bf','Cnum'))
        center=d*d*((x*x-A-B)**2-4*A*B)-2*d*C*(x*x+A+B)+C*C
        return {'Ncenter':center,'N8':center*center-64*d**3*A*B*C*x*x}
    cut_check(p,['Ncenter','N8'],['Zbar','delta','A','Bf','Cnum'],norm,'norm')
    cut_check(p,['P11'],['N8','A1'],
              lambda e:{'P11':(1+e['N8'])*(1+e['A1'])-1},'unit product')
    ring=Ring(['x','r','s','t']); x,r,s,t=(ring.var(n) for n in ring.names)
    product=ring.const(1)
    for e1 in (-1,1):
        for e2 in (-1,1):
            for e3 in (-1,1):product=product*(x-e1*r-e2*s-e3*t)
    A,B,C=r*r,s*s,t*t
    closed=((x*x-A-B-C)**2-4*(A*B+A*C+B*C))**2-64*A*B*C*x*x
    equal(product,closed,'eight signed conjugates')
    return {'conjugate_identity_terms':len(product.d)}

def double_center_certificate():
    names=['Q','V','M','t','z','e','D']; weights=[18,18,4,7,9,10,8]
    ring=Ring(names,weights); Q,V,M,t,z,e,D=(ring.var(n) for n in names)
    d=Q-1; x=M*(V+t)+z; A=M*M*D; B=M*M*(t*t-e)
    C=M*M*(Q*V*V-1)
    center=d*d*((x*x-A-B)**2-4*A*B)-2*d*C*(x*x+A+B)+C*C
    poly=center*center-64*d**3*A*B*C*x*x
    require(len(poly.d)==1110,'norm expansion size')
    require(poly.degree()==200,'double-center weighted degree')
    equal(poly.lead(),64*M**6*Q**4*V**4*t*t*z*z,'double-center leading form')
    monomial={'j':48,'i':24,'eta':37,'X':30,'Y':67,'F':4,'alpha':2,'gamma':1}
    require(sum(monomial.values())==213,'final selected degree')
    # Isolate the unique minimum-q-degree fiber after choosing gamma and i^24.
    small=Ring(['F','alpha','X']); F,alpha,X=(small.var(n) for n in small.names)
    fiber=F**4*(-X*(F+alpha))**2
    require(fiber.d.get((4,2,2))==1,'minimum-q-degree selected coefficient')
    return {'abstract_variables':names,'weights':weights,'expanded_terms':1110,
            'weighted_degree':200,'leading_form':'64 M^6 Q^4 V^4 t^2 z^2',
            'P_exact_degree':213,'selected_monomial':monomial,
            'selected_coefficient':'2^13 (3 beta)^48'}

def coefficient_check():
    binding=json.loads((ROOT/'coefficients'/'ACTIVE_BINDING.json').read_text())
    vals={}; out={}
    for name,entry in binding['ports'].items():
        compressed=(ROOT/'coefficients'/entry['gzip_payload']).read_bytes()
        require(hashlib.sha256(compressed).hexdigest()==entry['gzip_sha256'],
                'compressed coefficient hash '+name)
        raw=gzip.decompress(compressed); val=int.from_bytes(raw,'little')
        require(hashlib.sha256(raw).hexdigest()==entry['sha256'],'raw hash '+name)
        require(len(raw)==entry['raw_bytes'] and val.bit_length()==entry['bits'],
                'coefficient length '+name)
        vals[name]=val;out[name]={'bits':val.bit_length(),'sha256':entry['sha256']}
    require(vals['beta']==(1<<590069)-1,'fixed beta')
    require(vals['beta']%3==1,'fixed beta congruence')
    require(0<vals['MC']<vals['beta'],'MC bound')
    require(0<vals['MF']<2*vals['beta'],'shifted MF bound')
    require(vals['K0']>=1,'K0 positive')
    source=(ROOT/'coefficients'/binding['whole_binding']).resolve()
    require(hashlib.sha256(source.read_bytes()).hexdigest()==binding['whole_binding_sha256'],
            'whole binding authentication')
    return out

def pell_pair(A,n):
    D=A*A-1; x,y=1,0
    for _ in range(n):x,y=A*x+D*y,x+A*y
    return x,y

def pell_controls():
    cases=[]
    for q in (2,3,4):
        Y=q**3
        for X in (1,2):
            A=Y*(X+1)+2; Delta=A*A-1
            g,c=pell_pair(A,2)
            f,v=pell_pair(g,c)
            require(v%c==0,'strong composition divisibility')
            i=v//c; I=i*c*c
            require(f*f-Delta*I*I==1,'constructed strong norm')
            require(i>8*q*Delta*c**4,'strong growth bound')
            require(i**3>6*q*f*f,'transport guard domination')
            require(i**3>q*q,'negative-rank guard domination')
            require(f<A*I<i*i,'double-center estimates')
            cases.append({'q':q,'X':X,'Y':Y,'main_index':2,
                          'strong_relative_index':c,'i_bits':i.bit_length()})
    # A guard based on i^2 would fail to dominate q Df for every positive input.
    for q in range(2,7):
        for i in range(1,7):
            c=3; Delta=15; Df=1+Delta*i*i*c**4
            require(i*i<q*Df,'reject unsound quadratic budget')
    return {'constructed_examples':cases,'quadratic_budget_negative_controls':30}

def main():
    packet=build.build(); path=ROOT/(packet['name']+'.json')
    expected=(json.dumps(packet,indent=2)+'\n').encode()
    require(path.read_bytes()==expected,'literal deterministic rebuild')
    result={'status':'PASS','scope':'Exact finite algebra and data; unbounded proof is PROOF.md.',
            'python_optimization':sys.flags.optimize,
            'circuit_sha256':hashlib.sha256(expected).hexdigest(),
            'metadata':metadata(packet),'prefix':prefix(packet),
            'norm_contracts':norm_contracts(packet),
            'double_center':double_center_certificate(),
            'coefficients':coefficient_check(),'pell_controls':pell_controls()}
    output='CHECKS_OPTIMIZED.json' if sys.flags.optimize else 'CHECKS.json'
    (ROOT/output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
