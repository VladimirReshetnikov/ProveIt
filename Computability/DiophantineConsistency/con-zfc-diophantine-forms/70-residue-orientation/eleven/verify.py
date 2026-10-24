#!/usr/bin/env python3
"""Exact finite audit of the eleven-positive circuit, standard library only.

Checks literal regeneration, all register contracts, generic norm and radical
identities, the main-Pell cancellation, exact degrees and a selected nonzero
coefficient. This does not decide consistency or replace the existence proof.
"""
import gzip
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
import build
from exact_ring import Ring,Poly,require,equal,evaluate,cut_check

ROOT=Path(__file__).resolve().parent

def metadata(packet):
    available=set(packet['witnesses']+packet['fixed_numerals'])
    needed={packet['output']}
    for name,op,x,y in packet['source']:
        require(name not in available,'Duplicate register')
        require(op in ('+','-','*'),'Unknown operation')
        require(all(not isinstance(a,str) or a in available for a in (x,y)),'Forward reference')
        available.add(name)
    for name,op,x,y in reversed(packet['source']):
        if name in needed: needed.update((x,y))
    require(all(row[0] in needed for row in packet['source']),'Dead gate')
    require(set(packet['witnesses']+packet['fixed_numerals'])<=needed,'Dead input')
    require(len(packet['source'])==packet['operations']==113,'Operation count')
    require(dict(Counter(row[1] for row in packet['source']))==packet['operation_breakdown'],'Operation breakdown')
    core=set(packet['residuals'])
    for name,op,x,y in reversed(packet['source']):
        if name in core: core.update((x,y))
    require(sum(r[0] in core for r in packet['source'])==packet['system_operations']==110,'System count')
    cut_check(packet,['P11'],['N8','A1'],lambda e:{'P11':(1+e['N8'])*(1+e['A1'])-1},'unit product')

def prefix(packet):
    names=packet['witnesses']+packet['fixed_numerals']
    ring=Ring(names,[1]*11+[0]*4); v={n:ring.var(n) for n in names}
    j,F,alpha,i,T,X,Y,n,eta,zeta,gamma=(v[x] for x in packet['witnesses'])
    beta,K0,MC,MF=(v[x] for x in packet['fixed_numerals'])
    J=3*j+1; q=beta*J+1; C=q-F-alpha; E=X*Y; k=eta+zeta
    c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H; ell=E*k*Y
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    Rhat=q**3*(q+F+alpha); I=i*q*(q-1)*c*c
    M=q**3*(q-1); Bt=(q*K0+X)*C-q*F; Dtau=ell*(ell+k)+1
    expected={'J':J,'q':q,'C':C,'E':E,'k':k,'c':c,'a':a,'H':H,
      'Delta':Delta,'ell':ell,'R':R,'Rhat':Rhat,'I':I,'M':M,'Bt':Bt,'Dtau':Dtau}
    actual=evaluate(packet,list(expected),v)
    for name,value in expected.items(): equal(actual[name],value,'prefix '+name)
    q0=3*beta*j; k0=k; Bt0=(K0*q0+X)*(q0-F-alpha)-q0*F
    heads={'q':q0,'c':k0*Y,'Delta':X**2*Y**2,'R':q0**3*(q0-F),
      'Rhat':q0**3*(q0+F+alpha),'I':i*q0**2*k0**2*Y**2,
      'M':q0**4,'Bt':Bt0,'Dtau':X**2*k0**2*Y**4}
    for name,head in heads.items(): equal(expected[name].lead(),head,'prefix head '+name)
    require({x:expected[x].degree() for x in ('I','M','Dtau','Delta','R','Rhat','Bt')}
        =={'I':7,'M':4,'Dtau':8,'Delta':4,'R':4,'Rhat':4,'Bt':2},'Prefix degrees')
    return {n:len(p.d) for n,p in expected.items()}

def contracts(packet):
    cut_check(packet,['Df','Q','delta'],['Delta','I'],lambda e:{
      'Df':1+e['Delta']*e['I']**2,'Q':e['Delta']**2*e['I']**2,
      'delta':e['Delta']**2*e['I']**2-1},'strong')
    cut_check(packet,['V','Vbar','L'],['Df','c','T','R','Rhat'],lambda e:{
      'V':e['Df']*(e['c']*e['T']-e['R'])-e['c'],
      'Vbar':e['Df']*(e['c']*e['T']+e['Rhat']),
      'L':3*e['Df']*(e['c']*e['T']+e['Rhat'])},'auxiliary and guard')
    cut_check(packet,['W'],['qm','L'],lambda e:{'W':1+e['qm']*e['L']},'weight')
    cut_check(packet,['Zbar'],['M','ell','k','n','L','qm','Y','q3','W','Bt'],lambda e:{
      'Zbar':e['M']*(e['ell']+e['k']+e['n']+e['L'])+e['qm']*e['Y']-e['q3']*e['W']*e['Bt']},'transport')
    cut_check(packet,['A','Bf','Dnum','Cnum'],['M','Dtau','Df','Q','V'],lambda e:{
      'A':e['M']**2*e['Dtau'],'Bf':e['M']**2*e['Df'],
      'Dnum':e['Q']*e['V']**2-1,'Cnum':e['M']**2*(e['Q']*e['V']**2-1)},'scaled radicands')
    def norm(e):
        z,d,A,B,C=(e[x] for x in ['Zbar','delta','A','Bf','Cnum'])
        center=d*d*((z*z-A-B)**2-4*A*B)-2*d*C*(z*z+A+B)+C*C
        return {'Ncenter':center,'N8':center**2-64*d**3*A*B*C*z*z}
    cut_check(packet,['Ncenter','N8'],['Zbar','delta','A','Bf','Cnum'],norm,'cleared octic norm')

def universal_identities():
    ring=Ring(['x','p','q','r','d']); x,p,q,r,d=(ring.var(n) for n in ring.names)
    a,b,c=p*p,q*q,r*r
    product=ring.const(1)
    for s in (-1,1):
        for t in (-1,1):
            for u in (-1,1): product=product*(x-s*p-t*q-u*r)
    norm=((x*x-a-b-c)**2-4*(a*b+a*c+b*c))**2-64*a*b*c*x*x
    equal(product,norm,'eight conjugates')
    C=d*c
    center=d*d*((x*x-a-b)**2-4*a*b)-2*d*C*(x*x+a+b)+C*C
    equal(center**2-64*d**3*a*b*C*x*x,d**4*norm,'denominator clearing')
    t=p+q+r; u=p*q+p*r+q*r; v=p*q*r
    equal(t*t-a-b-c,2*u,'rational extraction u')
    equal(u*u-a*b-a*c-b*c,2*t*v,'rational extraction v')
    equal(a*t+v,p*(p+q)*(p+r),'rational extraction denominator')
    equal(a*(a+u),p*(a*t+v),'rational extraction root')
    return {'formal_conjugate_terms':len(product.d),'identities':6}

def main_cancellation(packet):
    names=['q','X','Y','eta','zeta','gamma','R']; ring=Ring(names,[1,1,1,1,1,1,4])
    e={x:ring.var(x) for x in names}; q,X,Y,eta,zeta,gamma,R=(e[x] for x in names)
    k=eta+zeta; c=k*Y+eta; a=X*Y+Y; H=4*a+3; Delta=a*a+H
    S=4*q*Y; U=q*S; shift=U*gamma+S*X-(k-R-1)
    expanded=U**2*(2*a*c*X+X*X-H*c*c-1)+2*U*(a*c+X)*H*shift+H**2*shift**2
    actual=evaluate(packet,['A1'],e)['A1']; equal(actual,expanded,'main cancellation')
    head=32*q*q*k*X*X*Y**4*(4*q*q*Y*gamma+R)
    require(actual.degree()==13,'Main residual degree13')
    equal(actual.lead(),head,'Main residual head13')
    return {'main_residual_terms':len(actual.d),'main_head_terms':len(head.d)}

def degree_certificate():
    # The preceding exact contracts certify every expression below. Unique
    # highest-degree summands justify propagation, except A1, checked above.
    d={'I':7,'Delta':4,'M':4,'Dtau':8,'Bt':2,'R':4,'Rhat':4,'cT':3}
    d['Df']=d['Delta']+2*d['I']; d['Q']=d['Delta']+d['Df']; d['delta']=d['Q']
    d['V']=d['Df']+d['R']; d['Vbar']=d['Df']+d['Rhat']; d['L']=d['Vbar']
    d['W']=1+d['L']; d['Zbar']=3+d['W']+d['Bt']
    require(d['Zbar']>d['M']+d['L'],'Unique transport leader')
    d['A']=2*d['M']+d['Dtau']; d['Bf']=2*d['M']+d['Df']
    d['Dnum']=d['Q']+2*d['V']; d['Cnum']=2*d['M']+d['Dnum']
    require(2*d['Zbar']>max(d['A'],d['Bf']),'Unique inner norm leader')
    d['Ncenter']=2*d['delta']+4*d['Zbar']
    alternatives=[d['delta']+d['Cnum']+2*d['Zbar'],2*d['Cnum']]
    require(d['Ncenter']>max(alternatives),'Unique norm center leader')
    tail=3*d['delta']+d['A']+d['Bf']+d['Cnum']+2*d['Zbar']
    d['N8']=2*d['Ncenter']; require(d['N8']>tail,'Unique octic leader')
    d['A1']=13; d['P11']=d['N8']+d['A1']
    require([d['Ncenter'],d['N8'],d['A1'],d['P11']]==[156,312,13,325],'Exact degree totals')
    # With q0=3 beta j and k0=eta+zeta, the certified head factors are
    # Q0=i²q0⁴k0⁴X⁴Y⁸ and z0=-3i²q0¹¹k0⁴X²Y⁶(q0+F+alpha)Bt0.
    # Multiply their monomial contents, and then the gamma summand of A1.
    qhead={'i':2,'q0':4,'k0':4,'X':4,'Y':8}
    zhead={'i':2,'q0':11,'k0':4,'X':2,'Y':6}
    mainhead={'q0':4,'k0':1,'X':2,'Y':5,'gamma':1}
    contents={}
    for scale,head in [(4,qhead),(8,zhead),(1,mainhead)]:
        for variable,exponent in head.items(): contents[variable]=contents.get(variable,0)+scale*exponent
    require(contents=={'i':24,'q0':108,'k0':49,'X':34,'Y':85,'gamma':1},'Head monomial contents')
    ring=Ring(['q0','F','alpha','X','K0']); q,F,alpha,X,K0=(ring.var(n) for n in ring.names)
    Bt=(K0*q+X)*(q-F-alpha)-q*F
    qindex=ring.names.index('q0')
    fiber=Poly(ring,{e:c for e,c in Bt.d.items() if e[qindex]==0})
    equal(fiber,-X*(F+alpha),'Minimum q-degree fiber')
    # The omitted common X^8 is accounted for separately; coefficient of
    # alpha^16 in (F+alpha)^16 is checked exactly in a two-variable ring.
    rr=Ring(['F','alpha']); F,alpha=(rr.var(n) for n in rr.names)
    require(((F+alpha)**16).d[(0,16)]==1,'Extreme fiber coefficient')
    powers={'j':108,'i':24,'eta':49,'X':42,'Y':85,'alpha':16,'gamma':1}
    require(sum(powers.values())==325,'Selected monomial total degree')
    return {'register_degrees':d,'lower_norm_center_terms_degrees':alternatives,
      'norm_tail_degree':tail,'witness_monomial':powers,
      'exact_coefficient':'2^7 * 3^8 * (3*beta)^108',
      'coefficient_integer_multiplier':128*3**116,'coefficient_beta_exponent':108}

def fixed_coefficients():
    binding=json.loads((ROOT/'coefficients/ACTIVE_BINDING.json').read_text()); checks={}; values={}
    for name,entry in binding['ports'].items():
        data=(ROOT/'coefficients'/entry['gzip_payload']).read_bytes(); raw=gzip.decompress(data)
        require(hashlib.sha256(data).hexdigest()==entry['gzip_sha256'],'Gzip digest '+name)
        require(hashlib.sha256(raw).hexdigest()==entry['sha256'],'Raw digest '+name)
        n=int.from_bytes(raw,'little'); values[name]=n
        require(len(raw)==entry['raw_bytes'] and n.bit_length()==entry['bits'],'Payload size '+name)
        checks[name]={'bits':n.bit_length(),'sha256':entry['sha256']}
    beta=values['beta']; require(beta==(1<<590069)-1,'Exact beta')
    require(0<values['MC']<beta and 0<values['MF']<2*beta,'Majorant mask hypotheses')
    require(beta%3==1 and values['K0']>0,'Other fixed hypotheses')
    require(hashlib.sha256((ROOT/'coefficients'/binding['whole_binding']).read_bytes()).hexdigest()
      ==binding['whole_binding_sha256'],'Whole binding digest')
    ledger=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for entry in ledger['retained_byte_identical_files']:
        content=(ROOT/entry['path']).read_bytes()
        require(hashlib.sha256(content).hexdigest()==entry['sha256'],'Retained source '+entry['path'])
        blob=hashlib.sha1(b'blob '+str(len(content)).encode()+b'\0'+content).hexdigest()
        require(blob==entry['git_blob_sha1'],'Git blob '+entry['path'])
    return checks

def main():
    packet=build.build(); path=ROOT/(packet['name']+'.json'); content=path.read_bytes()
    require(content==(json.dumps(packet,indent=2)+'\n').encode(),'Byte-identical regeneration')
    metadata(packet); sizes=prefix(packet); contracts(packet)
    receipt={'status':'passed','scope':'Finite exact algebra and fixed-data checks; not a consistency test or unbounded semantic proof.',
      'python_optimization':sys.flags.optimize,'operations':packet['operations'],
      'system_operations':packet['system_operations'],'operation_breakdown':packet['operation_breakdown'],
      'circuit_sha256':hashlib.sha256(content).hexdigest(),'prefix_monomial_counts':sizes,
      'universal_identities':universal_identities(),'main_cancellation':main_cancellation(packet),
      'degree_certificate':degree_certificate(),'coefficient_checks':fixed_coefficients()}
    name='OPTIMIZED_VERIFICATION.json' if sys.flags.optimize else 'VERIFICATION.json'
    (ROOT/name).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__': main()
