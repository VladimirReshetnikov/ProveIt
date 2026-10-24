#!/usr/bin/env python3
"""Exact component audits for the centered 11-positive degree-257 equation."""
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
import build_centered
import verify
from exact_ring import Ring, require, equal, evaluate, cut_check

ROOT=Path(__file__).resolve().parent

def metadata(p):
    known=set(p['witnesses']+p['fixed_numerals'])
    live={p['output']}
    for n,op,x,y in p['source']:
        require(n not in known,'Duplicate register')
        require(op in ('+','-','*'),'Unknown gate')
        require(all(not isinstance(v,str) or v in known for v in (x,y)),'Forward reference')
        known.add(n)
    for n,op,x,y in reversed(p['source']):
        if n in live: live.update((x,y))
    require(all(n in live for n,op,x,y in p['source']),'Dead gate')
    require(set(p['witnesses']+p['fixed_numerals'])<=live,'Dead input')
    require(len(p['source'])==p['operations']==114,'Operation total')
    require(dict(Counter(op for n,op,x,y in p['source']))==p['operation_breakdown'],'Gate breakdown')
    require(p['system_operations']==111,'System count')

def contracts(p):
    cut_check(p,['Df','Q','delta'],['Delta','I'],lambda e:{
      'Df':1+e['Delta']*e['I']**2,'Q':e['Delta']**2*e['I']**2,
      'delta':e['Delta']**2*e['I']**2-1},'strong')
    cut_check(p,['V','B0','L','hstar','W'],['Df','c','T','R','Rhat','q','qm'],lambda e:{
      'V':e['Df']*(e['c']*e['T']-e['R'])-e['c'],
      'B0':e['c']*e['T']+e['Rhat'],
      'L':e['Df']+e['c']*e['T']+e['Rhat'],
      'hstar':4*e['q']*e['Df']+e['Df']+e['c']*e['T']+e['Rhat'],
      'W':1+e['qm']*(4*e['q']*e['Df']+e['Df']+e['c']*e['T']+e['Rhat'])},'centered guard')
    cut_check(p,['Zbar'],['M','ell','k','n','L','V','qm','Y','q3','W','Bt'],lambda e:{
      'Zbar':e['M']*(e['ell']+e['k']+e['n']+e['L']+e['V'])+e['qm']*e['Y']-e['q3']*e['W']*e['Bt']},'centered transport')
    cut_check(p,['A','Bf','Dnum','Cnum'],['M','Dtau','Df','Q','V'],lambda e:{
      'A':e['M']**2*e['Dtau'],'Bf':e['M']**2*e['Df'],
      'Dnum':e['Q']*e['V']**2-1,'Cnum':e['M']**2*(e['Q']*e['V']**2-1)},'scaled radicands')
    def norm(e):
        x,d,A,B,C=(e[n] for n in ('Zbar','delta','A','Bf','Cnum'))
        center=d*d*((x*x-A-B)**2-4*A*B)-2*d*C*(x*x+A+B)+C*C
        return {'Ncenter':center,'N8':center**2-64*d**3*A*B*C*x*x}
    cut_check(p,['Ncenter','N8'],['Zbar','delta','A','Bf','Cnum'],norm,'octic norm')
    cut_check(p,['P11'],['N8','A1'],lambda e:{'P11':(1+e['N8'])*(1+e['A1'])-1},'unit product')

def centered_identity():
    r=Ring(['M','V','z','Q','A','Bf']); M,V,z,Q,A,B=(r.var(n) for n in r.names)
    d=Q-1; x=M*V+z; C=M*M*(Q*V*V-1)
    raw=d*(x*x-A-B)-C
    centered=d*(z*(z+2*M*V)-A-B)-M*M*(V*V-1)
    equal(raw,centered,'Exact centered Jn cancellation')
    return {'expanded_terms':len(raw.d),'identity':'Jn=delta[z(z+2MV)-A-Bf]-M^2(V^2-1)'}

def degree_certificate():
    d=dict(I=5,Delta=4,M=4,Dtau=8,Bt=2,R=4,Rhat=4,cT=3)
    d.update(Df=14,Q=18,delta=18,V=18,B0=4,L=14,hstar=15,W=16,z=21,Zbar=22,A=16,Bf=22,Cnum=62)
    # Degrees of the summands in the exact centered identity just checked.
    candidates=[d['delta']+2*d['z'],d['delta']+d['M']+d['V']+d['z'],
        d['delta']+d['A'],d['delta']+d['Bf'],2*d['M']+2*d['V']]
    require(candidates==[60,61,34,40,44],'Centered degree candidates')
    d['Jn']=61; d['Ncenter']=122
    correction=max(2*d['delta']+d['A']+d['Bf'],d['delta']+d['Cnum']+max(d['A'],d['Bf']))
    require(correction==102<122,'Norm center correction degree')
    tail=3*d['delta']+d['A']+d['Bf']+d['Cnum']+2*d['Zbar']
    require(tail==198,'Norm tail degree')
    d.update(N8=244,A1=13,P11=257)
    # Nonzero leading forms are products in an integral polynomial ring.
    # N8 head = 2^12 Q0^4 q0^36 Df0^8 R0^4 Bt0^4.
    # The gamma summand of A1 has head 2^7 q0^4 k0 X^2 Y^5 gamma.
    Qhead={'i':2,'k0':4,'X':4,'Y':8}
    Dhead={'i':2,'k0':4,'X':2,'Y':6}
    contents={'q0':52,'k0':1,'X':2,'Y':5,'gamma':1}
    for scale,head in [(4,Qhead),(8,Dhead)]:
        for n,k in head.items():contents[n]=contents.get(n,0)+scale*k
    require(contents=={'q0':52,'k0':49,'X':34,'Y':85,'gamma':1,'i':24},'Leading content')
    r=Ring(['F','alpha','X']); F,alpha,X=(r.var(n) for n in r.names)
    fiber=F**4*(-X*(F+alpha))**4
    require(fiber.d[(4,4,4)]==1,'Selected extreme coefficient')
    monomial={'j':52,'i':24,'eta':49,'X':38,'Y':85,'F':4,'alpha':4,'gamma':1}
    require(sum(monomial.values())==257,'Selected total degree')
    return {'register_degrees':d,'Jn_summand_degrees':candidates,'norm_center_correction_degree':correction,
       'norm_tail_degree':tail,'selected_monomial':monomial,'selected_coefficient':'2^19 * (3*beta)^52'}

def main():
    p=build_centered.build(); path=ROOT/(p['name']+'.json')
    require(path.read_bytes()==(json.dumps(p,indent=2)+'\n').encode(),'Literal rebuild')
    metadata(p); sizes=verify.prefix(p); contracts(p)
    result={'status':'passed','scope':'Exact finite algebra, degree and coefficient-data checks; unbounded existence proof is separate.',
      'python_optimization':sys.flags.optimize,'operations':114,'system_operations':111,
      'circuit_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
      'prefix_monomial_counts':sizes,'universal_identities':verify.universal_identities(),
      'main_cancellation':verify.main_cancellation(p),'centered_identity':centered_identity(),
      'degree_certificate':degree_certificate(),'coefficient_checks':verify.fixed_coefficients()}
    target='CHECK_CENTERED_OPTIMIZED.json' if sys.flags.optimize else 'CHECK_CENTERED.json'
    (ROOT/target).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
