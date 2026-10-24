#!/usr/bin/env python3
"""Exact finite algebra and fixed-numeral checks, Python standard library only.

This does not test or prove consistency.  The existence reductions are in
section.tex.  Sparse-ring implementation follows the elementary approach of
ProveIt package 61 check13.py; no proof is inferred from modular sampling.
"""
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path
import build

ROOT=Path(__file__).resolve().parent

def require(condition,message):
    if not condition: raise ValueError(message)

class Ring:
    def __init__(self,names,witness_count=None):
        self.names=list(names); self.n=len(names)
        self.nw=len(names) if witness_count is None else witness_count
        self.zero=(0,)*self.n
    def const(self,k): return Poly(self,{self.zero:k} if k else {})
    def var(self,name):
        e=[0]*self.n; e[self.names.index(name)]=1
        return Poly(self,{tuple(e):1})

class Poly:
    def __init__(self,ring,data): self.ring=ring; self.d=data
    def coerce(self,other):
        if isinstance(other,Poly):
            require(self.ring is other.ring,'Different rings')
            return other
        return self.ring.const(other)
    def __add__(self,other):
        other=self.coerce(other); data=dict(self.d)
        for e,c in other.d.items():
            data[e]=data.get(e,0)+c
            if data[e]==0: del data[e]
        return Poly(self.ring,data)
    __radd__=__add__
    def __neg__(self): return Poly(self.ring,{e:-c for e,c in self.d.items()})
    def __sub__(self,other): return self+-self.coerce(other)
    def __rsub__(self,other): return self.coerce(other)+-self
    def __mul__(self,other):
        other=self.coerce(other); data={}
        for e,c in self.d.items():
            for f,d in other.d.items():
                g=tuple(x+y for x,y in zip(e,f))
                data[g]=data.get(g,0)+c*d
        return Poly(self.ring,{e:c for e,c in data.items() if c})
    __rmul__=__mul__
    def __pow__(self,n):
        require(isinstance(n,int) and n>=0,'Bad exponent')
        a=self; out=self.ring.const(1)
        while n:
            if n%2: out=out*a
            n//=2
            if n: a=a*a
        return out
    def degree(self):
        return max((sum(e[:self.ring.nw]) for e in self.d),default=-1)
    def lead(self):
        deg=self.degree()
        return Poly(self.ring,{e:c for e,c in self.d.items() if sum(e[:self.ring.nw])==deg})

def equal(p,q,label): require(not (p-q).d,'Polynomial mismatch: '+label)

def evaluate(packet,roots,env):
    need=set(roots)
    for name,op,x,y in reversed(packet['source']):
        if name in need and name not in env: need.update((x,y))
    out=dict(env)
    ring=next(iter(env.values())).ring
    for name,op,x,y in packet['source']:
        if name not in need or name in out: continue
        require(op in ('+','-','*'),'Unknown gate')
        xx=out[x] if isinstance(x,str) else ring.const(x)
        yy=out[y] if isinstance(y,str) else ring.const(y)
        out[name]=xx+yy if op=='+' else xx-yy if op=='-' else xx*yy
    return out

def cut_check(packet,roots,cut_names,formula,label):
    ring=Ring(cut_names)
    env={name:ring.var(name) for name in cut_names}
    actual=evaluate(packet,roots,env)
    target=formula(env)
    for name in roots: equal(actual[name],target[name],label+':'+name)

def metadata(packet):
    needed={packet['output']}; available=set(packet['witnesses']+packet['fixed_numerals'])
    for name,op,x,y in packet['source']:
        require(name not in available,'Duplicate register')
        require(all(not isinstance(a,str) or a in available for a in (x,y)),'Forward reference')
        available.add(name)
    for name,op,x,y in reversed(packet['source']):
        if name in needed: needed.update((x,y))
    require(all(row[0] in needed for row in packet['source']),'Dead gate')
    require(set(packet['witnesses']+packet['fixed_numerals'])<=needed,'Dead input')
    require(len(packet['source'])==packet['operations'],'Operation count')
    require(dict(Counter(row[1] for row in packet['source']))==packet['operation_breakdown'],'Operation breakdown')
    core=set(packet['residuals'])
    for name,op,x,y in reversed(packet['source']):
        if name in core: core.update((x,y))
    require(sum(row[0] in core for row in packet['source'])==packet['system_operations'],'System cost')
    cut_check(packet,[packet['output']],packet['residuals'],
      lambda e:{packet['output']:sum((e[r]**2 for r in packet['residuals']),0)},'SOS finalizer')

def exact_prefix(packet,kind):
    ring=Ring(packet['witnesses']+packet['fixed_numerals'],len(packet['witnesses']))
    v={name:ring.var(name) for name in ring.names}
    j,F,alpha,i,T,X,Y,eta,zeta,u,gamma=(v[n] for n in ['j','F','alpha','i','T','X','Y','eta','zeta','u','gamma'])
    beta,K0,MC,MF=(v[n] for n in packet['fixed_numerals'])
    J=3*j+1; q=beta*J+1; C=q-F-alpha
    E=X*Y; k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H
    ell=E*k*Y; I=i*c*c; R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    Bt=(q*K0+X)*C-q*F; hstar=k if kind==13 else i*k*c
    W=1+(q-1)*hstar; M=q**3*(q-1)
    rr=v['r'] if kind==13 else v['n']
    Z0=M*(ell+k+rr)+(q-1)*Y-q**3*W*Bt
    rad0=ell*(ell+k)+1
    S=4*q*Y; U=q*S; shift=U*gamma+S*X-(k-R-1)
    # Expanded main-carrier cancellation, independently specified.
    A1=U**2*(2*a*c*X+X*X-H*c*c-1)+2*U*(a*c+X)*H*shift+H**2*shift**2
    if kind==13:
        f=v['f']; fsquare=f*f; fminus=fsquare-1
    else:
        fminus=Delta*I*I; fsquare=fminus+1
    V=fsquare*(c*T-R)-c; Q=Delta*fminus
    expected={'J':J,'q':q,'C':C,'c':c,'a':a,'H':H,'Delta':Delta,
      'I':I,'M':M,'W':W,'Bt':Bt,'R':R,'Z0':Z0,'rad0':rad0,
      'A1':A1,'V':V,'Kaux':Q}
    if kind==13:
        expected['A0']=Z0**2-M**2*rad0
        expected['As']=fsquare-Delta*I*I-1
    else:
        L=(a+2)*I
        expected.update({'Df':fsquare,'L':L,'Zbar':Z0+M*L})
    actual=evaluate(packet,list(expected),v)
    for name,p in expected.items(): equal(actual[name],p,'exact prefix '+name)
    cut_check(packet,['Aa'],['V','u','Kaux'],lambda e:{'Aa':
      (e['V']+e['u'])**2-e['Kaux']*e['u']*(2*e['V']+e['u'])-1},'auxiliary cancellation')
    q0=3*beta*j; k0=k
    Bt0=(K0*q0+X)*(q0-F-alpha)-q0*F
    R0=q0**3*(q0-F)
    a1leader=32*q0**2*k0*X**2*Y**4*(4*q0**2*Y*gamma+R0)
    equal(A1.lead(),a1leader,'main carrier leading13')
    require(A1.degree()==13,'Main carrier degree')
    if kind==13:
        equal(expected['A0'].lead(),-2*q0**8*k0**2*X*Y**2*Bt0,'A0 leading15')
        equal(expected['As'].lead(),-i**2*k0**4*X**2*Y**6,'As leading14')
        require(expected['A0'].degree()==15 and expected['As'].degree()==14,'Other residual degrees')
        require(V.degree()==6 and Q.degree()==6,'Auxiliary input degrees')
        auxlead=-2*Q.lead()*V.lead()*u
        equal(auxlead,2*X**2*Y**2*v['f']**4*R0*u,'Aa leading13')
        outlead=4*q0**16*k0**4*X**2*Y**4*Bt0**2
        powers={'j':16,'eta':4,'X':4,'Y':4,'alpha':2}
        coeff=4*3**16; beta_power=16
    else:
        cut_check(packet,['N'],['Zbar','M','Df','rad0'],lambda e:{'N':
          (e['Zbar']**2+e['M']**2*(e['Df']-e['rad0']))**2
          -4*e['M']**2*e['Zbar']**2*e['Df']},'norm identity')
        L=expected['L']
        equal(L*L-fsquare,I*I-1,'upper approximation gap')
        require([M.degree(),L.degree(),fsquare.degree(),rad0.degree(),Z0.degree()]==[4,7,14,8,10],'Norm prefix degrees')
        equal(Z0.lead(),-q0**4*i*k0**2*Y*Bt0,'Z0 leading10')
        # The center identity is verified separately in an independent cut ring.
        rr=Ring(['z','m','l','ii','aa']); z,m,l,ii,aa=(rr.var(n) for n in rr.names)
        b=l*l-ii*ii+1
        equal((z+m*l)**2-m*m*(b+aa),z*z+2*m*l*z-m*m*(1-ii*ii+aa),'center cancellation')
        # Degrees 20,21,18: a unique degree-21 center summand; norm tail38.
        require([2*Z0.degree(),M.degree()+L.degree()+Z0.degree(),2*M.degree()+max(2*I.degree(),rad0.degree())]==[20,21,18],'Center degree separation')
        require(4*M.degree()+fsquare.degree()+rad0.degree()==38,'Norm tail degree')
        normlead=(2*M.lead()*L.lead()*Z0.lead())**2
        equal(normlead,4*q0**16*i**4*k0**8*X**2*Y**8*Bt0**2,'N leading42')
        require(V.degree()==18 and Q.degree()==18,'Auxiliary degrees12')
        auxlead=-2*Q.lead()*V.lead()*u
        require(auxlead.degree()==37 and bool(auxlead.d),'Auxiliary exact degree37')
        outlead=normlead**2
        powers={'j':32,'i':8,'eta':16,'X':8,'Y':16,'alpha':4}
        coeff=16*3**32; beta_power=32
    # Isolate the stated witness coefficient as a polynomial in fixed ports.
    target=tuple(powers.get(name,0) for name in packet['witnesses'])
    coefficients={e[ring.nw:]:c for e,c in outlead.d.items() if e[:ring.nw]==target}
    port_target=tuple(beta_power if name=='beta' else 0 for name in packet['fixed_numerals'])
    require(coefficients=={port_target:coeff},'Actual-slice nonzero coefficient')
    require(outlead.degree()==packet['exact_degree'],'Exact final degree')
    return {'exact_degree':packet['exact_degree'],'residual_degrees':packet['residual_degrees'],
      'operations':packet['operations'],'system_operations':packet['system_operations'],
      'coefficient_witness_powers':powers,'coefficient':str(coeff)+'*beta^'+str(beta_power),
      'prefix_monomial_counts':{name:len(p.d) for name,p in expected.items()},
      'exact_checks':'full sparse prefix identities; independent cut-ring auxiliary, norm and SOS identities; cancellation-resolved leading forms and selected coefficients'}

def fixed_coefficients():
    binding=json.loads((ROOT/'coefficients/ACTIVE_BINDING.json').read_text())
    checks={}
    for name,entry in binding['ports'].items():
        data=(ROOT/'coefficients'/entry['gzip_payload']).read_bytes(); raw=gzip.decompress(data)
        require(hashlib.sha256(data).hexdigest()==entry['gzip_sha256'],'Gzip digest '+name)
        require(hashlib.sha256(raw).hexdigest()==entry['sha256'],'Raw digest '+name)
        require(len(raw)==entry['raw_bytes'],'Raw length '+name)
        n=int.from_bytes(raw,'little')
        require(n.bit_length()==entry['bits'],'Bit length '+name)
        if name=='beta': require(n==(1<<590069)-1,'beta exact value')
        checks[name]={'bits':n.bit_length(),'raw_bytes':len(raw),'sha256':entry['sha256']}
    require(hashlib.sha256((ROOT/'coefficients'/binding['whole_binding']).read_bytes()).hexdigest()==binding['whole_binding_sha256'],'Whole coefficient binding')
    ledger=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for entry in ledger['retained_byte_identical_files']:
        content=(ROOT/entry['path']).read_bytes()
        require(hashlib.sha256(content).hexdigest()==entry['sha256'],'Retained source '+entry['path'])
        blob=hashlib.sha1(b'blob '+str(len(content)).encode()+b'\x00'+content).hexdigest()
        require(blob==entry['git_blob_sha1'],'Git blob '+entry['path'])
    return checks

def main():
    checks={}
    for kind in (13,12):
        built=build.build(kind); path=ROOT/(built['name']+'.json')
        content=path.read_bytes()
        require(content==(json.dumps(built,indent=2)+'\n').encode(),'Byte-identical regeneration')
        packet=json.loads(content); metadata(packet)
        checks[str(kind)]=exact_prefix(packet,kind)
        checks[str(kind)]['circuit_sha256']=hashlib.sha256(content).hexdigest()
    receipt={'status':'passed','scope':'Finite exact algebra and fixed-data checks, not a consistency test or an unbounded semantic proof.',
      'circuits':checks,'coefficient_checks':fixed_coefficients()}
    (ROOT/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__': main()
