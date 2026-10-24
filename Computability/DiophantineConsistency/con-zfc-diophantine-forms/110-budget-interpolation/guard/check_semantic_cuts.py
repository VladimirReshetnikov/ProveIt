#!/usr/bin/env python3
"""Exact local proof-cut diagnostics; no claim to verify native calibration."""
from pathlib import Path
import gzip, hashlib, json
from exact_polynomial import Ring
ROOT=Path(__file__).resolve().parent

def require(ok, message):
    if not ok: raise ValueError(message)

def equal(p,q,label):
    require(not (p-q).terms, label+' failed')

def positive_on_orthant(p,label):
    require(p.terms.get(p.ring.zero,0)>0,label+' lacks positive constant')
    require(all(c>=0 for c in p.terms.values()),label+' has negative coefficient')
    return {'label':label,'monomials':len(p.terms),'positive_constant':p.terms[p.ring.zero]}

def main():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for row in pins['sources']:
        raw=(ROOT/row['path']).read_bytes()
        require(len(raw)==row['bytes'],'source length: '+row['path'])
        require(hashlib.sha256(raw).hexdigest()==row['sha256'],'source hash: '+row['path'])
    active=json.loads((ROOT/'coefficients/BINDING.json').read_text())
    for name,row in active['payloads'].items():
        raw=gzip.decompress((ROOT/'coefficients'/row['file']).read_bytes())
        for sub in ['centered17','centered18']:
            old=gzip.decompress((ROOT/'provenance'/sub/'coefficients'/(name+'.bin.gz')).read_bytes())
            require(raw==old,'coefficient tuple mismatch: '+sub+'/'+name)
    ring=Ring(['sx','sm','sc','sq']); sx,sm,sc,sq=(ring.var(n) for n in ring.names)
    x,m,C=sx+64,sm+16,sc+16
    tests=[]
    tests.append(positive_on_orthant(m*m*(x-4)-4*m*(x+2)+9,'four d-bound minus three tau-bound'))
    tests.append(positive_on_orthant(2*x*m*m-6*m-5,'tau exceeds three times c upper bound'))
    tests.append(positive_on_orthant((x-1)*m-6,'sqrt Delta exceeds three'))
    tests.append(positive_on_orthant(509*C-255,'small auxiliary pair below three c'))
    tests.append(positive_on_orthant(2*(sq+16)**3-510*(sq+16)-1,'guard below c divided by 255'))
    tests.append(positive_on_orthant(9*C**4-6*C*C-C,'large auxiliary branch exceeds twice f'))
    ring=Ring(['tau','L','k','y','V','Q','q','F','C','K0','W','z','M','H','gamma','lc','b0','f','p1','vold','S'])
    d={n:ring.var(n) for n in ring.names}
    tau,L,k,y,V,Q,q,F,C,K0,W,z,M,H,gamma,lc,b0,f,p1,vold,S=(d[n] for n in ring.names)
    equal((tau-L)**2+(2*(tau-L)-k)*L-1,tau*tau-L*(L+k)-1,'first-root translation')
    equal(V*V-(Q-1)*(y-V)*(2*V+y-V)-1,Q*V*V-(Q-1)*y*y-1,'auxiliary-root translation')
    alpha=q-F-C
    equal((q-1)*(q-F)+alpha,q*(q-F)-C,'packed R abbreviation')
    restoredF=(K0+W)*C-z*(q-1)
    equal((K0+W)*C-restoredF-z*(q-1),ring.scalar(0),'transport restoration')
    U=M*H
    n=lc*gamma+f+tau+p1+y-V-vold-S
    Z=U*(n+V+S)+M*lc*b0+H*M*vold
    equal(Z,M*lc*(b0+H*gamma)+U*(f+tau+p1+y),'canonical CRT carrier and shear')
    result={'status':'PASS','source_files_authenticated':len(pins['sources']),
        'same_six_source34_coefficients':True,'exact_restoration_cut_identities':5,
        'positive_coefficient_bounds':tests,
        'boundary':'Proof-cut checks and source transcription authentication; not verification of inherited native/compiler or calibration theorems.'}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
