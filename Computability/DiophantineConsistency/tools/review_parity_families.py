#!/usr/bin/env python3
"""Read-only ordinary-math review evidence for the two distinct parity ZIPs."""
import argparse
from fractions import Fraction
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
spec=importlib.util.spec_from_file_location('review_ring',ROOT/'candidates/positive11-adaptive-shears/independent_ring.py')
ring=importlib.util.module_from_spec(spec);spec.loader.exec_module(ring);Ring=ring.Ring
def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def local_checks():
    t,a,delta,r=[Ring.variable(x) for x in ('t','a','delta','r')]
    A=4*a+1;x=2*t+1;G=(delta*(t*(t+1)-a)-r)**2-A*delta*r
    need(16*G==(delta*(x*x+A)-4*r)**2-4*A*x*x*delta*delta,'primitive odd-carrier identity')
    d,L,Q,A,u,tau=[Ring.variable(x) for x in ('d','L','Q','A','u','tau')]
    U=d*(L*L-A)+Q;N=U*U-4*d*L*L*Q
    need((2*d*L*L-U)**2-4*d*d*L*L*A==N,'mod4 rational-root extraction')
    L=u+tau;Q=d*u*u;N=(d*(L*L-A)+Q)**2-4*d*L*L*Q
    need(N==d*d*(tau*tau-A)*((tau+2*u)**2-A),'mod4 completeness factorization')
    m,k=[Ring.variable(x) for x in ('m','k')]
    A=1+m*(m+1)*k*k;S=k*(2*m+1)
    need(S*S-4*A==k*k-4,'guard-only separation')
    positive=0;zeros=0
    for aa in range(-4,5):
      for dd in range(-4,5):
       if not dd:continue
       for rr in range(-40,41):
        for tt in range(-10,11):
         A=4*aa+1;x=2*tt+1
         g=(dd*(tt*(tt+1)-aa)-rr)**2-A*dd*rr
         if g:continue
         U=Fraction(dd*(x*x+A)-4*rr,2*x*dd);y=(x-U)/2
         need(U.denominator==y.denominator==1 and U*U==A and dd*y*y==rr,'signed primitive extraction controls')
         zeros+=1
    for c in [-3,-2,-1,1,2,3]:
      for u in [-5,-3,-1,1,3,5]:
       for tau in [-5,-3,-1,1,3,5]:
        tau=tau if (tau-u)%4==0 else -tau
        for B0 in [-8,-4,0,4,8]:
         n0=Fraction(u+tau-B0-2,4);need(n0.denominator==1,'private root sign makes carrier integral')
         L=4*n0+2+B0;A=tau*tau;d=c**4;Q=d*u*u;U=d*(L*L-A)+Q
         need(L%4==2 and U*U-4*d*L*L*Q==0,'mod4 carrier completeness')
         positive+=1
    return {'free_ring_identities':['primitive odd-carrier norm','mod4 rational-root extraction','mod4 completeness factorization','guard-only S²-4A'],
      'signed_primitive_zero_controls':zeros,'mod4_private_root_sign_controls':positive,
      'negative_control':'Bare L=0,A=5,d=1,Q=5 norm vanishes with irrational roots; affine carriers exclude this branch.',
      'scope':'Finite fixtures supplement ordinary proofs, not a source-zero or consistency search.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--scratch',type=Path,default=Path('/tmp/proofs62ff-parity-review'))
    ap.add_argument('--output',type=Path,default=ROOT/'data/parity-families-review.json');args=ap.parse_args();r=args.scratch
    first=r/'first/original/con-zfc-parity-norms-2026-10-23';second=r/'second/original/con-zfc-parity-norms'
    arrivals={}
    for label in ('first','second'):
        o=json.loads((r/label/'ARRIVAL.json').read_text())
        for f in o['members']:need(sha(r/label/'original'/f['path'])==f['sha256'],'full original tree preserved')
        arrivals[label]={k:v for k,v in o.items() if k!='members'}
    nfirst=0
    for line in (first/'SHA256SUMS').read_text().splitlines():
        h,p=line.split('  ',1);need(sha(first/p)==h,'first manifest');nfirst+=1
    secondmanifest=json.loads((second/'MANIFEST.json').read_text())
    for name,h in secondmanifest['files'].items():
        need(sha(second/name)==h,'second manifest')
    prior=json.loads((ROOT/'data/saturated-certificates-integer-review.json').read_text())['whole_tuple_raw_hashes']
    for label,base in [('first',first),('second',second/'integer-norms')]:
        binding=json.loads((base/'coefficients/BINDING.json').read_text());hashes={}
        for name,f in binding['ports'].items():
            p=base/f['path'] if 'path' in f else base/'coefficients'/f['file']
            raw=gzip.decompress(p.read_bytes());h=hashlib.sha256(raw).hexdigest()
            need(h==f.get('raw_sha256',f.get('sha256_raw')),'actual fixed coefficient');hashes[name]=h
        need(hashes==prior,'whole source34 tuple '+label)
    firstnormal=json.loads((r/'first/normal-receipt.json').read_text());firstopt=json.loads((r/'first/optimized-receipt.json').read_text())
    need(firstnormal['status']==firstopt['status']=='PASS','first release modes')
    secondnormal=json.loads((r/'second/normal/CHECKS.json').read_text());secondopt=json.loads((r/'second/optimized/CHECKS_OPTIMIZED.json').read_text())
    need(secondnormal['status']==secondopt['status']=='PASS' and secondopt['mode']=='optimized','second check modes')
    rebuilt=json.loads((r/'second/build-receipt.json').read_text());need(rebuilt['status']=='PASS','second literal rebuild')
    result={'status':'PASS ordinary proof review and scoped finite replays','scope':'Both small-integer norm components; second direct-quartic and integer20 components not reviewed or replayed.',
      'arrivals':arrivals,'manifest_entries':{'first':nfirst,'second':len(secondmanifest['files'])},'whole_source34_raw_hashes':prior,
      'first_normal_full_release':firstnormal,'first_optimized_seven_audits':firstopt,
      'second_normal_six_norm_audits':secondnormal,'second_optimized_six_norm_audits':secondopt,'second_regeneration':rebuilt,
      'focused_checks':local_checks(),'primary_tradeoffs':{'first15':{'variables':15,'degree':204,'operations':128},
        'second16':{'variables':16,'degree':112,'operations':119}},
      'proof_boundary':'Ordinary source calibration remains inherited. No Lean, internal-model or consistency claim is added.'}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','manifests':result['manifest_entries'],'whole_tuple_preserved':True}))

if __name__=='__main__':main()
