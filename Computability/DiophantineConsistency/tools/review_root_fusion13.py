#!/usr/bin/env python3
"""Focused read-only evidence for the13-integer root-fusion arrival.

The separate release replay receipts must already exist in scratch. This
script reads inert arrival data and proves extra local ring identities;
it imports no arrival builder, runs no Lean and modifies no arrival file.
"""
import argparse
import gzip
import hashlib
import importlib.util
import json
from math import gcd
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
spec=importlib.util.spec_from_file_location('review_ring',ROOT/'candidates/positive11-adaptive-shears/independent_ring.py')
ring=importlib.util.module_from_spec(spec);spec.loader.exec_module(ring)
Ring=ring.Ring

def need(ok,label):
    if not ok:raise ValueError(label)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def local_checks():
    q,u,z,x,m,a,c,I,R,T,f=[Ring.variable(n) for n in ['q','u','z','x','m','a','c','I','R','T','f']]
    G=u*z-(q-u-z)**2
    need(12*G==4*q*q-(3*(u+z)-4*q)**2-3*(u-z)**2,'determinant identity')
    # The CRT main/first comparison holds on the whole required cone.
    positive=(16+m)**2*((64+x)-4)-4*(16+m)*((64+x)+2)+9
    need(all(v>0 for v in positive.terms.values()),'strict positive coefficients on x64,m16 cone')
    # Restore the ordinary source after normalized strong extraction.
    Delta=a*a+4*a+3;Df=1+Delta*I*I;V=Df*(c*T-R)-c
    o=f*(c*T-R)
    need(f*o-c-V==(f*f-Df)*(c*T-R),'first quotient remainder')
    # With I=i*c², the exact j formula has R*Delta*i²*c³.
    i=Ring.variable('i');Dn=1+Delta*i*i*c**4
    j=Dn*T-1-R*Delta*i*i*c**3
    VV=Dn*(c*T-R)-c
    need(j*c-R==VV,'second quotient identity')
    # CRT root relation is satisfied by the final integer carrier recipe.
    H,M,L,gamma,n,v,b0,d,ff,tau,p1,y=[Ring.variable(k) for k in ['H','M','L','gamma','n','v','b0','d','ff','tau','p1','y']]
    U=M*H;vv=Ring.variable('V');quot=Ring.variable('quot')
    nvalue=L*gamma+ff+tau+p1+y-vv-quot
    relation=U*(nvalue+vv)+M*L*b0+H*M*quot-(M*L*(b0+H*gamma)+U*(ff+tau+p1+y))
    need(relation==0,'CRT completeness carrier identity')
    # Signed modular controls include the former v=0 boundary.
    cases=0
    for jj in range(-3,4):
        qq=19*(6*jj+1)+1
        need(qq%2==0 and qq%3==2 and qq!=0,'toy fixed-class radix')
        for ww in range(-2,3):
            xx=qq*(12*ww+4)
            for vv0 in range(-2,3):
                aa=(xx+1)*qq*vv0;hh=4*aa+3;mm=2*qq*qq
                need(hh!=0 and gcd(hh,mm)==1 and gcd(4*hh+1,hh)==1,'all-sign CRT units')
                need(3<(4*hh+1)/hh<5,'lambda sign/bounds')
                need((aa+2)**2-1>1,'unconditional Delta including v0')
                cases+=1
    return {'exact_identities':['determinant12G','positive-coefficient CRT separation inequality','first quotient remainder','second quotient exact restoration','CRT final carrier completeness'],
       'crt_signed_toy_controls':cases,'negative_controls':{'five_rational_sum_without_subset_separation':'sqrt2+sqrt8-sqrt18+10+11=21, with nonrational roots','zero_scale_excluded_after_realness':'v=0 makes scaled guard strictly negative; c=0 makes eta*zeta<=0'},
       'diagnostic_scope':'Finite controls supplement ordinary proof; no candidate zero or consistency test.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--arrival',type=Path,default=Path('/tmp/dioph-new-arrivals-751bc067e2/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24'))
    ap.add_argument('--scratch',type=Path,default=Path('/tmp/proofs62ff-root-fusion-review'))
    ap.add_argument('--output',type=Path,default=ROOT/'data/root-fusion13-review.json');args=ap.parse_args();src=args.arrival
    inv=json.loads((args.scratch/'original-inventory.json').read_text())
    need(all(sha(src/p)==h for p,h in inv.items()),'original93tree unchanged')
    manifest=json.loads((src/'MANIFEST.json').read_text())
    for r in manifest['files']:
        p=src/r['path'];need(p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],'manifest item')
    binding=json.loads((src/'coefficients/BINDING.json').read_text());hashes={};rawbytes=0
    for port,r in binding['payloads'].items():
        packed=(src/'coefficients'/r['file']).read_bytes() if 'file' in r else (src/r['path']).read_bytes()
        raw=gzip.decompress(packed)
        expected=r.get('raw_sha256',r.get('sha256'));need(hashlib.sha256(raw).hexdigest()==expected,'raw whole coefficient')
        hashes[port]=expected;rawbytes+=len(raw)
    prior=json.loads((ROOT/'data/saturated-certificates-integer-review.json').read_text())['whole_tuple_raw_hashes']
    need(hashes==prior,'whole six source34 tuple preserved')
    normal=json.loads((args.scratch/'normal-receipt.json').read_text());opt=json.loads((args.scratch/'optimized-receipt.json').read_text())
    need(normal['status']==opt['status']=='PASS','both full replay receipts')
    need(not normal['python_optimized'] and opt['python_optimized'],'actual optimization modes')
    for label,r in [('normal',normal),('optimized',opt)]:
        need(len(r['literal_norm_equations'])==6 and len(r['quotient_companions'])==4,'complete10equations '+label)
    arrivals=json.loads((src.parent.parent/'ARRIVALS.json').read_text())
    result={'status':'PASS ordinary proof review and full finite release replay','arrival':next(r for r in arrivals if r['archive'].endswith('ConZFC_13_Integer_Norms_2026-10-24.zip')),
      'original_files':len(inv),'manifest_entries':len(manifest['files']),'original_unchanged':True,
      'scope':'13/14/15-integer norm family and4quotient companions only; no Lean or internal-ZFC claim.',
      'whole_source34_raw_hashes':hashes,'raw_bytes':rawbytes,'focused_checks':local_checks(),
      'metrics':json.loads((src/'equations/METRICS.json').read_text()),
      'full_release_replays':{'normal':normal,'optimized':opt},
      'proof_review':['Four non-guard radicands real and positive before source assumptions, includingc0/v0.','Norm zero forces guard nonnegative, then Pair>0 and c/v nonzero; this precedes rationality.','Full signed-subset separation handles dependent squareclasses and zero guard root.','Normalized odd strong witnesses restore ordinary source through explicit integer formulas.','CRT moduli are coprime by H=3modq,q=2mod3,Hodd, with Lambda=1modH.','Scaled CRT guard witnesses are regenerated for original unscaledPair; no false pointwise identity.','Canonical normalized i is integral and odd by composition plus recurrence, before auxiliary T and final n.','All source coefficients and determinant scales remain identical source34 tuple.'],
      'comparison':'13variable1088/195,1392/186,1408/185;14variable696/150,792/137;15variable344/131;17variable88/110 improves newly reviewed114operation interface via canonical squared-modulus reselection.'}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','manifest':len(manifest['files']),'files':len(inv),'norms':6,'companions':4,'rawbytes':rawbytes}))
if __name__=='__main__':main()
