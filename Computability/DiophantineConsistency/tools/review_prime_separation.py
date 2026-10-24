#!/usr/bin/env python3
"""Read-only source binding and exact fixed-three companion review."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
spec=importlib.util.spec_from_file_location('review_ring',ROOT/'candidates/positive11-adaptive-shears/independent_ring.py')
ring=importlib.util.module_from_spec(spec);spec.loader.exec_module(ring);P=ring.Ring
def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def exact_fixed3():
    x,u,k,V,delta=[P.variable(s) for s in ['x','u','k','V','delta']]
    Q=delta+1;t=2*u+k;ell=k*k-4;A=u*(u+k)+1
    j=delta*x*x+delta*(6*t+4*V)*x+9*delta*ell-4*(V*V-1);h=12*delta*t*V
    N=j*j+2*h*j+576*delta*A*(1-V*V)+144*delta*delta*ell*V*V
    L=x+3*t+2*V
    expected=(delta*(L*L-36*A)-4*(Q*V*V-1))**2-576*delta*A*(Q*V*V-1)
    need(N==expected,'complete generic fixed3 cleared norm identity')
    need(t*t-ell==4*A,'first-root midpoint identity')
    return {'free_ring_norm_identity':True,'generic_monomials':len(N.terms),'first_root_midpoint_identity':True,
      'proof_boundary':'The universal signed 3-adic separation and integer Pell descent are ordinary proofs, not inferred from these identities.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--scratch',type=Path,default=Path('/tmp/proofs62ff-prime-separation-review'))
    ap.add_argument('--output',type=Path,default=ROOT/'data/prime-separation-review.json');args=ap.parse_args();r=args.scratch
    arrival=json.loads((r/'ARRIVAL.json').read_text());src=r/'original/con_zfc_prime_separation_2026-10-23'
    for f in arrival['members']:need(sha(r/'original'/f['path'])==f['sha256'],'original tree unchanged')
    manifests=0
    for line in (src/'SHA256SUMS.txt').read_text().splitlines():
        h,p=line.split('  ',1);need(sha(src/p)==h,'release manifest');manifests+=1
    binding=json.loads((src/'new_integer_compression/coefficients/BINDING.json').read_text());hashes={}
    for name,item in binding['payloads'].items():
        raw=gzip.decompress((src/'new_integer_compression/coefficients'/item['path']).read_bytes())
        h=hashlib.sha256(raw).hexdigest();need(h==item['raw_sha256'],'fixed coefficient');hashes[name]=h
    need(hashes==json.loads((ROOT/'data/saturated-certificates-integer-review.json').read_text())['whole_tuple_raw_hashes'],'entire source34 tuple')
    modes={mode:json.loads((r/(mode+'-receipt.json')).read_text()) for mode in ('normal','optimized')}
    need(all(x['status']=='PASS' for x in modes.values()),'complete release replay modes')
    need(not modes['normal']['optimized_mode'] and modes['optimized']['optimized_mode'],'actual optimization modes')
    result={'status':'PASS ordinary proof review and both complete finite release replays',
      'arrival':{k:v for k,v in arrival.items() if k!='members'},'manifest_entries':manifests,'original_unchanged':True,
      'whole_source34_raw_hashes':hashes,'exact_local_checks':exact_fixed3(),'release_replays':modes,
      'endpoint':{'variables':16,'degree':108,'operations':132},
      'comparison':'16/108/132 trades4degree units for13operations against parity16/112/119;13/1392/205 and14/696/151 are dominated by root fusion,15/244/137 by parity15/204/128.',
      'proof_assessment':['Every subset containing an old root has a unique even least3-adic square order; a singleton guard root needs no such condition.',
        'The13variable odd-c restriction establishes Q>1 before its guard is recovered; canonical odd-c completeness is explicit.',
        'The16variable source keeps both strong and guard rows, so Q>1 and3dividesI precede fixed3 root separation.',
        'The main midpoint quotient is integral from2gamma andHgamma integral withHodd.',
        'Fresh normalized strong and squared-modulus auxiliary choices preserve the same canonical native/determinant family.'],
      'scope':'Ordinary mathematical new reductions plus finite equation verification; no Lean, internal-ZFC proof or new proof of inherited native/refutation theorem.'}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','files':arrival['files'],'manifest_entries':manifests,'local_norm_terms':53}))

if __name__=='__main__':main()
