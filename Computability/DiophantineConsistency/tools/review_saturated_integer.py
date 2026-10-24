#!/usr/bin/env python3
"""Read-only focused review of the saturated-certificates integer component.

Does not rerun its release suite, import arrival code, or invoke Lean.
"""
import argparse
from collections import Counter
from fractions import Fraction
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
RING=ROOT/'candidates/positive11-adaptive-shears/independent_ring.py'
spec=importlib.util.spec_from_file_location('review_sparse_ring',RING)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
Ring,expand=m.Ring,m.expand

def need(ok,label):
    if not ok:raise ValueError(label)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def audit_dag(path):
    x=json.loads(path.read_text());nodes=x['nodes'];counts=Counter();inputs=[]
    for i,node in enumerate(nodes):
        kind=node['type']
        if kind in ['add','sub','mul']:
            need(0<=node['left']<i and 0<=node['right']<i,'backward DAG references');counts[kind]+=1
        else:
            need(kind in ['variable','fixed','constant'],'literal leaf type')
            if kind!='constant':inputs.append((kind,node['value']))
    seen=set();todo=[x['output']]
    while todo:
        i=todo.pop()
        if i not in seen:
            seen.add(i);n=nodes[i]
            if n['type'] in ['add','sub','mul']:todo.extend([n['left'],n['right']])
    need(len(seen)==len(nodes),'all nodes live')
    need(len(inputs)==len(set(inputs)),'distinct input leaves')
    need([v for k,v in inputs if k=='variable']==x['variables'],'ordered variables')
    need(set(v for k,v in inputs if k=='fixed')==set(x['fixed_ports']),'six fixed ports live')
    need(dict(counts)==x['counts'] and sum(counts.values())==x['live_binary_operations'],'literal operation metrics')
    return {'sha256':sha(path),'variables':len(x['variables']),'fixed_ports':len(x['fixed_ports']),'operations':sum(counts.values()),'counts':dict(counts),'all_nodes_and_inputs_live':True}

def exact_identities():
    names=['c','f','R','T','b','n','A','Q','S','V','m','k','B0','tau','delta']
    s={n:Ring.variable(n) for n in names};c,f,R,T,b,n,A,Q,S,V,mm,k,B0,tau,delta=[s[x] for x in names]
    val=c*(T*f-1)-R*f*f;o=c*T-R*f;j=T*f-1-R*b
    need(o*f-c==val,'first restored quotient')
    need(j*c-R-val==-R*(c*b-f*f+1),'sole quotient remainder')
    need(f*(o*f+R)-o*(f*f-1)==o+R*f,'forward CRT identity')
    A0=1+mm*(mm+1)*k*k;Ss=k*(2*mm+1)
    need(Ss*Ss-4*A0==k*k-4,'guard-only separation')
    total=n+B0+S*V
    lhs=(Q-1)*(total*total-(1+B0*B0+mm*k*k))-S*S*(Q*V*V-1)
    right=(Q-1)*(n*n+2*n*(B0+S*V)+2*B0*S*V-mm*k*k-1)+S*S*(1-V*V)
    need(lhs==right,'centered rational norm')
    need((n*n+A-b)**2-4*n*n*A==(n*n-A-b)**2-4*A*b,'rational norm extraction')
    # Relation to the preceding Pell-congruences17/88 half-centered root.
    tp=2*tau-k;P=B0+k
    need(tp*tp+2*tp*(2*P-k)+k*k-4==4*(tau*tau+(2*tau-k)*B0-1),'earlier17 half-center comparison')
    need((2*tau-k+k)==2*tau,'half-center inverse parity')
    # A primitive-norm or gcd argument is not silently substituted for separation.
    def norm(a,q,ss,vv,nn):
        dd=q-1;bb=ss*ss*(q*vv*vv-1)
        return (dd*(nn*nn-a)-bb)**2-4*dd*a*bb
    need(norm(7,2,1,2,0)==0,'equal-radicand negative control')
    need(all(u*u!=7 for u in range(-7,8)),'nonsquare negative control')
    need(2-4*Fraction(1,2)**2==1,'nonadjacent rational Pell negative control')
    ctr=0
    for cc in range(-12,13):
        if not cc:continue
        for ff in range(-8,9):
            if (ff*ff-1)%cc:continue
            bb=(ff*ff-1)//cc
            for rr in range(-4,5):
                for tt in range(-4,5):
                    vv=cc*(tt*ff-1)-rr*ff*ff;oo=cc*tt-rr*ff;jj=tt*ff-1-rr*bb
                    need(vv==oo*ff-cc==jj*cc-rr,'signed quotient fixture')
                    need((oo+rr*ff)%cc==0 and (oo+rr*ff)//cc==tt,'integer inverse fixture');ctr+=1
    return {'exact':['quotient first restoration','quotient conditional second remainder','forward quotient/CRT identity','guard-only separation','centered norm cancellation','rational extraction identity','prior17 half-centered root relation'],
      'signed_quotient_diagnostics':ctr,'negative_controls':['A7,Q2,S1,V2,n0 yields a false root if separation omitted','nonadjacent coefficients admit ordinate1/2']}

def compare23(root,prior):
    new=json.loads((root/'integer/equations/integer23_degree10.json').read_text())
    old=json.loads(prior.read_text())
    aliases={'J3':'J','v_scale':'v','w3':'w','pair_root':'t','pair_pos1':'p1','pair_pos2':'p2','pair_pos3':'p3'}
    sy={n:Ring.variable(n) for n in new['variables']+new['fixed_ports']}
    env=dict(sy)
    for n,formula in new['registers'].items():env[n]=expand(formula,env)
    newrows=[expand(formula,env) for formula in new['residuals']]
    oldenv={n:sy[aliases.get(n,n)] for n in old['variables']+old['fixed_numerals']}
    oldrows=[expand(formula,oldenv) for formula in old['residuals']]
    unmatched=list(oldrows);matches=[]
    for i,row in enumerate(newrows):
        candidates=[j for j,other in enumerate(unmatched) if row==other or row==-other]
        need(candidates,'new23 row absent from shears23')
        unmatched.pop(candidates[0]);matches.append(i)
    need(not unmatched,'all11 rows matched under renaming')
    return {'same_squared_polynomial_as_shears23_under_renaming':True,'row_count':len(matches),'renaming':aliases,'prior_sha256':sha(prior)}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--arrival',type=Path,default=Path('/tmp/dioph-wave11-arrivals-d42be5cd87/con-zfc-saturated-certificates-2026-10-24'))
    ap.add_argument('--output',type=Path,default=ROOT/'data/saturated-certificates-integer-review.json');args=ap.parse_args();root=args.arrival
    inventory={str(p.relative_to(root)):sha(p) for p in root.rglob('*') if p.is_file()}
    ledger=0
    for line in (root/'MANIFEST.sha256').read_text().splitlines():
        digest,rel=line.split('  ',1);need(sha(root/rel)==digest,'manifest '+rel);ledger+=1
    binding=json.loads((root/'integer/coefficients/BINDING.json').read_text());actual={};rawhash={};rawbytes=0
    for port,r in binding['ports'].items():
        p=root/'integer'/r['path'];packed=p.read_bytes();raw=gzip.decompress(packed)
        need(hashlib.sha256(packed).hexdigest()==r['gzip_sha256'],'compressed port hash')
        need(hashlib.sha256(raw).hexdigest()==r['raw_sha256'],'raw port hash')
        val=int.from_bytes(raw,'little');need(val.bit_length()==r['bits'] and len(raw)==r['raw_bytes'],'port encoding size')
        actual[port]=val;rawhash[port]=r['raw_sha256'];rawbytes+=len(raw)
    need(actual['beta']==(1<<1064921)-1 and actual['beta']%3==1,'whole source34 base')
    need(actual['cone_A']==1<<1113 and actual['cone_B']==1<<666104,'two literal determinant powers')
    need(0<actual['MC']<actual['beta']<actual['MF']<2*actual['beta'] and actual['K0']>=0,'native coefficient bounds')
    priorhash=json.loads((ROOT/'PROPOSAL_REVIEW_PELL_CONGRUENCES_INTEGER.json').read_text())['whole_tuple_raw_hashes']
    need(rawhash==priorhash,'all six identical to previously reviewed tuple')
    dags={p.stem:audit_dag(p) for p in (root/'integer/circuits').glob('*.json')}
    identities=exact_identities()
    comparison=compare23(root,Path('/tmp/dioph-wave11-arrivals-440dd03ab8/ConZFC_Polynomial_Shears_2026-10-23/con_zfc_polynomial_shears/integer/forms/centered23_degree10.json'))
    need(all(sha(root/rel)==digest for rel,digest in inventory.items()),'arrival unchanged')
    result={'status':'PASS focused ordinary-proof and read-only finite review','arrival':json.loads((root.parent/'ARRIVAL.json').read_text()),
      'scope':'Integer component only; parent already replayed five root audits normally/-O, so full suite intentionally not rerun; no Lean.',
      'original_files':len(inventory),'manifest_entries_checked':ledger,'original_unchanged':True,
      'whole_tuple_raw_hashes':rawhash,'raw_bytes':rawbytes,'literal_dags':dags,'focused_exact_checks':identities,'prior23_comparison':comparison,
      'delivered_release_receipt_sha256':sha(root/'verification/RELEASE_CHECKS_BOTH.json'),
      'delivered_integer_normal_receipt_sha256':sha(root/'integer/certificates/VERIFIED_NORMAL.json'),
      'delivered_integer_optimized_receipt_sha256':sha(root/'integer/certificates/VERIFIED_OPTIMIZED.json'),
      'normal_optimized_focused_mode':'optimized' if not __debug__ else 'normal',
      'proof_assessment':'Quotient bootstrap precedes deleted congruences; sign cases and rational-norm separation valid; finalizer needs only G>=0; native/strong-rank calibration inherited.',
      'operation_comparison':'17/88/114 dominates reviewed17/112/124 and17/110/140;16/184/135 vs16/192/134 is genuine1op/8degree tradeoff;23/10/131 repeats shears polynomial under renaming and gives explicit counted DAG.'}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','files':len(inventory),'manifest':ledger,'dags':len(dags),'same23':comparison['same_squared_polynomial_as_shears23_under_renaming']}))
if __name__=='__main__':main()
