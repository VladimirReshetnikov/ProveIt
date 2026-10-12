"""Native sparse/dense incidence audits and complete certified-query timings."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
import time
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from fastunknot.interval_orbits import IntervalPairing as P, SignedPairing as SP
from fastunknot.interval_incidence import analyze_port_incidence as dense, verify_port_incidence_certificate as dense_verify
from fastunknot.sparse_incidence import analyze_sparse_port_incidence as sparse, analyze_sparse_signed_incidence as signed
from fastunknot.sparse_incidence_verify import verify_sparse_port_incidence_certificate as verify, verify_sparse_signed_incidence_certificate as signed_verify
from fastunknot.integer_codec import json_safe
BASELINE='308d5aad3b70b8e21c428cc3b818b730c0f6adbc';SEED=261008526


def sources():
    paths=list((ROOT/'fastunknot').rglob('*.py'))+[Path(__file__),ROOT/'tests/test_sparse_incidence.py',ROOT/'tests/test_sparse_incidence_integration.py']
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths}


def encode(x):return json.dumps(json_safe(x),sort_keys=True,separators=(',',':')).encode()


def fixtures():
    L=1<<256;out=[]
    for r in (6,8,10):out.append((f'disjoint-{r}',(r+2)*L,[],[[(i*L,(i+1)*L)] for i in range(r)],{0:2*L,**{1<<i:L for i in range(r)}}))
    for r in (4,10):out.append((f'coincident-{r}',8*L,[],[[(L,3*L)]]*r,{0:6*L,(1<<r)-1:2*L}))
    out.append(('nested-10',12*L,[],[[(0,(i+1)*L)] for i in range(10)],{0:2*L,**{1023^((1<<j)-1):L for j in range(10)}}))
    out.append(('paired-blocks-8',4*L,[P(0,L-1,L,2*L-1),P(2*L,3*L-1,3*L,4*L-1,True)],[[(i*(L//8),(i+1)*(L//8))] for i in range(8)],{0:L,**{1<<i:L//8 for i in range(8)}}))
    out.append(('all-signatures-6',64,[],[[(x,x+1) for x in range(64) if x>>i&1] for i in range(6)],{x:1 for x in range(64)}))
    return out


def audit():
    comparisons=0;proofs=0
    for pattern in range(256):
        support=[t for t in range(8) if pattern>>t&1];n=len(support)
        ports=[[(j,j+1) for j,t in enumerate(support) if t>>i&1] for i in range(3)];expected={t:1 for t in support}
        d=dense(n,[],ports,record_certificate=True)
        assert {i:w for i,w in enumerate(d['histogram']) if w}==expected
        assert dense_verify(n,[],ports,d['certificate']);proofs+=1
        for strategy in ('linear','split'):
            s=sparse(n,[],ports,strategy=strategy,record_certificate=True)
            assert dict(s['histogram'])==expected and verify(n,[],ports,s['certificate'])
            comparisons+=1;proofs+=1
    large=[]
    for name,n,ps,ports,expected in fixtures():
        for strategy in ('linear','split'):
            s=sparse(n,ps,ports,strategy=strategy,record_certificate=True)
            assert dict(s['histogram'])==expected and verify(n,ps,ports,s['certificate'])
            large.append(dict(name=name,strategy=strategy,stats=s['stats'],histogram_sha256=sha256(encode(sorted(expected.items()))).hexdigest()))
    signed_checks=0
    for parity in (0,1):
        n=1<<1024;ps=[SP(P(0,n-1,0,n-1),parity)];ports=[[(0,7)],[(7,13)],[]]
        result=signed(n,ps,ports,strategy='split',record_certificate=True)
        assert signed_verify(n,ps,ports,result['certificate'])
        assert {m:(a,b) for m,a,b in result['signed_histogram']}=={0:((n-13,0) if parity==0 else (0,n-13)),1:((7,0) if parity==0 else (0,7)),2:((6,0) if parity==0 else (0,6))}
        signed_checks+=1
    return dict(exhaustive_histograms=256,dense_sparse_comparisons=comparisons,independent_small_replays=proofs,analytic_large_cases=large,huge_signed_identity_checks=signed_checks,
        scope='Native supplied interval systems. All three complete interfaces are checked against explicit components; huge fixtures use analytic multiplicities and independent source replay. No knot-discovery claim.')


def benchmark():
    rng=random.Random(SEED);rows=[];proofs={};arms=('dense','dense_AA','linear','linear_AA','split','split_AA')
    for name,n,ps,ports,expected in fixtures():
        samples=[];warmups=[]
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);measurements={}
            for arm in order:
                kind=arm.removesuffix('_AA');start=time.perf_counter()
                if kind=='dense':
                    result=dense(n,ps,ports,max_ports=len(ports),record_certificate=True)
                    complete=result['status']=='COMPLETE';assert complete
                    assert dense_verify(n,ps,ports,result['certificate'],max_ports=len(ports))
                else:
                    result=sparse(n,ps,ports,strategy=kind,record_certificate=True)
                    complete=result['status']=='COMPLETE';assert complete
                    assert verify(n,ps,ports,result['certificate'])
                elapsed=time.perf_counter()-start
                hist={i:w for i,w in enumerate(result['histogram']) if w} if kind=='dense' else dict(result['histogram'])
                assert hist==expected
                raw=encode(result['certificate']);key=sha256(raw).hexdigest();proofs[key]=result['certificate']
                measurements[arm]=dict(seconds=elapsed,completed=complete,stats=result['stats'],certificate_bytes=len(raw),certificate_sha256=key)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={a:median(s['measurements'][a]['seconds'] for s in samples) for a in arms}
        pairs=[('linear','dense','linear'),('split','dense','split')]+[(a+'_AA',a,a+'_AA') for a in ('dense','linear','split')]
        ratios={key:median(s['measurements'][old]['seconds']/s['measurements'][new]['seconds'] for s in samples) for key,old,new in pairs}
        rows.append(dict(name=name,size=n,pairings=[[p.a,p.b,p.c,p.d,-1 if p.reverse else 1] for p in ps],ports=ports,expected=sorted(expected.items()),samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios))
        print(name,json.dumps(dict(medians=medians,ratios=ratios)),flush=True)
    return dict(cases=rows,certificates=proofs,measured_calls=len(rows)*30,warmup_calls=len(rows)*6,completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),
        scope='Complete supplied incidence queries, including input validation, proof construction and independent source replay. Same maintained orbit engine in all six shuffled arms; five rounds and one warm-up. No expansion of huge point universes. Serialization and analytic output assertions are outside timing. These are local topology observers, not complete knot recognition.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('audit','benchmark'));p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    before=sources();pins={}
    for name in ('interval_incidence.py','interval_orbits.py','interval_orbit_verify.py','integer_codec.py'):
        raw=subprocess.check_output(['git','show',f'{BASELINE}:Topology/UnknotRecognition/fast/fastunknot/{name}'],cwd=ROOT)
        assert raw==(ROOT/'fastunknot'/name).read_bytes();pins[name]=sha256(raw).hexdigest()
    start=time.perf_counter();result={'audit':audit,'benchmark':benchmark}[args.mode]()
    assert before==sources()
    result.update(seconds=time.perf_counter()-start,mode=args.mode,seed=SEED,baseline_commit=BASELINE,baseline_unchanged_modules=pins,source_sha256=before,source_hashes_unchanged=True,python=platform.python_version(),platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','source_sha256','analytic_large_cases')},indent=2))


if __name__=='__main__':main()
