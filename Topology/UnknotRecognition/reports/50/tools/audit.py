"""Exhaustive small support audit, JSON replay, examples, and censored controls."""
from bootstrap import bootstrap
ROOT=bootstrap()
from fastunknot.interval_orbits import IntervalPairing as P, SignedPairing as SP
from fastunknot.interval_incidence import analyze_port_incidence as dense
from fastunknot.sparse_incidence import analyze_sparse_port_incidence as sparse
from fastunknot.sparse_incidence import analyze_sparse_signed_incidence as signed
from fastunknot.sparse_incidence_verify import verify_sparse_port_incidence_certificate as verify
from fastunknot.sparse_incidence_verify import verify_sparse_signed_incidence_certificate as signed_verify
from fastunknot.integer_codec import json_safe
import json, time, sys
from unittest.mock import patch
from benchmark import fixtures, digest

class AuditDeadline(TimeoutError):pass


def main():
    saved=json.loads((ROOT/'results/benchmark.json').read_text())
    saved_rows={c['name']:c for c in saved['cases']}
    analytic=0; L=1<<256
    for name,n,ps,pp in fixtures():
        r=len(pp)
        if name.startswith('static-disjoint'):
            expected={0:2*L,**{1<<i:L for i in range(r)}}
        elif name.startswith('coincident'):
            expected={0:6*L,(1<<r)-1:2*L}
        elif name.startswith('nested'):
            expected={0:2*L,**{((1<<r)-1)^((1<<j)-1):L for j in range(r)}}
        elif name.startswith('paired-blocks'):
            expected={0:L,**{1<<j:L//8 for j in range(8)}}
        else:
            expected={t:1 for t in range(64)}
        assert digest(expected)==saved_rows[name]['output_sha256'],name
        analytic+=1
    basic_ports=[[(2,10)],[(5,17)],[(10,17)]]
    basic=sparse(17,[],basic_ports,record_certificate=True)
    assert dict(basic['histogram'])=={0:2,1:3,3:5,6:7}
    assert verify(17,[],basic_ports,basic['certificate'])
    (ROOT/'examples/basic_sparse_certificate.json').write_text(json.dumps(json_safe(dict(
        size=17,pairings=[],ports=basic_ports,certificate=basic['certificate'])),indent=2))
    pairs=0;certs=0
    for pattern in range(256):
        supports=[t for t in range(8) if pattern>>t&1]
        n=len(supports)
        ports=[[(j,j+1) for j,t in enumerate(supports) if t>>i&1] for i in range(3)]
        expected={t:1 for t in supports}
        d=dense(n,[],ports)
        assert {i:w for i,w in enumerate(d['histogram']) if w}==expected
        for strategy in ('linear','split'):
            s=sparse(n,[],ports,strategy=strategy,record_certificate=True)
            assert dict(s['histogram'])==expected
            assert verify(n,[],ports,s['certificate'])
            pairs+=1;certs+=1
    n=1<<16000;ports=[[(0,17)],[(30,40)],[(0,17)],[]]
    x=sparse(n,[],ports,record_certificate=True)
    old=sys.get_int_max_str_digits()
    transported=json.loads(json.dumps(json_safe(x['certificate'])))
    assert verify(n,[],ports,transported)
    assert old==sys.get_int_max_str_digits()
    (ROOT/'examples/huge_static_certificate.json').write_text(json.dumps(json_safe(dict(
        size=n,pairings=[],ports=ports,certificate=x['certificate'])),indent=2))
    ps=[SP(P(0,0,1,1),0),SP(P(1,1,2,2),0),SP(P(0,0,2,2),1),SP(P(3,3,4,4),0)]
    pp=[[(0,2)],[(2,4)],[(5,6)]]
    ss=signed(6,ps,pp,strategy='split',record_certificate=True)
    with patch('fastunknot.sparse_incidence.count_orbits',side_effect=RuntimeError('producer disabled')), \
         patch('fastunknot.sparse_incidence.recover_nonnegative',side_effect=RuntimeError('producer disabled')), \
         patch('fastunknot.sparse_incidence.signed_cover',side_effect=RuntimeError('producer disabled')):
        assert signed_verify(6,ps,pp,ss['certificate'])
    rows=[dict(pairing=[p.pairing.a,p.pairing.b,p.pairing.c,p.pairing.d,-1 if p.pairing.reverse else 1],parity=p.parity) for p in ps]
    (ROOT/'examples/signed_triangle_certificate.json').write_text(json.dumps(json_safe(dict(
        size=6,signed_pairings=rows,ports=pp,certificate=ss['certificate'])),indent=2))
    censored=[]
    for r in (32,128,256):
        n=1<<500;pp=[[(2*i,2*i+1)] for i in range(r)]
        start=time.perf_counter();limit=start+5.0
        def check():
            if time.perf_counter()>limit:raise AuditDeadline('five-second cooperative driver allowance')
        try:
            x=sparse(n,[],pp,strategy='split',record_certificate=True,check=check)
            assert verify(n,[],pp,x['certificate'],check=check)
            assert dict(x['histogram'])=={0:n-r,**{1<<i:1 for i in range(r)}}
            c=dict(r=r,status='COMPLETE',seconds=time.perf_counter()-start,stats=x['stats'])
        except AuditDeadline:
            c=dict(r=r,status='CANCELLED_BY_DRIVER',seconds=time.perf_counter()-start,
                   histogram_published=False,ratio=None)
        censored.append(c);print(c,flush=True)
    result=dict(analytic_large_fixture_digest_checks=analytic,exhaustive_boolean_histograms=256,native_dense_sparse_comparisons=pairs,
                independent_sparse_replays=certs,hex_roundtrip=True,
                decimal_limit_unchanged=True,signed_producers_disabled_replay=True,
                gapped_port_controls=censored,
                earlier_aborted_run='benchmark_aborted.log: process stopped at 200 seconds during gapped large-case phase; no complete large-case samples retained')
    (ROOT/'results/audit.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
