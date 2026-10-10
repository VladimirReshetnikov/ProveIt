"""Exact sign and critical-value certificates for Stieltjes indices 6 and 7.

Floating-point exploration supplies rational bracket proposals only. All
acceptance decisions here use outward integer/rational arithmetic and the
written Euler--Maclaurin bound valid for every fixed nonnegative index.
The analytic global multiplicity bound and critical-point descent complete
the proof; the finite certificates alone are not a global root-count scan.
"""
from pathlib import Path
from fractions import Fraction
import hashlib, importlib.util, json, sys

sys.dont_write_bytecode=True
B=Path(__file__).resolve().parents[1]
source=B.parent/'reports/relation-cm-zero-transitions/code/certify_n5_zeros.py'
spec=importlib.util.spec_from_file_location('higher_zero_interval',source)
core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
# The interval formula is index-uniform. Rebuild the elementary symmetric
# coefficient table to degree seven; do not change the delivered source.
core.INDEX=7
core.E[:]=[core.elementary(k) for k in range(80)]
proposals=json.loads((B/'verification/higher-zero-proposals.json').read_text())
records=[];counts={};all_rows=[]
for n,threshold in [(6,4),(7,5)]:
    rows={r['k']:r for r in proposals['rows'] if r['n']==n}
    assert set(rows)==set(range(1,threshold+1))
    assert len(rows[threshold]['roots'])==n
    previous_signs={}
    for k in range(threshold,0,-1):
        roots=rows[k]['roots'];brackets=[];signs=[]
        for j,s in enumerate(roots):
            r=Fraction(s);scale=10**14
            lo=Fraction((r.numerator*scale)//r.denominator,scale)
            hi=lo+Fraction(1,scale)
            left,le=core.enclosure(k,lo,n=n)
            right,re=core.enclosure(k,hi,n=n)
            assert left.sign()==(-1)**j and right.sign()==-(-1)**j,(n,k,j,'root signs')
            record=dict(n=n,k=k,j=j+1,bracket=[str(lo),str(hi)],
                left=left.record(),right=right.record(),
                left_sign=left.sign(),right_sign=right.sign(),
                analytic_error_upper_integers=[str(le),str(re)])
            if k>1:
                previous,pe=core.enclosure(k-1,lo,hi,n=n)
                assert previous.sign()!=0,(n,k,j,'unresolved critical value')
                record.update(previous_order_interval=previous.record(),
                    previous_order_sign=previous.sign(),
                    previous_analytic_error_upper_integer=str(pe),
                    previous_decimal_enclosure=core.short_interval(previous,10))
                signs.append(previous.sign())
            brackets.append((lo,hi));records.append(record)
            print(n,k,j+1,'signs',left.sign(),right.sign(),
                  'previous',record.get('previous_order_sign'),flush=True)
        assert all(brackets[j][1]<brackets[j+1][0] for j in range(len(brackets)-1))
        if k>1:
            assert signs[-1]==(-1)**n
            # U_(n,k-1)'=-U_(n,k). On every interval between these
            # complete critical points, the predecessor is strictly monotone.
            sequence=[1,*signs]
            derived=sum(a!=b for a,b in zip(sequence,sequence[1:]))
            assert derived==len(rows[k-1]['roots']),(n,k,'descent count')
            previous_signs[k-1]=dict(critical_value_signs=signs,derived_count=derived)
    counts[str(n)]=dict(saturation_threshold=threshold,
        counts_before_and_at_threshold=[len(rows[k]['roots']) for k in range(1,threshold+1)],
        critical_point_descent=previous_signs,
        all_later_counts=n,all_zeros_simple=True)
result=dict(status='PASS',arithmetic='Outward integer intervals and exact fractions only',
    fixed_denominator=str(core.SCALE),log_series_terms=core.TAYLOR_TERMS,
    euler_maclaurin_M=core.M,euler_maclaurin_R=core.RORDER,
    interval_source='../'+source.relative_to(B.parent).as_posix(),
    interval_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    root_endpoint_enclosures=2*len(records),
    critical_interval_enclosures=sum('previous_order_interval' in r for r in records),
    counts=counts,certificates=records,
    scope='Finite signs plus the written global multiplicity, endpoint and critical-point descent proofs. No scan completeness or floating-point sign is trusted.')
(B/'verification/higher-zero-certificates.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='certificates'},indent=2))
