"""Exact conditional matching witnesses via linear basis and block-ones repair.

No LP, row-pair closure, ray enumeration, or Pachner search is called.
Every test uses the FULL INITIAL mask away from its one conditioned tetrahedron.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
from math import gcd,lcm
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
sys.path.insert(0,str(ROOT/'fast'))
from pachner_descent_research.common import load_archive,source_hashes,digest
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.normal_sector import _assemble_sector_kernel


class CheckLimit(RuntimeError):
    pass


class Budget:
    def __init__(self,maximum):self.maximum=maximum;self.spent=0
    def check(self):
        if self.spent==self.maximum:raise CheckLimit('explicit check allowance exhausted')
        self.spent+=1


def rational(x):
    x=Fraction(x);return [x.numerator,x.denominator]


def save(path,data):
    path.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')


def construct(kernel,tested,check):
    support=kernel.support;target=support.index(tested)
    chosen=next((i for i,row in enumerate(kernel.basis) if row[target]),None)
    if chosen is None:return None
    vector=kernel.basis[chosen];scale=vector[target]
    q=[value/scale for value in vector]
    assert q[target]==1
    positions={pair:i for i,pair in enumerate(support)}
    shifts=[];n=len(kernel.prepared['tetrahedra'])
    for tet in range(n):
        check()
        if tet==tested[0]:continue
        indices=[positions[tet,kind] for kind in range(3)]
        shift=max(Fraction(0),-min(q[i] for i in indices))
        if shift:
            for i in indices:q[i]+=shift
            shifts.append([tet,rational(shift)])
    assert q[target]==1 and all(value>=0 for value in q)
    assert all(sum(a*b for a,b in zip(row,q))==0 for row in kernel.cycle_rows)
    triangles=[]
    for c in kernel.corner_class:
        check();triangles.append(sum(a*b for a,b in zip(kernel.potentials[c],q)))
    groups={}
    for corner,vertex in enumerate(kernel.prepared['vertex_roots']):groups.setdefault(vertex,[]).append(corner)
    triangle_shifts=[]
    for vertex,corners in sorted(groups.items()):
        check();shift=-min(triangles[i] for i in corners)
        for i in corners:triangles[i]+=shift
        triangle_shifts.append([vertex,rational(shift)])
    rows=[[Fraction(0)]*7 for _ in range(n)]
    for corner,value in enumerate(triangles):rows[corner//4][corner%4]=value
    for pair,value in zip(support,q):rows[pair[0]][4+pair[1]]=value
    denominator=1
    for row in rows:
        check()
        for value in row:denominator=lcm(denominator,value.denominator)
    integers=[[int(value*denominator) for value in row] for row in rows]
    divisor=gcd(*(value for row in integers for value in row))
    assert divisor>0
    integers=[[value//divisor for value in row] for row in integers]
    flat=[value for row in integers for value in row]
    assert all(type(value) is int and value>=0 for value in flat)
    assert integers[tested[0]][4+tested[1]]>0
    assert all(integers[tested[0]][4+kind]==0 for kind in range(3) if kind!=tested[1])
    for equation in kernel.prepared['matching']:
        check();assert sum(value*flat[column] for column,value in equation.items())==0
    return dict(coordinates=integers,construction=dict(basis_index=chosen,
        original_target=rational(scale),block_shifts=shifts,triangle_link_shifts=triangle_shifts,
        denominator=denominator,primitive_divisor=divisor))


def main():
    if not __debug__:raise RuntimeError('witness audit requires assertions enabled')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-checks',type=int,default=1000000)
    parser.add_argument('--output',type=Path,default=HERE/'probe.json')
    args=parser.parse_args()
    if args.max_checks<0:raise ValueError('max-checks must be nonnegative')
    pins=source_hashes();archive,raw=load_archive('fixed-u1-staged-audit','audit.json')
    assert archive['passed'] is True
    output=dict(schema='scratch-conditional-type-witnesses-v1',passed=False,
        source_sha256=pins,script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        staged_audit_sha256=sha256(raw).hexdigest(),max_checks_per_source=args.max_checks,
        maximum_total_construction_checks=6*args.max_checks,expected_tests=276,
        check_scope='Explicit callbacks across preparation, all linear kernels and witness construction. Independent replay excluded; no timing or exact bit-operation claim.',
        witness_scope='Formal nonnegative STANDARD matching vectors; other tetrahedra may have incompatible quadrilaterals. No Euler sign, extremality, normal-surface admissibility, or knot verdict claimed.',
        no_lp_rowpair_ray_or_pachner_discovery=True,no_global_deletions=True,
        no_timing_claim=True,records=[])
    save(args.output,output)
    for old in archive['records']:
        source=old['preprocessing']['u1']['result']['partial_chain']['triangulation']
        n=len(source['tetrahedra']);full=[(t,q) for t in range(n) for q in range(3)]
        budget=Budget(args.max_checks)
        record=dict(id=old['id'],input_pd=old['input_pd'],source=source,source_sha256=digest(source),
            full_initial_mask=[list(a) for a in full],queries=[],preparation=None,status='RUNNING',
            checks_used=0,all_types_have_matching_witnesses=False)
        output['records'].append(record);save(args.output,output)
        print(json.dumps(dict(start=old['id'],tetrahedra=n,tests=len(full))),flush=True)
        current=None
        try:
            prepared=_prepare(source,budget.check)
            assert prepared['vertices']==1
            record['preparation']=dict(status='RETURNED',checks_used=budget.spent,vertices=prepared['vertices'])
            for tested in full:
                mask=tuple(pair for pair in full if pair[0]!=tested[0] or pair==tested)
                current=dict(index=len(record['queries']),tested_type=list(tested),
                    conditional_mask=[list(a) for a in mask],start_checks=budget.spent,status='RUNNING')
                record['queries'].append(current);save(args.output,output)
                budget.check();kernel=_assemble_sector_kernel(source,prepared,mask,budget.check)
                current['kernel_statistics']=kernel.stats
                witness=construct(kernel,tested,budget.check)
                if witness is None:
                    current.update(status='ZERO_LINEAR_TARGET',end_checks=budget.spent,
                        scope='Producer linear diagnostic only; no independently certified infeasibility or deletion.')
                else:current.update(status='MATCHING_WITNESS',end_checks=budget.spent,**witness)
                record['checks_used']=budget.spent;save(args.output,output);current=None
            record['status']='COMPLETE_INITIAL_MASK_SCAN'
        except CheckLimit as error:
            if current is not None:current.update(status='CAPPED',end_checks=budget.spent,reason=str(error))
            if record['preparation'] is None:record['preparation']=dict(status='CAPPED',checks_used=budget.spent)
            record['status']='CAPPED'
        except BaseException as error:
            if current is not None:current.update(status='ERROR',end_checks=budget.spent,error_type=type(error).__name__,message=str(error))
            if record['preparation'] is None:record['preparation']=dict(status='ERROR',checks_used=budget.spent,error_type=type(error).__name__,message=str(error))
            record.update(status='ERROR',error_type=type(error).__name__,message=str(error))
            if not isinstance(error,Exception):
                record['checks_used']=budget.spent;save(args.output,output);raise
        record['checks_used']=budget.spent
        record['all_types_have_matching_witnesses']=(record['status']=='COMPLETE_INITIAL_MASK_SCAN' and
            len(record['queries'])==len(full) and all(q['status']=='MATCHING_WITNESS' for q in record['queries']))
        assert source_hashes()==pins,'source changed during witness audit'
        save(args.output,output)
        print(json.dumps(dict(done=record['id'],status=record['status'],queries=len(record['queries']),
            witnesses=sum(q['status']=='MATCHING_WITNESS' for q in record['queries']),
            zero_diagnostics=sum(q['status']=='ZERO_LINEAR_TARGET' for q in record['queries']),
            checks=budget.spent)),flush=True)
    assert source_hashes()==pins and len(output['records'])==6
    output['passed']=all(r['status'] in ('CAPPED','COMPLETE_INITIAL_MASK_SCAN') for r in output['records'])
    save(args.output,output);print('PASSED' if output['passed'] else 'RETAINED ERRORS',flush=True)


if __name__=='__main__':main()
