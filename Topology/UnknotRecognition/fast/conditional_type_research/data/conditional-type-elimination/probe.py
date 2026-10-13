"""Bounded sufficient conditional matching propagation; no LP/ray/move search.

Prepared before publication timing ends. Execute only after the parent release.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
sys.path.insert(0,str(ROOT/'fast'))
from pachner_descent_research.common import load_archive,source_hashes,digest
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.normal_sector import _assemble_sector_kernel
from fastunknot.sector_matching_support import matching_support


class CheckLimit(RuntimeError):
    pass


class Budget:
    def __init__(self,maximum):
        self.maximum=maximum;self.spent=0
    def check(self):
        if self.spent==self.maximum:raise CheckLimit('explicit check allowance exhausted')
        self.spent+=1


def save(path,data):
    path.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-checks',type=int,default=1000000)
    parser.add_argument('--output',type=Path,default=HERE/'probe.json')
    args=parser.parse_args()
    if args.max_checks<0:raise ValueError('max-checks must be nonnegative')
    pins=source_hashes()
    archive,raw=load_archive('fixed-u1-staged-audit','audit.json')
    assert archive['passed'] is True
    output=dict(schema='scratch-conditional-type-elimination-v1',passed=False,
        source_sha256=pins,script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        staged_audit_sha256=sha256(raw).hexdigest(),max_checks_per_source=args.max_checks,
        maximum_total_discovery_checks=6*args.max_checks,
        check_scope='Explicit callback invocations in source preparation, kernel assembly and sufficient matching closure/provenance; independent replay excluded. Not CPU time or a complete bit-operation count.',
        proof_scope='Raw matching_support provenance from a private arbitrary-mask kernel is research data. Its legacy compatible-only packet schema is not reinterpreted as an accepted native certificate.',
        no_lp_ray_or_pachner_discovery=True,no_timing_claim=True,records=[])
    save(args.output,output)
    for old in archive['records']:
        source=old['preprocessing']['u1']['result']['partial_chain']['triangulation']
        n=len(source['tetrahedra']);allowed=[(t,q) for t in range(n) for q in range(3)]
        budget=Budget(args.max_checks)
        record=dict(id=old['id'],input_pd=old['input_pd'],source=source,source_sha256=digest(source),
            initial_types=[list(a) for a in allowed],queries=[],preparation=None,
            status='RUNNING',checks_used=0,retained_types=[list(a) for a in allowed],deletions=[])
        output['records'].append(record);save(args.output,output)
        print(json.dumps(dict(start=old['id'],tetrahedra=n)),flush=True)
        current=None
        try:
            prepared=_prepare(source,budget.check)
            record['preparation']=dict(status='RETURNED',checks_used=budget.spent,vertices=prepared['vertices'])
            assert prepared['vertices']==1
            cursor=0
            while cursor<len(allowed):
                tested=allowed[cursor]
                mask=tuple(pair for pair in allowed if pair[0]!=tested[0] or pair==tested)
                current=dict(index=len(record['queries']),tested_type=list(tested),
                    retained_before=[list(a) for a in allowed],conditional_mask=[list(a) for a in mask],
                    start_checks=budget.spent,status='RUNNING')
                record['queries'].append(current);save(args.output,output)
                budget.check()
                kernel=_assemble_sector_kernel(source,prepared,mask,budget.check)
                current['kernel_statistics']=kernel.stats
                keep,proof=matching_support(kernel,budget.check)
                target=mask.index(tested)
                removed=target not in keep
                current.update(status='RETURNED',end_checks=budget.spent,
                    retained_indices=keep,raw_matching_provenance=proof,
                    conditional_forced_types=[list(mask[i]) for i in range(len(mask)) if i not in keep],
                    removed_type=list(tested) if removed else None)
                if removed:
                    # Other conditionally forced types are never deleted here.
                    allowed.remove(tested);record['deletions'].append(list(tested));cursor=0
                else:cursor+=1
                record.update(retained_types=[list(a) for a in allowed],checks_used=budget.spent)
                save(args.output,output);current=None
            record['status']='SUFFICIENT_CLOSURE_FIXED_POINT'
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
        record.update(checks_used=budget.spent,retained_types=[list(a) for a in allowed])
        assert source_hashes()==pins,'source changed during conditional probe'
        save(args.output,output)
        print(json.dumps(dict(done=record['id'],status=record['status'],queries=len(record['queries']),
            deletions=len(record['deletions']),remaining_types=len(allowed),checks=budget.spent)),flush=True)
    assert source_hashes()==pins and len(output['records'])==6
    output['passed']=all(r['status'] in ('CAPPED','SUFFICIENT_CLOSURE_FIXED_POINT') for r in output['records'])
    save(args.output,output)
    print('PASSED' if output['passed'] else 'RETAINED ERRORS',flush=True)


if __name__=='__main__':main()
