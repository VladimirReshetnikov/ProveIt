"""Complete Q support, feasible-span discovery and independent replay evidence."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import time
from types import ModuleType

from fastunknot.normal_sector import discover_in_sector,sector_rays
from fastunknot.normal_sector_verify import verify_sector_exhaustion,verify_sector_witness
from fastunknot.sector_sparse import PreparedSectorSource
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.integer_codec import json_safe
from normal_orbit_research import seeds
from planar_sector_research.fixtures import fresh_standard

ROOT=Path(__file__).resolve().parents[1]
BASELINE='c21e78bcd6a9df68a93c3b659c2db051c4266532'
BANK=ROOT.parent/'reports/57/results/discovery_corpus.json'
PRIOR=ROOT.parent/'synthesis/data/generic-euler-sector-audit.json'


def baseline():
    modules={};hashes={}
    for name in ('normal_sector','normal_sector_verify'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
        hashes[name]=sha256(code).hexdigest()
        module=ModuleType('fastunknot._feasible_span_baseline_'+name);module.__package__='fastunknot'
        sys.modules[module.__name__]=module;exec(compile(code,BASELINE+':'+path,'exec'),module.__dict__)
        modules[name]=module
    return modules,hashes


def pins():
    result=seeds.sources()
    for path in (BANK,PRIOR):result[str(path.relative_to(ROOT.parent))]=sha256(path.read_bytes()).hexdigest()
    return result


def contains(rows,support):
    return any(row[4+q]for row in rows for q in range(3))and all(
        not row[4+q]or (i,q)in support for i,row in enumerate(rows)for q in range(3))


def verify(raw,answer,verifier):
    assert answer['status']!='INCONCLUSIVE'
    if answer['status']=='DISC_FOUND':assert verifier.verify_sector_witness(raw,answer['certificate'])
    else:assert verifier.verify_sector_exhaustion(raw,answer['certificate'])


def audit(old,fresh):
    bank={r['id']:r for r in json.loads(BANK.read_text())['records']}
    prior=json.loads(PRIOR.read_text())['sector_cases'];records=[];proofs=[];fresh_cache={}
    class Current:
        verify_sector_exhaustion=staticmethod(verify_sector_exhaustion)
        verify_sector_witness=staticmethod(verify_sector_witness)
    for c in prior:
        item=bank[c['id']];raw=item['triangulation'];source=PreparedSectorSource(raw)
        kernel=source.build(c['allowed_types']);qrows=list(sector_rays(kernel,phase='quadrilateral'))
        retained=[i for i,(t,q)in enumerate(kernel.support)if any(rows[t][4+q]for rows in qrows)]
        reduced=source.build([kernel.support[i]for i in retained])
        all_original=[s['coordinates']for s in item['standard_vertices']if contains(s['coordinates'],kernel.support)]
        actual=list(sector_rays(reduced));assert sorted(seeds.encode(v)for v in actual)==sorted(seeds.encode(v)for v in all_original)
        before=old['normal_sector'].discover_in_sector(raw,kernel.support,phase='standard')
        after=discover_in_sector(raw,kernel.support,phase='standard')
        assert before['status']==after['status'];verify(raw,after,Current)
        r=dict(id=c['id'],allowed_types=kernel.support,retained_indices=retained,raw_nullity=len(kernel.basis),
            feasible_nullity=len(reduced.basis),forced_zero_types=len(kernel.support)-len(retained),
            standard_rays=len(actual),old_status=before['status'],new_status=after['status'],
            old_stats=before['stats'],new_stats=after['stats'],certificate=after['certificate'])
        if r['forced_zero_types']:
            assert all(not rows[kernel.support[i][0]][4+kernel.support[i][1]]
                       for rows in all_original for i in range(len(kernel.support))if i not in retained)
            if fresh:
                if c['id']not in fresh_cache:fresh_cache[c['id']]=fresh_standard(raw)
                literal=[rows for rows in fresh_cache[c['id']]if contains(rows,kernel.support)]
                assert sorted(seeds.encode(v)for v in literal)==sorted(seeds.encode(v)for v in actual)
                r['fresh_regina_standard_rays']=len(literal)
        if 'q_support_certificate'in after['certificate']:
            assert after['certificate']['allowed_types']==[list(x)for x in kernel.support]
            proofs.append(dict(triangulation=raw,certificate=after['certificate']))
            # The unchanged statement can also be checked by the frozen
            # original full-source verifier. Check one for each effective
            # dimension rather than repeating its expensive reconstruction.
            if not any(x.get('legacy_dimension')==len(reduced.basis)for x in records):
                legacy=deepcopy(after['certificate']);legacy.pop('q_support_certificate')
                assert old['normal_sector_verify'].verify_sector_exhaustion(raw,legacy)
                r['legacy_dimension']=len(reduced.basis)
        records.append(r)
        print(c['id'],c['matching_nullity'],len(reduced.basis),after['status'],flush=True)
    counts=Counter((r['raw_nullity'],r['feasible_nullity'])for r in records if r['forced_zero_types'])
    assert len(records)==188 and sum(r['forced_zero_types']>0 for r in records)==65
    assert counts=={(4,3):22,(4,4):41,(5,4):2}
    return dict(source_cases=records,reduced_proofs=proofs,source_sectors=len(records),forced_zero_sectors=65,
        dimension_transitions={f'{a}->{b}':n for (a,b),n in sorted(counts.items())},
        fresh_regina_sources=len(fresh_cache),unchanged_statuses=len(records))


def benchmark(old,rounds):
    bank={r['id']:r for r in json.loads(BANK.read_text())['records']}
    audit_data=json.loads((ROOT.parent/'synthesis/data/feasible-span-audit.json').read_text())['source_cases']
    selected=[]
    for a,b in ((4,3),(4,4),(5,4)):
        selected.append(next(r for r in audit_data if r['raw_nullity']==a and r['feasible_nullity']==b
                             and 'q_support_certificate'in r['certificate']))
    # Full-support positive and nonpositive Q controls retain their old path.
    selected.append(next(r for r in audit_data if r['id']=='cap_1_2_3'and not r['forced_zero_types']))
    selected.append(next(r for r in audit_data if r['id']=='fibonacci_lst_09'and r['new_status']=='NO_POSITIVE_EULER'))
    cases=[(r['id']+f"-{r['raw_nullity']}-to-{r['feasible_nullity']}",r)for r in selected]
    class Current:
        verify_sector_exhaustion=staticmethod(verify_sector_exhaustion)
        verify_sector_witness=staticmethod(verify_sector_witness)
    def run(case,use_old):
        raw=bank[case['id']]['triangulation']
        call=old['normal_sector'].discover_in_sector if use_old else discover_in_sector
        answer=call(raw,case['allowed_types'],phase='standard')
        verifier=old['normal_sector_verify']if use_old else Current
        verify(raw,answer,verifier);assert answer['status']==case['new_status']
        wire=seeds.encode(answer)
        return dict(completed=True,status=answer['status'],stats=answer['stats'],result_bytes=len(wire),
            certificate_sha256=sha256(seeds.encode(answer['certificate'])).hexdigest(),
            proof_ray_records=len(answer['certificate'].get('rays',[])))
    result=seeds.rounds(cases,run,rounds)
    for record in result['cases']:
        for sample in record['samples']+record['warmups']:
            assert len({m['status']for m in sample['measurements'].values()})==1
    result['scope']='Complete supplied-source standard discovery, respective independent replay and serialized output; not diagram recognition.'
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--fresh-regina',action='store_true');parser.add_argument('--rounds',type=int,default=5)
    args=parser.parse_args()
    if args.rounds<1:parser.error('--rounds must be positive')
    old,hashes=baseline();before=pins();started=time.perf_counter()
    result=audit(old,args.fresh_regina)if args.mode=='audit'else benchmark(old,args.rounds)
    assert before==pins()
    result.update(native_source_sha256=before,native_baseline=BASELINE,native_baseline_source_sha256=hashes,
        native_runtime_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
        native_seconds=time.perf_counter()-started)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['native_seconds'],flush=True)


if __name__=='__main__':main()
