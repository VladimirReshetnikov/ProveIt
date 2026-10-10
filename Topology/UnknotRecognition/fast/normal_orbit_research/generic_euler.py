"""Frozen grouped-Euler baseline and all-dimensional Q-screen evidence."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import time
from types import ModuleType
from itertools import combinations,product
import random

from fastunknot import Diagram,recognize
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.integer_codec import json_safe
from normal_orbit_research import seeds
from normal_orbit_research.sector_windows import corpus
from normal_orbit_research.fixtures import regina_triangulation,regina_surface
from fastunknot.normal_sector import sector_rays,discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_exhaustion,verify_sector_witness
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.sector_sparse import PreparedSectorSource
from fastunknot.sector_euler import SourceEuler
from fastunknot.sector_residual import _full_quad_columns
from fastunknot.sector_window_basis import projected_corner_forms
from planar_sector_research.fixtures import fresh_standard

ROOT=Path(__file__).resolve().parents[1]
PRIOR=ROOT.parent/'synthesis/data/euler-aggregate-audit.json'
BASELINE='e0a2aa2eed1c756adf2b2eab04af0432150c78c4'
BANK=ROOT.parent/'reports/57/results/discovery_corpus.json'


def baseline():
    hashes={};modules={}
    for name in ('normal_sector','sector_euler','sector_residual','normal_seed','recognize'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
        hashes[name]=sha256(code).hexdigest()
        if name=='sector_residual':
            code=code.replace(b'from .sector_euler import',b'from ._generic_euler_baseline_sector_euler import')
        if name=='normal_seed':
            code=code.replace(b'from .sector_residual import search_sector_window',
                b'from ._generic_euler_baseline_sector_residual import search_sector_window')
        if name=='recognize':
            code=code.replace(b'from .normal_seed import normal_seed_decide',
                b'from ._generic_euler_baseline_normal_seed import normal_seed_decide')
        module=ModuleType('fastunknot._generic_euler_baseline_'+name);module.__package__='fastunknot'
        sys.modules[module.__name__]=module;exec(compile(code,BASELINE+':'+path,'exec'),module.__dict__)
        modules[name]=module
    return modules,hashes


def pins():
    result=seeds.sources()
    for path in (PRIOR,BANK):result[str(path.relative_to(ROOT.parent))]=sha256(path.read_bytes()).hexdigest()
    return result


def selected_supports(record):
    t=len(record['triangulation']['tetrahedra']);supports={()}
    for field in ('standard_vertices','quad_vertices'):
        supports.update(tuple((i,q)for i,row in enumerate(s['coordinates'])for q in range(3)if row[4+q])
                        for s in record[field])
    if t<=3:
        supports.update(tuple((i,q)for i,q in enumerate(types)if q>=0)
                        for types in product((-1,0,1,2),repeat=t))
    else:
        for size in (1,2):
            for indices in combinations(range(t),size):
                supports.update(tuple(zip(indices,types))for types in product(range(3),repeat=size))
        rng=random.Random('sector-envelope-v1:'+record['id'])
        supports.update(tuple((i,rng.randrange(3))for i in range(t))for _ in range(64))
    return sorted(supports)


def contained(rows,support):
    return any(row[4+q]for row in rows for q in range(3))and all(
        not row[4+q]or (i,q)in support for i,row in enumerate(rows)for q in range(3))


def sector_audit(old,fresh):
    records=[];fresh_cache={};negative_proofs=[]
    for item in json.loads(BANK.read_text())['records']:
        raw=item['triangulation'];source=PreparedSectorSource(raw);euler=potentials=None
        for support in selected_supports(item):
            kernel=source.build(support)
            if len(kernel.basis)<=3:continue
            if euler is None:
                _,_,potentials=_full_quad_columns(source.prepared,lambda:None,True)
                euler=SourceEuler(source.prepared,potentials,lambda:None)
            forms=projected_corner_forms(support,kernel.basis,potentials,lambda:None)
            envelope=euler.aggregate(support,kernel.basis,forms,lambda:None)
            stats=dict(euler_screens=0,euler_corners=0,euler_pruned_sectors=0)
            excluded=euler.excludes_positive(support,kernel.basis,forms,lambda:None,stats)
            qstats={};qrays=list(sector_rays(kernel,phase='quadrilateral',stats=qstats))
            old_qrays=list(old['normal_sector'].sector_rays(kernel,phase='quadrilateral'))
            assert qrays==old_qrays
            qchi=[]
            free=[next(i for i in range(len(support)-1,-1,-1)if row[i])for row in kernel.basis]
            for rows in qrays:
                chi=_coordinates(source.prepared,rows,lambda:None)['euler_characteristic'];qchi.append(chi)
                for scale in (1,2**90+1):
                    z=tuple(scale*rows[support[i][0]][4+support[i][1]]for i in free)
                    assert euler.canonical_value(support,kernel.basis,forms,z,lambda:None)==scale*chi
                    assert euler.aggregated_value(envelope,z,lambda:None)==scale*chi
            std=[s['coordinates']for s in item['standard_vertices']if contained(s['coordinates'],support)]
            schi=[_coordinates(source.prepared,rows,lambda:None)['euler_characteristic']for rows in std]
            assert excluded==(not any(c>0 for c in qchi))==(not any(c>0 for c in schi))
            record=dict(id=item['id'],allowed_types=support,matching_nullity=len(kernel.basis),
                q_corners=len(qrays),standard_rays=len(std),q_euler=qchi,standard_euler=schi,
                excluded=excluded,screen_stats=stats,q_enumeration_stats=qstats)
            if excluded:
                assert stats['euler_corners']==len(qrays)
                answer=discover_in_sector(raw,support,phase='standard')
                assert answer['status']=='NO_POSITIVE_EULER'and answer['stats']['q_screen_only']
                assert verify_sector_exhaustion(raw,answer['certificate'])
                record['discovery']=answer;negative_proofs.append(dict(triangulation=raw,certificate=answer['certificate']))
                if fresh:
                    if item['id']not in fresh_cache:fresh_cache[item['id']]=fresh_standard(raw)
                    actual=[rows for rows in fresh_cache[item['id']]if contained(rows,support)]
                    assert sorted(seeds.encode(v)for v in actual)==sorted(seeds.encode(v)for v in std)
                    record['fresh_regina_standard_rays']=len(actual)
            records.append(record)
        print(item['id'],sum(r['id']==item['id']for r in records),flush=True)
    assert len(records)==188 and sum(r['excluded']for r in records)==12
    return dict(sector_cases=records,negative_proofs=negative_proofs,
        fresh_regina_sources=len(fresh_cache),source_sectors=188,excluded_sectors=12,
        matching_nullities=sorted({r['matching_nullity']for r in records}))


def sector_benchmark(old,rounds):
    audit_data=json.loads((ROOT.parent/'synthesis/data/generic-euler-sector-audit.json').read_text())
    bank={r['id']:r for r in json.loads(BANK.read_text())['records']}
    chosen=[]
    for identifier in ('fibonacci_lst_09','fibonacci_lst_10','lst_1_8','solid_torus_sum_s2xs1'):
        chosen.append(next(r for r in audit_data['sector_cases']if r['id']==identifier and r['excluded']))
    for d in (4,5):chosen.append(next(r for r in audit_data['sector_cases']if r['matching_nullity']==d and not r['excluded']))
    cases=[(r['id']+'-d'+str(r['matching_nullity']),r)for r in chosen]
    def run(case,use_old):
        raw=bank[case['id']]['triangulation']
        call=old['normal_sector'].discover_in_sector if use_old else discover_in_sector
        answer=call(raw,case['allowed_types'],phase='standard')
        assert answer['status']!='INCONCLUSIVE'
        if answer['status']=='DISC_FOUND':assert verify_sector_witness(raw,answer['certificate'])
        else:assert verify_sector_exhaustion(raw,answer['certificate'])
        if case['excluded']:assert answer['status']=='NO_POSITIVE_EULER'
        wire=seeds.encode(answer)
        return dict(completed=True,status=answer['status'],bases_attempted=answer['stats']['bases_attempted'],
            ray_records=len(answer['certificate'].get('rays',[])),result_bytes=len(wire),
            certificate_sha256=sha256(seeds.encode(answer['certificate'])).hexdigest(),stats=answer['stats'])
    result=seeds.rounds(cases,run,rounds)
    for case in result['cases']:
        for sample in case['samples']+case['warmups']:
            assert len({m['status']for m in sample['measurements'].values()})==1
    result['scope']='Complete supplied-sector discovery, independent certificate replay and serialized output; excludes knot-diagram recognition.'
    return result


def audit(old,fresh):
    prior=json.loads(PRIOR.read_text());records=[];proofs=[];regina_checks=0
    for source,previous in zip(corpus(),prior['source_cases']):
        assert seeds.encode(source)==seeds.encode(previous['source'])
        d=Diagram.from_pd(source['pd'])
        # These checks establish exact incumbent disabled behavior afresh;
        # the bounded radius-two incumbent results are retained release data.
        before=old['normal_seed'].normal_seed_decide(d)
        disabled=normal_seed_decide(d,sector_radius=0);assert before==disabled
        after=normal_seed_decide(d,sector_radius=2)
        if after['status']=='UNKNOT':
            assert source['expected']=='UNKNOT'and verify_normal_seed_certificate(d,after['certificate'])
            proofs.append(after['certificate'])
            if fresh and after['certificate']['schema']=='diagram-normal-disc-v1':
                p=after['certificate'];s=regina_surface(regina_triangulation(p['triangulation']),p['coordinates'])
                assert s.isCompressingDisc(True);regina_checks+=1
        r=dict(source=source,disabled_status=before['status'],old_radius_two_status=previous['new_radius_two_status'],
            new_radius_two_status=after['status'],old_work=previous['new_work'],new_work=after['work'],
            old_window_stats=previous['new_window_stats'],new_window_stats=after['stats'].get('sector_search'),
            reason=after.get('reason'),certificate=after.get('certificate'))
        records.append(r)
        print(source['name'],r['old_radius_two_status'],r['new_radius_two_status'],after['work'],flush=True)
    return dict(source_cases=records,legacy_exact_comparisons=len(records),source_proofs=proofs,
        old_radius_two_positives=prior['new_radius_two_positives'],new_radius_two_positives=len(proofs),
        fresh_regina_window_discs=regina_checks,incumbent_radius_two_evidence=str(PRIOR.relative_to(ROOT.parent)))


def benchmark(old,rounds):
    sources={s['name']:s for s in corpus()}
    sources['figure-eight']=dict(name='figure-eight',pd=Diagram.from_braid(3,[1,-2,1,-2]).pd,expected='KNOTTED')
    names=('empty-circle','optimized-positive','genus-one-miss','trefoil','figure-eight')
    cases=[('seed/'+name,('seed',sources[name]))for name in names]
    cases += [('recognition/'+name,('recognition',sources[name]))for name in names]
    def run(case,use_old):
        kind,source=case;d=Diagram.from_pd(source['pd'])
        if kind=='seed':
            call=old['normal_seed'].normal_seed_decide if use_old else normal_seed_decide
            answer=call(d,sector_radius=2,max_work=None)
            if answer['status']=='UNKNOT':assert verify_normal_seed_certificate(d,answer['certificate'])
            assert 'exhausted'not in answer.get('reason','')
            wire=seeds.encode(answer)
            return dict(completed=True,status=answer['status'],work=answer['work'],
                result_sha256=sha256(wire).hexdigest(),result_bytes=len(wire),
                certificate_sha256=sha256(seeds.encode(answer.get('certificate'))).hexdigest(),
                window_stats=answer['stats'].get('sector_search'))
        call=old['recognize'].recognize if use_old else recognize
        answer=call(d,**dict(seeds.FORCED,normal_seed_sector_radius=2,seconds=30))
        assert answer.status==source['expected']
        wire=seeds.encode(answer.evidence)
        return dict(completed=True,status=answer.status,method=answer.method,
            evidence_sha256=sha256(wire).hexdigest(),evidence_bytes=len(wire))
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        values=[v for s in row['samples']+row['warmups']for v in s['measurements'].values()]
        assert all(v['completed']and v['status']==values[0]['status']for v in values)
        if row['name'].startswith('seed/'):
            assert all(v['certificate_sha256']==values[0]['certificate_sha256']for v in values)
            for arm in ('old','new'):
                values=[{k:v for k,v in s['measurements'][a].items()if k!='seconds'}
                    for s in row['samples']+row['warmups']for a in (arm,arm+'_AA')]
                assert all(v==values[0]for v in values)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark','sector-audit','sector-benchmark'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--fresh-regina',action='store_true')
    parser.add_argument('--rounds',type=int,default=5);args=parser.parse_args()
    if args.rounds<1:parser.error('--rounds must be positive')
    old,hashes=baseline();before=pins();start=time.perf_counter()
    if args.mode=='audit':result=audit(old,args.fresh_regina)
    elif args.mode=='benchmark':result=benchmark(old,args.rounds)
    elif args.mode=='sector-audit':result=sector_audit(old,args.fresh_regina)
    else:result=sector_benchmark(old,args.rounds)
    assert before==pins();result.update(native_source_sha256=before,native_baseline=BASELINE,
        native_baseline_source_sha256=hashes,native_seconds=time.perf_counter()-start,
        native_runtime_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['native_seconds'],flush=True)


if __name__=='__main__':main()
