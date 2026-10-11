"""Actual source-row pair reductions and complete native sector query costs."""
import argparse
from contextlib import ExitStack
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import time
from types import ModuleType
from unittest.mock import patch

from fastunknot.normal_sector import build_sector_kernel,discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_exhaustion,_matching_support_indices,_digest
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.sector_matching_support import matching_support
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation

ROOT=Path(__file__).resolve().parents[1];DATA=ROOT.parent/'synthesis/data'
BASE='338a3a3877c337f981072061c16bc8ee1d87155d'

def baseline():
    path='Topology/UnknotRecognition/fast/fastunknot/sector_matching_support.py'
    raw=subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT)
    module=ModuleType('fastunknot._frozen_matching_pairs');module.__package__='fastunknot'
    exec(compile(raw,BASE+':'+path,'exec'),module.__dict__)
    return module,sha256(raw).hexdigest()

def inputs():
    bank={r['id']:r for r in json.loads((ROOT.parent/'reports/57/results/discovery_corpus.json').read_text())['records']}
    pilot=json.loads((DATA/'matching-pair-pilot.json').read_text())
    return bank,pilot

def cases():
    bank,pilot=inputs()
    targets=[h for h in pilot['hits']if h['raw_nullity']>3]
    result=[(f'figure-eight-pair-{i}',dict(raw=bank[h['id']]['triangulation'],support=h['support']))for i,h in enumerate(targets)]
    result.append(('existing-single-row',dict(raw=bank['cap_3_5_2']['triangulation'],
        support=[[0,0],[1,1],[2,2],[3,0],[4,1]])))
    result.append(('no-pair-control',dict(raw=bank['finite_figureEight_interior']['triangulation'],
        support=[[i,0]for i in range(13)])))
    return result

def query(case,old):
    with patch('fastunknot.sector_matching_support.matching_support',old.matching_support if old else matching_support):
        result=discover_in_sector(case['raw'],case['support'],phase='standard')
    assert result['status']not in ('INCONCLUSIVE','DISC_FOUND'),result['status']
    assert verify_sector_exhaustion(case['raw'],result['certificate'])
    wire=seeds.encode(result)
    return dict(completed=True,status=result['status'],stats=result['stats'],bytes=len(wire),
        certificate_sha256=sha256(seeds.encode(result['certificate'])).hexdigest())

def audit(old):
    bank,pilot=inputs();records=[];proofs=[]
    for h in pilot['hits']:
        raw=bank[h['id']]['triangulation'];kernel=build_sector_kernel(raw,h['support'])
        old_keep,_=old.matching_support(kernel,lambda:None)
        keep,proof=matching_support(kernel,lambda:None)
        assert sorted(set(range(len(h['support'])))-set(keep))==h['new_forced']
        assert sorted(set(range(len(h['support'])))-set(old_keep))==h['old_forced']
        disabled=('fastunknot.sector_matching_support._source_constraints',
            'fastunknot.sector_matching_support._pair_step','fastunknot.normal_sector.build_sector_kernel')
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer')))
            assert _matching_support_indices(_prepare(raw,lambda:None),list(kernel.support),proof,_digest(raw),lambda:None)==keep
        records.append(dict(id=h['id'],support=h['support'],old_forced=h['old_forced'],new_forced=h['new_forced'],
            retained_nullity=len(build_sector_kernel(raw,[h['support'][i]for i in keep]).basis),proof_steps=len(proof['steps'])))
        proofs.append(dict(triangulation=raw,certificate=proof))
    prior=json.loads((DATA/'matching-support-audit.json').read_text());unchanged=0
    for r in prior['source_cases']:
        kernel=build_sector_kernel(bank[r['id']]['triangulation'],r['allowed_types'])
        keep,_=matching_support(kernel,lambda:None)
        assert keep==r['retained_indices'];unchanged+=1
    complete=[];fresh=[]
    import regina
    for name,case in cases():
        before=query(case,old);after=query(case,None)
        assert before['status']==after['status']
        result=discover_in_sector(case['raw'],case['support'],phase='standard')
        proof=result['certificate'];assert verify_sector_exhaustion(case['raw'],proof)
        legacy=deepcopy(proof);legacy.pop('matching_support_certificate',None)
        assert verify_sector_exhaustion(case['raw'],legacy)
        complete.append(dict(name=name,old=before,new=after,certificate=proof,triangulation=case['raw']))
        if name.startswith('figure-eight-pair'):
            tri=regina_triangulation(case['raw']);surfaces=regina.NormalSurfaces(tri,regina.NS_STANDARD)
            expected=[]
            allowed=set(tuple(x)for x in case['support'])
            for surface in surfaces:
                q=[int(str(surface.quads(t,j)))for t,j in case['support']]
                if not any(q):continue
                if any(int(str(surface.quads(t,j)))and (t,j)not in allowed
                    for t in range(tri.size())for j in range(3)):continue
                assert not surface.isCompressingDisc(True)
                expected.append(tuple(q))
            assert set(expected)=={tuple(row['quadrilaterals'])for row in proof['rays']}
            fresh.append(dict(name=name,rays=len(expected),no_essential_disc=True))
        print(name,before['stats']['matching_nullity'],after['stats']['matching_nullity'],
              before['stats']['bases_attempted'],after['stats']['bases_attempted'],flush=True)
    return dict(source_reductions=records,source_implication_proofs=proofs,
        previous_source_cases_unchanged=unchanged,complete_queries=complete,fresh_regina_sources=fresh)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--rounds',type=int,default=5)
    args=parser.parse_args();old,digest=baseline();before=seeds.sources();start=time.perf_counter()
    result=audit(old)if args.mode=='audit'else seeds.rounds(cases(),lambda case,use_old:query(case,old if use_old else None),args.rounds)
    assert before==seeds.sources()
    result.update(native_source_sha256=before,baseline=BASE,baseline_module_sha256=digest,
        native_runtime_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=ROOT).strip(),
        native_seconds=time.perf_counter()-start,
        pilot_sha256=sha256((DATA/'matching-pair-pilot.json').read_bytes()).hexdigest(),
        corpus_sha256=sha256((ROOT.parent/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest())
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k in ('native_runtime_revision','native_seconds','measured_calls','completed_calls','warmup_calls')}))

if __name__=='__main__':main()
