"""Frozen two-module baseline, complete adaptive discovery and shared kernels."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import time
from types import ModuleType
from unittest.mock import patch

from fastunknot import normal_sector as current
from fastunknot.integer_codec import json_safe
from fastunknot.normal_sector_verify import verify_sector_exhaustion,verify_sector_witness
from fastunknot.sector_planar import sector_planar_rays,sector_planar_discovery_rays
from normal_orbit_research import seeds
from planar_sector_research import audit as package_audit
from planar_sector_research.fixtures import double_capped_fibonacci,capped_fibonacci,vector_key,ray_digest

ROOT=Path(__file__).resolve().parents[1]
CORPUS=ROOT.parent/'reports/57/results/discovery_corpus.json'
BASELINE='89d3e8bee3caf7bb48f31a40cc7dd0f2191571d5'


def baseline():
    modules={};hashes={}
    for name in ('sector_planar','normal_sector'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
        hashes[name]=sha256(code).hexdigest()
        # Redirect only the incumbent's lazy import to its frozen planner.
        # All other imported dependencies are unchanged in this release.
        if name=='normal_sector':
            code=code.replace(b'from .sector_planar import sector_planar_rays',
                              b'from ._adaptive_baseline_sector_planar import sector_planar_rays')
        m=ModuleType('fastunknot._adaptive_baseline_'+name)
        m.__package__='fastunknot';sys.modules[m.__name__]=m
        exec(compile(code,BASELINE+':'+path,'exec'),m.__dict__)
        modules[name]=m
    return modules,hashes


def pins():
    result=seeds.sources()
    result[str(CORPUS.relative_to(ROOT.parent))]=sha256(CORPUS.read_bytes()).hexdigest()
    return result


def corpus_source(name):
    return next(r['triangulation']for r in json.loads(CORPUS.read_text())['records']if r['id']==name)


def cap_boundary(raw):
    raw=json.loads(json.dumps(raw))
    t,f=next((t,f)for t,row in enumerate(raw['tetrahedra'])for f,v in enumerate(row)if v is None)
    new=len(raw['tetrahedra']);raw['tetrahedra'][t][f]={'tetrahedron':new,'permutation':[0,1,2,3]}
    row=[None]*4;row[f]={'tetrahedron':t,'permutation':[0,1,2,3]};raw['tetrahedra'].append(row)
    return raw


def audit(old,fresh):
    counts=dict(exact_canonical_sequences=0,adaptive_complete_sets=0)
    pending=[]
    def checked(kernel,*,stats=None,**options):
        old_stats=dict(stats or {})
        before=list(old['sector_planar'].sector_planar_rays(kernel,stats=old_stats,**options))
        after=list(sector_planar_rays(kernel,stats=stats,**options))
        assert before==after and (stats is None or old_stats==stats)
        adaptive_stats={};adaptive=list(sector_planar_discovery_rays(kernel,stats=adaptive_stats))
        assert len(adaptive)==len(after)
        assert {vector_key(r)for r in adaptive}=={vector_key(r)for r in after}
        assert adaptive_stats['bases_attempted']==len(after)
        counts['exact_canonical_sequences']+=1;counts['adaptive_complete_sets']+=1
        if len(kernel.basis)==3:pending.append((kernel.triangulation,kernel.support))
        yield from after
    with patch.object(package_audit,'sector_planar_rays',checked):
        result,certificates=package_audit.run(CORPUS,fresh_regina=fresh)
    sources={current._source_hash(r['triangulation']):r['id']for r in json.loads(CORPUS.read_text())['records']}
    records=[];early=refined=negatives=0
    for raw,support in pending:
        before=old['normal_sector'].discover_in_sector(raw,support,phase='standard')
        after=current.discover_in_sector(raw,support,phase='standard')
        assert before['status']==after['status']!='INCONCLUSIVE'
        positive=after['status']=='DISC_FOUND'
        verifier=verify_sector_witness if positive else verify_sector_exhaustion
        assert verifier(raw,after['certificate'])
        if positive:
            assert verify_sector_witness(raw,before['certificate'])
        else:
            first=before['certificate'];second=after['certificate']
            assert {seeds.encode(r)for r in first['rays']}=={seeds.encode(r)for r in second['rays']}
            negatives+=1
        early+=int(positive and after['stats']['overlay_refinements']==0)
        refined+=after['stats']['overlay_refinements']
        records.append(dict(source_id=sources[current._source_hash(raw)],allowed_types=support,
            old_status=before['status'],new_status=after['status'],old_stats=before['stats'],new_stats=after['stats'],
            certificate=after['certificate'],independent_replay=True,
            old_positive_certificate=before['certificate']if positive else None))
    result['adaptive_counts']=dict(counts,discovery_queries=len(records),early_positive_queries=early,
        refined_discovery_queries=refined,complete_negative_replays=negatives)
    result['discovery_records']=records
    result['discovery_sources']={r['id']:r['triangulation']for r in json.loads(CORPUS.read_text())['records']}
    return result,certificates


def benchmark(old,rounds):
    cases=[]
    for n in (1,4,8,16,32):
        f=double_capped_fibonacci(n);cases.append((f'discovery/double-cap-{n}',('discovery',f)))
    cases.append(('discovery/complete-negative',('discovery',dict(triangulation=corpus_source('fibonacci_lst_06'),
        allowed_types=[(0,0),(1,2),(2,1),(3,0),(4,2),(5,1)]))))
    cases.append(('discovery/empty-sector',('discovery',dict(triangulation=double_capped_fibonacci(1)['triangulation'],allowed_types=[]))))
    for n in (4,8):cases.append((f'control/single-cap-{n}',('discovery',capped_fibonacci(n))))
    for n in (1,8,16):cases.append((f'enumeration/double-cap-{n}',('enumeration',double_capped_fibonacci(n))))
    for name in ('finite_trefoil_interior','finite_figureEight_interior'):
        raw=cap_boundary(corpus_source(name))
        cases.append(('sparse/'+name,('sparse',dict(triangulation=raw))))
    def run(case,use_old):
        kind,source=case;module=old['normal_sector']if use_old else current
        if kind=='sparse':
            answer=module.sparse_disc_search(source['triangulation'],max_active=1)
            assert answer['status']=='NO_VERTEX_DISC_UP_TO_SUPPORT'
            wire=seeds.encode(answer)
            return dict(completed=True,output_sha256=sha256(wire).hexdigest(),output_bytes=len(wire),
                status=answer['status'],sectors_visited=answer['sectors_visited'])
        raw,allowed=source['triangulation'],source['allowed_types']
        if kind=='enumeration':
            rays,stats=module.enumerate_sector(raw,allowed)
            wire=seeds.encode(sorted(tuple(x for row in r for x in row)for r in rays))
            return dict(completed=True,output_sha256=ray_digest(rays),output_bytes=len(wire),rays=len(rays),
                bases=stats['bases_attempted'],method=stats['method'])
        answer=module.discover_in_sector(raw,allowed,phase='standard')
        assert answer['status']!='INCONCLUSIVE'
        verify=verify_sector_witness if answer['status']=='DISC_FOUND'else verify_sector_exhaustion
        assert verify(raw,answer['certificate'])
        wire=seeds.encode(answer['certificate'])
        return dict(completed=True,output_sha256=sha256(answer['status'].encode()).hexdigest(),
            certificate_sha256=sha256(wire).hexdigest(),certificate_bytes=len(wire),
            status=answer['status'],bases=answer['stats']['bases_attempted'],method=answer['stats']['method'],
            overlay_refinements=answer['stats'].get('overlay_refinements'))
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        values=[v for s in row['samples']+row['warmups']for v in s['measurements'].values()]
        assert all(v['completed']and v['output_sha256']==values[0]['output_sha256']for v in values)
        for arm in ('old','new'):
            values=[{k:v for k,v in s['measurements'][a].items()if k!='seconds'}
                for s in row['samples']+row['warmups']for a in (arm,arm+'_AA')]
            assert all(v==values[0]for v in values)
    return result,None


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--fresh-regina',action='store_true');parser.add_argument('--rounds',type=int,default=5)
    args=parser.parse_args()
    if args.rounds<1:parser.error('--rounds must be positive')
    old,hashes=baseline();before=pins();started=time.perf_counter()
    result,certificates=audit(old,args.fresh_regina)if args.mode=='audit'else benchmark(old,args.rounds)
    assert before==pins()
    result.update(native_baseline=BASELINE,native_baseline_source_sha256=hashes,
        native_source_sha256=before,native_seconds=time.perf_counter()-started)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    if certificates is not None:
        args.output.with_name(args.output.stem+'-certificates.json').write_text(json.dumps(json_safe(certificates),indent=2)+'\n')
    print('complete',args.mode,result['native_seconds'],flush=True)


if __name__=='__main__':main()
