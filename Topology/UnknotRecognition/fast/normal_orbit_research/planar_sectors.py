"""Native adaptive planar rays against a frozen incumbent and full oracle."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import time
from types import ModuleType
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_sector import sector_rays,enumerate_sector,discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_witness,verify_sector_exhaustion
from fastunknot.sector_planar import sector_planar_rays,certify_planar_sector
from fastunknot.sector_planar_verify import verify_planar_sector_certificate
from normal_orbit_research import seeds
from planar_sector_research import audit as package_audit
from planar_sector_research.fixtures import double_capped_fibonacci,capped_fibonacci,ray_digest,vector_key

ROOT=Path(__file__).resolve().parents[1]
CORPUS=ROOT.parent/'reports/57/results/discovery_corpus.json'
BASELINE='6a34c5c0d'


def baseline():
    path='Topology/UnknotRecognition/fast/fastunknot/normal_sector.py'
    code=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
    m=ModuleType('fastunknot._planar_native_baseline');m.__package__='fastunknot';sys.modules[m.__name__]=m
    exec(compile(code,BASELINE+':'+path,'exec'),m.__dict__)
    return m,sha256(code).hexdigest()


def pins():
    result=seeds.sources();result[str(CORPUS.relative_to(ROOT.parent))]=sha256(CORPUS.read_bytes()).hexdigest()
    return result


def audit(old,fresh):
    counts=dict(auto_comparisons=0,low_dimension_legacy_exact=0,new_nullity_three=0)
    def checked(kernel,*,stats=None,**options):
        direct=list(sector_planar_rays(kernel,stats=stats,**options))
        auto_stats={};auto=list(sector_rays(kernel,stats=auto_stats))
        assert {vector_key(r) for r in direct}=={vector_key(r) for r in auto}
        d=len(kernel.basis);counts['auto_comparisons']+=1
        if d<=2:
            legacy_stats={};legacy=list(old.sector_rays(kernel,stats=legacy_stats))
            assert legacy==auto and legacy_stats==auto_stats
            counts['low_dimension_legacy_exact']+=1
        else:
            assert auto_stats['method']=='planar' and auto_stats['bases_attempted']==len(auto)
            counts['new_nullity_three']+=1
        yield from direct
    with patch.object(package_audit,'sector_planar_rays',checked):
        result,certificates=package_audit.run(CORPUS,fresh_regina=fresh)
    result['native_dispatch']=counts
    return result,certificates


def benchmark(old,rounds):
    cases=[]
    for n in (1,4,8,16):
        cases.append((f'enumeration/double-cap-{n}',('enumeration',double_capped_fibonacci(n))))
    for n in (1,4,8,16):
        cases.append((f'discovery/double-cap-{n}',('discovery',double_capped_fibonacci(n))))
    for n in (4,8):cases.append((f'enumeration/single-cap-{n}',('enumeration',capped_fibonacci(n))))
    raw=double_capped_fibonacci(1)
    cases.append(('discovery/empty-sector',('discovery',dict(raw,allowed_types=[]))))
    def run(case,use_old):
        kind,source=case;tri,allowed=source['triangulation'],source['allowed_types']
        if kind=='enumeration':
            produce=old.enumerate_sector if use_old else enumerate_sector
            rays,stats=produce(tri,allowed)
            wire=seeds.encode(sorted(tuple(x for row in r for x in row) for r in rays))
            return dict(completed=True,output_sha256=ray_digest(rays),output_bytes=len(wire),rays=len(rays),
                bases=stats['bases_attempted'],nonextreme=stats['nonextreme_directions'],method=stats['method'])
        produce=old.discover_in_sector if use_old else discover_in_sector
        answer=produce(tri,allowed,phase='standard')
        assert answer['status']!='INCONCLUSIVE'
        verify=verify_sector_witness if answer['status']=='DISC_FOUND' else verify_sector_exhaustion
        assert verify(tri,answer['certificate'])
        wire=seeds.encode(answer['certificate'])
        return dict(completed=True,output_sha256=sha256(answer['status'].encode()).hexdigest(),
            certificate_sha256=sha256(wire).hexdigest(),certificate_bytes=len(wire),
            bases=answer['stats']['bases_attempted'],method=answer['stats']['method'],status=answer['status'])
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
        assert all(v['completed'] and v['output_sha256']==values[0]['output_sha256'] for v in values)
        for arm in ('old','new'):
            values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                    for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
            assert all(v==values[0] for v in values)
    capacity=[]
    for n in (1,8,16,32):
        source=double_capped_fibonacci(n);start=time.perf_counter()
        answer=certify_planar_sector(source['triangulation'],source['allowed_types'])
        assert answer['status']=='COMPLETE' and verify_planar_sector_certificate(source['triangulation'],answer['certificate'])
        wire=seeds.encode(answer['certificate'])
        capacity.append(dict(base_tetrahedra=n,seconds=time.perf_counter()-start,certificate=answer['certificate'],
            source=source,certificate_bytes=len(wire),certificate_sha256=sha256(wire).hexdigest(),scope='new-only coverage capacity'))
    result['coverage_capacity']=capacity
    return result,None


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--fresh-regina',action='store_true')
    parser.add_argument('--rounds',type=int,default=5);args=parser.parse_args()
    old,h=baseline();before=pins();start=time.perf_counter()
    result,certificates=audit(old,args.fresh_regina) if args.mode=='audit' else benchmark(old,args.rounds)
    assert before==pins();result.update(native_source_sha256=before,native_baseline=BASELINE,
        native_baseline_source_sha256=h,native_seconds=time.perf_counter()-start)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    if certificates is not None:args.output.with_name(args.output.stem+'-certificates.json').write_text(json.dumps(json_safe(certificates),indent=2)+'\n')
    print('complete',args.mode,result['native_seconds'],flush=True)


if __name__=='__main__':main()
