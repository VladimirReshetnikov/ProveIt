"""Native minimum-envelope audit and complete API timing comparisons."""
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
from fastunknot.normal_sector import enumerate_sector,sector_rays,discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_witness,verify_sector_exhaustion
from fastunknot.sector_envelope import sector_envelope_rays
from fastunknot.sector_envelope_certificate import certify_sector_enumeration
from fastunknot.sector_envelope_verify import verify_sector_envelope_certificate
from normal_orbit_research import seeds
from sector_envelope_research import audit as delivered_audit
from sector_envelope_research.fixtures import capped_fibonacci,ray_digest

ROOT=Path(__file__).resolve().parents[1]
CORPUS=ROOT.parent/'reports/57/results/discovery_corpus.json'
BASELINE='654c0b2a7'


def baseline():
    path='Topology/UnknotRecognition/fast/fastunknot/normal_sector.py'
    source=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
    module=ModuleType('fastunknot._envelope_baseline');module.__package__='fastunknot'
    sys.modules[module.__name__]=module
    exec(compile(source,BASELINE+':'+path,'exec'),module.__dict__)
    return module,sha256(source).hexdigest()


def pins():
    result=seeds.sources()
    result[str(CORPUS.relative_to(ROOT.parent))]=sha256(CORPUS.read_bytes()).hexdigest()
    return result


def audit(fresh):
    automatic=[0]
    def checked(kernel,*,stats=None,**options):
        direct=list(sector_envelope_rays(kernel,stats=stats,**options))
        auto_stats={}
        current=list(sector_rays(kernel,phase='standard',method='auto',stats=auto_stats))
        assert direct==current
        if len(kernel.basis):assert auto_stats['method']=='envelope'
        automatic[0]+=1
        yield from direct
    with patch.object(delivered_audit,'sector_envelope_rays',checked):
        result=delivered_audit.run(CORPUS,fresh)
    result['automatic_comparisons']=automatic[0]
    assert automatic[0]==result['counts']['audited']+len(result['capped_family'])+1
    return result


def benchmark(old,rounds):
    cases=[]
    for n,typ in ((1,1),(4,1),(8,1),(16,1),(32,1),(8,0),(16,0)):
        source=capped_fibonacci(n,typ)
        cases.append((f'enumeration/cap-{n}-{typ}',('enumeration',source)))
    for n in (1,4,8,16,32):
        cases.append((f'discovery/cap-{n}-1',('discovery',capped_fibonacci(n,1))))
    source=capped_fibonacci(1,1)
    cases.append(('discovery/empty-sector',('discovery',dict(source,allowed_types=[]))))

    def run(case,use_old):
        kind,source=case;raw,allowed=source['triangulation'],source['allowed_types']
        if kind=='enumeration':
            produce=old.enumerate_sector if use_old else enumerate_sector
            rays,stats=produce(raw,allowed,phase='standard')
            signature=ray_digest(rays)
            wire=seeds.encode(sorted(tuple(v for row in x for v in row) for x in rays))
            return dict(completed=True,output_sha256=signature,output_bytes=len(wire),
                rays=len(rays),bases=stats['bases_attempted'],nonextreme=stats['nonextreme_directions'],
                method=stats['method'])
        produce=old.discover_in_sector if use_old else discover_in_sector
        result=produce(raw,allowed,phase='standard')
        assert result['status']!='INCONCLUSIVE'
        verify=verify_sector_witness if result['status']=='DISC_FOUND' else verify_sector_exhaustion
        assert verify(raw,result['certificate'])
        wire=seeds.encode(result['certificate'])
        return dict(completed=True,output_sha256=sha256(result['status'].encode()).hexdigest(),
            certificate_sha256=sha256(wire).hexdigest(),certificate_bytes=len(wire),
            bases=result['stats']['bases_attempted'],method=result['stats']['method'],status=result['status'])
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
        assert all(v['completed'] and v['output_sha256']==values[0]['output_sha256'] for v in values)
        for arm in ('old','new'):
            values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                    for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
            assert all(v==values[0] for v in values)
    capacity=[]
    for n in (1,8,32,64):
        source=capped_fibonacci(n,1);start=time.perf_counter()
        answer=certify_sector_enumeration(source['triangulation'],source['allowed_types'])
        assert answer['status']=='COMPLETE'
        assert verify_sector_envelope_certificate(source['triangulation'],answer['certificate'])
        wire=seeds.encode(answer['certificate'])
        capacity.append(dict(base_tetrahedra=n,seconds=time.perf_counter()-start,
            certificate_bytes=len(wire),certificate_sha256=sha256(wire).hexdigest(),
            certificate=answer['certificate'],source=source,
            scope='new complete coverage production, replay and serialization only; no speedup comparison'))
    result['coverage_capacity']=capacity
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--fresh-regina',action='store_true');parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    old,old_hash=baseline();before=pins();started=time.perf_counter()
    result=audit(args.fresh_regina) if args.mode=='audit' else benchmark(old,args.rounds)
    assert before==pins()
    result.update(native_source_sha256=before,native_baseline=BASELINE,native_baseline_source_sha256=old_hash,
                  native_seconds=time.perf_counter()-started)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['native_seconds'],flush=True)


if __name__=='__main__':main()
