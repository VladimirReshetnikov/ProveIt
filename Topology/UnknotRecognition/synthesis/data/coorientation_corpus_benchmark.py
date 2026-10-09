"""Isolated complete-call timing over all 1,275 frozen supplied surfaces."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from normal_orbit_research import coorientation as research
from normal_orbit_research import seeds


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    old,old_check,hashes=research.baseline()
    corpus=json.loads(research.CORPUS.read_text())
    triangulations={r['id']:r['triangulation'] for r in corpus['triangulations']}
    cases=[(triangulations[c['triangulation_id']],c['coordinates']) for c in corpus['cases']]
    pins=research.pins();pins[str(Path(__file__).relative_to(ROOT))]=sha256(Path(__file__).read_bytes()).hexdigest()
    def run(unused,use_old):
        produce,verify=(old,old_check) if use_old else (research.normal_surface_topology,research.verify_normal_surface_certificate)
        proof_hash,topology_hash=sha256(),sha256()
        size=events=cycles=derived=0
        for raw,coords in cases:
            answer=produce(raw,coords,record_certificate=True)
            assert verify(raw,coords,answer['certificate'])
            proof=research.encoded(answer['certificate'])
            size+=len(proof);proof_hash.update(proof)
            topology_hash.update(research.encoded(research.topology(answer)))
            cycles+=answer['cycles']
            events+=sum(len(p['operations']) for p in answer['certificate']['queries'].values())
            derived+=answer['certificate']['schema']=='normal-surface-topology-v4'
        return dict(completed=True,surfaces=len(cases),proof_bytes=size,events=events,cycles=cycles,
                    derived=derived,certificate_sha256=proof_hash.hexdigest(),topology_sha256=topology_hash.hexdigest())
    start=time.perf_counter()
    result=seeds.rounds([('1275-supplied-surfaces',None)],run,args.rounds)
    row=result['cases'][0]
    records=[r for s in row['warmups']+row['samples'] for r in s['measurements'].values()]
    assert len({r['topology_sha256'] for r in records})==1
    for arm in ('old','new'):
        records=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                 for s in row['warmups']+row['samples'] for a in (arm,arm+'_AA')]
        assert all(r==records[0] for r in records)
    for path,digest in pins.items():assert sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    result.update(baseline=research.BASELINE,baseline_source_sha256=hashes,source_sha256=pins,
                  seconds=time.perf_counter()-start,measured_surface_calls=1275*result['measured_calls'],
                  warmup_surface_calls=1275*result['warmup_calls'])
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('complete',result['seconds'],flush=True)


if __name__=='__main__':main()
