"""Pinned complete sector-discovery timings against an independent dense model."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import time

from fastunknot.integer_codec import json_safe
from fastunknot.normal_sector import discover_in_sector
from fastunknot.normal_sector_verify import dense_sector_model,dense_reference_rays,verify_sector_witness,verify_sector_exhaustion
from fastunknot.normal_disk_kernel import normal_compressing_disk_count
from normal_orbit_research import seeds

ROOT=Path(__file__).resolve().parents[1]
REPORT=ROOT.parent/'reports/57'


def dense_discover(raw,allowed):
    model=dense_sector_model(raw,allowed)
    rays=dense_reference_rays(model,'quadrilateral')
    records=[];positive=False
    source=sha256(json.dumps(raw,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    for q,(rows,chi) in sorted(rays.items()):
        record=dict(quadrilaterals=list(q),euler_characteristic=chi);records.append(record)
        if chi<=0:continue
        positive=True
        answer=normal_compressing_disk_count(raw,rows,record_certificate=True)
        assert answer['status']=='COMPLETE'
        record['disk_certificate']=answer['certificate']
        if answer['contains_compressing_disk']:
            return dict(status='DISC_FOUND',certificate=dict(schema='normal-sector-witness-v1',source_sha256=source,
                allowed_types=[list(p) for p in sorted(allowed)],coordinates=rows,disk_certificate=answer['certificate']))
    status='POSITIVE_EULER_ONLY' if positive else 'NO_POSITIVE_EULER'
    return dict(status=status,certificate=dict(schema='normal-sector-exhaustion-v1',source_sha256=source,
        allowed_types=[list(p) for p in sorted(allowed)],phase='quadrilateral',status=status,rays=records))


def pins():
    result=seeds.sources()
    for p in REPORT.rglob('*'):
        if p.is_file() and p.suffix in ('.py','.json','.tex'):
            result[str(p.relative_to(ROOT.parent))]=sha256(p.read_bytes()).hexdigest()
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--rounds',type=int,default=5)
    args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    corpus=json.loads((REPORT/'results/discovery_corpus.json').read_text())
    fixtures={r['id']:r for r in corpus['records']}
    cases=[]
    for n in (4,8,10):
        fixture=fixtures[f'fibonacci_lst_{n:02d}']
        vector=next(r['coordinates'] for r in fixture['standard_vertices'] if r['essential_disc'])
        allowed=[(i,q) for i,row in enumerate(vector) for q in range(3) if row[4+q]]
        cases.append((f'layered-{n}',(fixture['triangulation'],allowed)))
    raw=fixtures['fibonacci_lst_01']['triangulation']
    for name,allowed in [('empty',[]),('annulus',[(0,0)]),('one-sided',[(0,1)])]:cases.append((name,(raw,allowed)))
    cases.append(('inessential-positive',(fixtures['cap_1_2_1']['triangulation'],[(1,0)])))
    source_pins=pins();start=time.perf_counter()
    def run(case,use_old):
        raw,allowed=case
        answer=(dense_discover if use_old else discover_in_sector)(raw,allowed)
        proof=answer['certificate']
        verify=verify_sector_witness if answer['status']=='DISC_FOUND' else verify_sector_exhaustion
        assert verify(raw,proof)
        wire=seeds.encode(proof)
        return dict(completed=True,status=answer['status'],coordinates=proof.get('coordinates'),
            source_sha256=proof['source_sha256'],certificate_sha256=sha256(wire).hexdigest(),certificate_bytes=len(wire))
    result=seeds.rounds(cases,run,args.rounds)
    for row in result['cases']:
        values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
        assert all(v['completed'] and v['status']==values[0]['status'] and v['coordinates']==values[0]['coordinates'] for v in values)
        for arm in ('old','new'):
            values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'} for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
            assert all(v==values[0] for v in values)
    assert source_pins==pins()
    result.update(source_sha256=source_pins,seconds=time.perf_counter()-start,
        scope='supplied sector Q-ray discovery, essentiality proof, independent replay and serialization; dense reference is not an optimized normal enumerator')
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',result['seconds'],flush=True)


if __name__=='__main__':main()
