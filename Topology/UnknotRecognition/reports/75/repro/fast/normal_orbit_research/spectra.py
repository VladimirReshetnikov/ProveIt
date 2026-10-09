"""Audit full component types and time the smaller source-bound topology observer."""
import argparse
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
import time

from fastunknot.integer_codec import json_safe
from fastunknot.normal_topology import normal_topology_spectrum
from fastunknot.normal_topology_verify import verify_normal_topology_spectrum
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import layered_torus,interior_vertex_torus
from topology_research.benchmark import coordinates_reference,verify_coordinates_reference

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT.parent/'synthesis/data'
CORPUS=ROOT.parent/'reports/53/results/normal_audit_20261009_corpus.json'


def expected(records):
    types=defaultdict(int)
    for r in records:
        types[r['euler_characteristic'],r['boundary_components'],r['orientable']]+=r['multiplicity']
    rows=[]
    for (chi,b,orientable),amount in sorted(types.items(),key=lambda item:(item[0][0],item[0][1],not item[0][2])):
        if not amount:continue
        row=dict(chi=chi,boundary_components=b,orientable=orientable,multiplicity=amount)
        row['genus' if orientable else 'crosscaps']=(2-chi-b)//2 if orientable else 2-chi-b
        rows.append(row)
    return rows


def corpus():
    data=json.loads(CORPUS.read_text())
    raw={r['id']:r['triangulation'] for r in data['triangulations']}
    return [(case,raw[case['triangulation_id']],case['coordinates']) for case in data['cases']]


def audit():
    rows=[];saved={}
    for i,(case,raw,coords) in enumerate(corpus()):
        target=expected(case['expected']['component_records'])
        for reduce in (False,True):
            for rule in ('fine_wilf','aht'):
                answer=normal_topology_spectrum(raw,coords,reduce_core=reduce,periodic_rule=rule,record_certificate=True)
                assert answer['status']=='COMPLETE' and answer['topology_spectrum']==target
                assert verify_normal_topology_spectrum(raw,coords,answer['certificate'])
                for k in ('components','boundary_components','euler_characteristic'):
                    assert answer[k]==case['expected'][k]
                if answer['certificate']['query'] is not None:
                    assert all(answer['certificate']['query'][key]['dimension']==2 for key in ('surface','double'))
                wire=seeds.encode(answer['certificate'])
                rows.append(dict(case_id=case['id'],reduce_core=reduce,periodic_rule=rule,spectrum=target,
                    certificate_sha256=sha256(wire).hexdigest(),certificate_bytes=len(wire),
                    cycles=answer['stats']['orbit_cycles'],queries=answer['stats']['queries']))
                key=(case['category'],reduce,rule)
                if key not in saved:saved[key]=dict(case_id=case['id'],triangulation=raw,coordinates=coords,certificate=answer['certificate'])
        if i%200==0:print(i,'of 1275',flush=True)
    return dict(cases=rows,examples=list(saved.values()),component_oracle='frozen independent component records in report 53',
                configurations=len(rows),input_vectors=1275)


def inputs():
    result=[]
    for n in (8,32,64):
        raw,coords=layered_torus(n);result.append((f'layered-{n}',(raw,coords)))
    raw,coords=layered_torus(32)
    result.append(('layered-32-binary-scale',(raw,[[(2**2048+1)*v for v in row] for row in coords])))
    raw,_=layered_torus(1)
    for name,coords in [('empty',[[0]*7]),('vertex-link',[[1,1,1,1,0,0,0]]),
                       ('mobius',[[0,0,0,0,0,1,0]]),('mobius-even',[[0,0,0,0,0,2,0]])]:
        result.append((name,(raw,coords)))
    raw,basis=interior_vertex_torus()
    for name,counts in [('mixed-components',(3,5,7)),('binary-mixture',((1<<2048)+1,(1<<1024)+2,(1<<4096)+3))]:
        vectors=list(basis.values())
        coords=[[sum(counts[k]*vectors[k][t][j] for k in range(3)) for j in range(7)] for t in range(len(vectors[0]))]
        result.append((name,(raw,coords)))
    fixture=json.loads((ROOT/'topology_research/data/klein_torus.json').read_text())
    result.append(('klein-torus',(fixture['triangulation'],fixture['coordinates'])))
    return result


def benchmark(rounds):
    cases=[('coordinates/'+n,('coordinates',case)) for n,case in inputs()]
    for n,case in inputs():
        if n in ('layered-32-binary-scale','binary-mixture','vertex-link','mobius-even'):
            cases.append(('direct/'+n,('direct',case)))
    def run(case,use_old):
        reference,(raw,coords)=case
        if use_old and reference=='coordinates':
            answer=coordinates_reference(raw,coords,lambda:None)
            assert verify_coordinates_reference(raw,coords,answer['certificate'],lambda:None)
        else:
            answer=normal_topology_spectrum(raw,coords,reduce_core=not(use_old and reference=='direct'),record_certificate=True)
            assert verify_normal_topology_spectrum(raw,coords,answer['certificate'])
        assert answer['status']=='COMPLETE'
        proof=seeds.encode(answer['certificate']);spectrum=seeds.encode(answer['topology_spectrum'])
        return dict(completed=True,spectrum_sha256=sha256(spectrum).hexdigest(),spectrum=answer['topology_spectrum'],
            certificate_sha256=sha256(proof).hexdigest(),certificate_bytes=len(proof),
            cycles=answer['stats']['orbit_cycles'],queries=answer['stats']['queries'],weight_dimension=answer['stats'].get('weight_dimension',2))
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
        assert all(v['completed'] and v['spectrum_sha256']==values[0]['spectrum_sha256'] for v in values)
        for arm in ('old','new'):
            values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'} for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
            assert all(v==values[0] for v in values)
    return result


def pins():
    result=seeds.sources()
    for path in (CORPUS,ROOT/'topology_research/data/klein_torus.json',DATA/'incoming-sectors-reflection-counterexample.json'):
        result[str(path.relative_to(ROOT.parent))]=sha256(path.read_bytes()).hexdigest()
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--rounds',type=int,default=5);args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    before=pins();started=time.perf_counter()
    result=audit() if args.mode=='audit' else benchmark(args.rounds)
    assert before==pins()
    result.update(source_sha256=before,seconds=time.perf_counter()-started,mode=args.mode)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['seconds'],flush=True)


if __name__=='__main__':main()
