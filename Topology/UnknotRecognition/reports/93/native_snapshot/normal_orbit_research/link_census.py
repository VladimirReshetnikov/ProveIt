"""Compare literal-link and incidence-census manifold validation end to end."""
import argparse
from collections import Counter
from contextlib import contextmanager
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
import platform
import random
import subprocess
import sys
import time
from types import ModuleType
from unittest.mock import patch
from fastunknot import Diagram,recognize
from fastunknot import normal_surface_geometry as geometry
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.boundary_shellings import shell_boundary
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import layered_torus,regina_triangulation
from primitive_power_research import forests
ROOT=Path(__file__).resolve().parents[1]
BASELINE='635465da51219f5645424408b4fce3db724e3d6f'
PREVIOUS=ROOT.parent/'synthesis/data/boundary-shellings-audit.json'
CURRENT=geometry._prepare


def baseline():
    path='Topology/UnknotRecognition/fast/fastunknot/normal_surface_geometry.py'
    source=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
    module=ModuleType('_vertex_link_baseline');module.__package__='fastunknot'
    exec(compile(source,BASELINE+':'+path,'exec'),module.__dict__)
    # Keep the live package's exception identity; implementation is unchanged.
    module.NormalOrbitError=geometry.NormalOrbitError
    return module,sha256(source).hexdigest()


def pins():
    result=seeds.sources();result[str(PREVIOUS.relative_to(ROOT.parent))]=sha256(PREVIOUS.read_bytes()).hexdigest()
    return result


@contextmanager
def selecting(function):
    def modules():return [m for name,m in list(sys.modules.items()) if name.startswith('fastunknot.') and m is not None]
    for m in modules():
        if getattr(m,'_prepare',None) is CURRENT:m._prepare=function
    try:yield
    finally:
        # Include aliases imported lazily during the call.
        for m in modules():
            if getattr(m,'_prepare',None) is function:m._prepare=CURRENT


def measured_prepare(function,raw):
    calls=[0]
    def tick():calls[0]+=1
    try:result=function(raw,tick)
    except geometry.NormalOrbitError as exc:return dict(error=str(exc),checks=calls[0]),None
    return dict(geometry_sha256=seeds.digest(result),checks=calls[0]),result


def random_pairing(rng,n,orientable):
    rows=[[None]*4 for _ in range(n)];faces=[(t,f) for t in range(n) for f in range(4)];rng.shuffle(faces)
    for _ in range(rng.randrange(len(faces)//2+1)):
        t,f=faces.pop();u,g=faces.pop()
        maps=[p for p in permutations(range(4)) if p[f]==g and (not orientable or geometry._permutation_sign(p)==-1)]
        p=list(rng.choice(maps));rows[t][f]=dict(tetrahedron=u,permutation=p)
        rows[u][g]=dict(tetrahedron=t,permutation=[p.index(v) for v in range(4)])
    return dict(tetrahedra=rows)


def audit(old):
    previous=json.loads(PREVIOUS.read_text());comparisons=[];source_records=[];proofs={}
    def compare(name,raw):
        a,ap=measured_prepare(old._prepare,raw);b,bp=measured_prepare(CURRENT,raw)
        assert a==b and ap==bp,name
        comparisons.append(dict(name=name,tetrahedra=len(raw['tetrahedra']),result=b))
    for entry in previous['source_cases']:
        source=entry['source'];d=Diagram.from_pd(source['pd']);raw=diagram_exterior(d)
        for label,tri in [('pulling',raw),('shellings',shell_boundary(raw)['triangulation']),('centred',diagram_exterior(d,subdivision='centred'))]:
            compare(source['name']+'-'+label,tri)
        results={}
        for arm,options in [('off',{}),('on',dict(shellings=True)),('planar',dict(shellings=True,planar=True))]:
            r=normal_seed_decide(d,**options)
            if r['status']=='UNKNOT':
                proof=r.pop('certificate');assert verify_normal_seed_certificate(d,proof)
                h=seeds.digest(proof);assert proof==previous['certificates'][h];proofs[h]=proof
                r.update(certificate_sha256=h,schema=proof['schema'])
            assert r=={k:v for k,v in entry['results'][arm].items() if k!='regina'},(source['name'],arm)
            results[arm]=r
        source_records.append(dict(source=source,results=results));print(source['name'],'preserved',flush=True)
    for n in (1,2,4,8,16,32,64,128,256):compare('layered-'+str(n),layered_torus(n)[0])
    rng=random.Random(261009482);negative=Counter();accepted=0;random_hashes=[]
    for i in range(12000):
        raw=random_pairing(rng,rng.randrange(1,9),i%2==0)
        a,ap=measured_prepare(old._prepare,raw);b,bp=measured_prepare(CURRENT,raw)
        assert a==b and ap==bp,(i,raw)
        tri=regina_triangulation(raw)
        supported=(tri.isValid() and tri.isOrientable() and tri.isConnected()
                   and not tri.isIdeal() and tri.countBoundaryComponents()==1
                   and tri.boundaryComponent(0).eulerChar()==0)
        assert bool(supported)==('error' not in b),(i,raw,b)
        if 'error' in b:negative[b['error']]+=1
        else:accepted+=1
        random_hashes.append(seeds.digest(dict(raw=raw,result=b)))
    family=[]
    for n in (1,8,32,128):
        raw=diagram_exterior(Diagram.from_braid(n+1,list(range(1,n+1))));arms={}
        for label,module in [('old',old),('new',geometry)]:
            cls=module._UnionFind;stats=dict(allocated_nodes=0,joins=0)
            class Counted(cls):
                def __init__(self,size):stats['allocated_nodes']+=size;super().__init__(size)
                def join(self,*args,**kwargs):stats['joins']+=1;return super().join(*args,**kwargs)
            with patch.object(module,'_UnionFind',Counted):p=module._prepare(raw,lambda:None)
            N=len(raw['tetrahedra']);B=len(p['boundary_faces']);P=len(p['pairs'])
            assert stats['allocated_nodes']==(34 if label=='old' else 10)*N+B
            assert stats['joins']==(15 if label=='old' else 6)*P+len(p['boundary_incidence'])
            arms[label]=stats
        family.append(dict(tetrahedra=N,boundary_faces=B,paired_faces=P,results=arms))
    ordinary=[]
    for source in forests.corpus():
        answers=[]
        for fn in (old._prepare,CURRENT):
            with selecting(fn):r=recognize(Diagram.from_pd(source['pd']),**seeds.COMMON,use_normal_seed=True)
            assert r.status==source['expected'];answers.append(dict(status=r.status,method=r.method,native_attempts=len(list(seeds.native_stages(r.evidence)))))
        assert answers[0]==answers[1];ordinary.append(dict(name=source['name'],answers=answers))
    return dict(geometry_comparisons=comparisons,source_cases=source_records,certificate_hashes=sorted(proofs),random_pairings=dict(cases=12000,regina_comparisons=12000,accepted=accepted,rejections=dict(negative),records_sha256=seeds.digest(random_hashes)),union_find_family=family,ordinary_pipeline=ordinary)


def benchmark(old,rounds):
    entries={e['source']['name']:e['source'] for e in json.loads(PREVIOUS.read_text())['source_cases']}
    entries['genus-one-miss']=dict(name='genus-one-miss',pd=Diagram.from_braid(2,[1,1,-1]).pd,expected='UNKNOT')
    specs=[('circle-9',False),('circle-9',True),('random-29',False),('random-29',True),('optimized-positive',False),('optimized-positive',True),('random-142',True),('random-1',True),('random-81',True),('trefoil',True),('genus-one-miss',True)]
    cases=[(name+('-shell' if shell else '-plain'),(entries[name],shell)) for name,shell in specs]
    def run(case,use_old):
        source,shell=case;d=Diagram.from_pd(source['pd'])
        with selecting(old._prepare if use_old else CURRENT):
            r=recognize(d,**seeds.FORCED,normal_seed_shellings=shell)
            native=r.evidence.get('normal_seed',{});proof=native.get('certificate')
            if proof is not None:assert verify_normal_seed_certificate(d,proof)
        complete=r.status in ('UNKNOT','KNOTTED')
        if complete:assert r.status==source['expected']
        return dict(completed=complete,status=r.status,method=r.method,native_status=native.get('status'),native_work=native.get('work'),certificate_sha256=seeds.digest(proof) if proof else None)
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        signatures=[{k:v for k,v in sample['measurements'][arm].items() if k!='seconds'} for sample in row['samples']+row['warmups'] for arm in ('old','old_AA','new','new_AA')]
        assert all(s==signatures[0] for s in signatures),row['name']
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','recognize'));parser.add_argument('--rounds',type=int,default=5);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    old,h=baseline();before=pins();start=time.perf_counter();result=audit(old) if args.mode=='audit' else benchmark(old,args.rounds)
    assert before==pins()
    result.update(mode=args.mode,source_sha256=before,baseline_commit=BASELINE,baseline_geometry_sha256=h,elapsed_seconds=time.perf_counter()-start,python=platform.python_version())
    args.output.write_text(json.dumps(seeds.json_safe(result),indent=2)+'\n');print('complete',args.mode,result['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
