"""Finite geometric pilot: chamber connectivity of cut-open normal surfaces."""
from hashlib import sha256
import json
from pathlib import Path
import sys
import time
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_surface_geometry import _prepare,_coordinates,_quad
from fastunknot.interval_orbits import IntervalPairing,count_orbits
from normal_orbit_research.fixtures import regina_triangulation,regina_surface


def chambers(prepared,rows):
    layout=[];total=0
    for row in rows:
        q=sum(row[4:]);kind=next((j for j in range(3)if row[4+j]),None)
        chain=total;total+=q+1;arms=[]
        for v in range(4):arms.append(total);total+=row[v]
        layout.append((chain,arms,q,kind))
    def local(t,f,v,rank):
        chain,arms,q,kind=layout[t]
        if rank<rows[t][v]:return arms[v]+rank,1
        assert kind is not None and _quad(f,v)==kind
        if v in (0,kind+1):return chain+rank-rows[t][v],1
        return chain+q-rank+rows[t][v],-1
    def central(t,f):
        chain,arms,q,kind=layout[t]
        return chain+(q if kind is not None and f in (0,kind+1)else 0)
    pairs=[]
    for t,f,u,g,p in prepared['pairs']:
        a,b=central(t,f),central(u,g)
        pairs.append(IntervalPairing(a,a,b,b))
        for v in range(4):
            if v==f:continue
            w=p[v]
            size=rows[t][v]+rows[t][4+_quad(f,v)]
            assert size==rows[u][w]+rows[u][4+_quad(g,w)]
            bounds=sorted({0,rows[t][v],rows[u][w],size})
            for low,stop in zip(bounds,bounds[1:]):
                if low==stop:continue
                a,sa=local(t,f,v,low);b,sb=local(u,g,w,low)
                aa=a+sa*(stop-low-1);bb=b+sb*(stop-low-1)
                pairs.append(IntervalPairing(min(a,aa),max(a,aa),min(b,bb),max(b,bb),sa!=sb))
    return total,pairs


def main():
    bank=json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())['records']
    records=[];start=time.perf_counter()
    for case in bank:
        prepared=_prepare(case['triangulation'],lambda:None);tri=regina_triangulation(case['triangulation'])
        count=0
        vertices=[v['coordinates']for v in case['standard_vertices']if v['normal_discs']<=64]
        vertices.append([[0]*7 for _ in case['triangulation']['tetrahedra']])
        for i,rows in enumerate(vertices):
            analysed=_coordinates(prepared,rows,lambda:None)
            n,pairs=chambers(prepared,rows)
            result=count_orbits(n,pairs)
            cut=regina_surface(tri,rows).cutAlong()
            expected=cut.countComponents()
            assert result.complete and result.orbits==expected,(case['id'],i,result.orbits,expected,rows)
            records.append(dict(id=case['id'],index=i,coordinates=rows,normal_discs=analysed['normal_disks'],
                chamber_points=n,interval_pairings=len(pairs),components=expected,expanded_cut_tetrahedra=cut.size()))
            count+=1
        print(case['id'],count,flush=True)
    report=dict(source_cases=len(bank),surface_cases=len(records),max_discs=64,records=records,
        seconds=time.perf_counter()-start,corpus_sha256=sha256((ROOT/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest(),
        driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'synthesis/data/complement-chamber-pilot.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k!='records'}))

if __name__=='__main__':main()
