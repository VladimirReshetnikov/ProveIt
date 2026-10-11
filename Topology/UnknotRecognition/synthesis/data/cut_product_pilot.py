"""Small geometric midsection checks for wholly prismatic cut components."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys
import time
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_cut_complement import _chamber_system
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from normal_orbit_research.fixtures import regina_triangulation,regina_surface


def inventory(rows):
    marks=set();types=[]
    for t,row in enumerate(rows):
        q=sum(row[4:]);kind=next((j for j in range(3)if row[4+j]),None)
        start=len(types);marks.update((start,start+q))
        types.extend((t,4+kind)if kind is not None else None for _ in range(q+1))
        for v,count in enumerate(row[:4]):
            if count:marks.add(len(types))
            types.extend((t,v)for _ in range(count))
    return marks,types


def main():
    bank={r['id']:r['triangulation']for r in json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())['records']}
    pilot=json.loads((ROOT/'synthesis/data/complement-chamber-pilot.json').read_text())
    records=[];midsections=0;start=time.perf_counter()
    variants=[]
    for case in pilot['records']:
        for scale in ((1,2,3,5)if 0<case['normal_discs']<=32 else(1,)):
            variants.append((case,scale))
    for case,scale in variants:
        raw=bank[case['id']];rows=[[scale*x for x in row]for row in case['coordinates']];prepared=_prepare(raw,lambda:None)
        n,pairs=_chamber_system(prepared,rows,lambda:None);marks,types=inventory(rows)
        parent=list(range(n))
        def find(x):
            while parent[x]!=x:parent[x]=parent[parent[x]];x=parent[x]
            return x
        for pair in pairs:
            for x in range(pair.a,pair.b+1):
                a,b=find(x),find(pair.image(x));parent[b]=a
        groups={}
        for point in range(n):groups.setdefault(find(point),[]).append(point)
        core={find(p)for p in marks};assert len(core)<=len(marks)<=6*len(rows)
        tri=regina_triangulation(raw);cut=regina_surface(tri,rows).cutAlong()
        signatures=Counter((p.eulerCharManifold(),tuple(sorted(b.eulerChar()for b in p.boundaryComponents())))for p in cut.triangulateComponents())
        for root,points in groups.items():
            if root in core:continue
            mid=[[0]*7 for _ in rows]
            for p in points:
                t,c=types[p];mid[t][c]+=1
            analysed=_coordinates(prepared,mid,lambda:None)
            surface=regina_surface(tri,mid);assert surface.isConnected()
            chi=analysed['euler_characteristic'];b=surface.countBoundaries()
            boundary=(2*chi,)if b or not surface.isOrientable()else(chi,chi)
            signature=(chi,tuple(sorted(boundary)))
            assert signatures[signature]>0,(case['id'],case['index'],signature,signatures)
            signatures[signature]-=1;midsections+=1
        assert len(groups)==cut.countComponents()
        records.append(dict(id=case['id'],index=case['index'],scale=scale,cut_components=len(groups),
            marked_chambers=len(marks),core_components=len(core),product_components=len(groups)-len(core)))
    report=dict(source_cases=48,surface_cases=len(records),normal_midsections_checked=midsections,
        records=records,seconds=time.perf_counter()-start,
        corpus_sha256=sha256((ROOT/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest(),
        input_pilot_sha256=sha256((ROOT/'synthesis/data/complement-chamber-pilot.json').read_bytes()).hexdigest(),
        driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'synthesis/data/cut-product-pilot.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k!='records'}))

if __name__=='__main__':main()
