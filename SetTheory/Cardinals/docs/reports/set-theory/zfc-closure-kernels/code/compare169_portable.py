"""Static literal tables only; no supplied program or TM simulation is run."""
from pathlib import Path
import argparse, json, hashlib
if not __debug__:
    raise ValueError('Keep assertions enabled.')
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--repo',type=Path,required=True)
ap.add_argument('--recovered',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args();R=a.repo.resolve();B=a.output.resolve();P=a.recovered.resolve()
assert not B.exists() and not B.is_relative_to(R) and not B.is_relative_to(P) and not P.is_relative_to(B)
recovery=json.loads((P/'recovery.json').read_text())
assert recovery['status']=='SIX_ORIGINAL_LAYOUTS_RECOVERED_AND_ALL_MAINTAINED_ALIASES_MATCH'
assert recovery['map_sha256']=='80a344a65f05e6767c773bbecf91aaae05bc22beafd53c9e2c13d997ed403726'
assert [r['source']for r in recovery['sources']]==list(range(74,80))
B.mkdir()

def table(p):
    d={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,m,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert(q,b)not in d and b in(0,1)and w in(0,1)and m in('L','R')
        d[q,b]=(w,m,t)
    return d
def rename(d,f):return {(f(q),b):(w,m,f(t))for(q,b),(w,m,t)in d.items()}
def incoming(d,t):return sorted([q,b,w,m]for(q,b),(w,m,z)in d.items()if z==t)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
basepath=R/'Computability/BusyBeaver/Research/ZFC/candidate-combined243/zfc_combined243_old.tm'
apath=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/72-fold242-runtime-survivor_1_old.tm'
cp=R/'Computability/BusyBeaver/Research/ZFC/candidate-fold241/zfc_fold241_old.tm'
assert sha(basepath)=='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
assert sha(apath)=='c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02'
assert sha(cp)=='1fa8526c3c971d5a48868599eaed890f614c5a79256e51622d3e32a64229f3a3'
base,A,C=map(table,(basepath,apath,cp))
f=lambda q:27 if q==15 else q
alt=rename(A,f)
fold241={(17,0):(0,'L',106),(17,1):(1,'L',37),(46,0):(0,'R',17),(50,0):(0,'R',17)}
reports=[]
for ar in recovery['sources']:
    p=Path(ar['destination']);roots=[q for q in p.iterdir()if q.is_dir()];assert len(roots)==1
    paths=list((roots[0]/'machine').glob('*_old.tm'));assert len(paths)==1;tp=paths[0];d=table(tp)
    assert d==A or d==alt
    is_alt=d==alt
    state_map=f if is_alt else lambda q:q
    states={q for q,b in d};assert len(states)==242 and len(d)==484
    assert {t for w,m,t in d.values()}-states=={254}
    assert incoming(d,17)==[[12,1,1,'R']]
    assert incoming(d,39)==[[46,0,0,'R'],[50,0,0,'R']]
    # Every action read by the four companion paths has identical inherited labels.
    path_rows=[(17,0),(17,1),(39,0),(39,1),(106,1),(92,0),(107,1),(125,0),(37,1),(55,1),(106,0),(93,0),(37,0),(25,1)]
    assert all(d[k]==A[k]for k in path_rows)
    composed={k:fold241.get(k,v)for k,v in d.items()if k[0]!=39}
    assert composed==rename(C,state_map) and len(composed)==482
    # Literal unqualified union of the two alternative 242 reductions is invalid.
    combined={k:v for k,v in base.items()if k[0]not in(15,27)}
    combined.update({(18,0):(0,'L',15),(47,0):(0,'L',15),(65,0):(0,'L',15),(11,0):(0,'R',27)})
    dangling=sorted([q,b,t]for(q,b),(w,m,t)in combined.items()if t in(15,27))
    assert dangling
    reports.append(dict(archive=ar['archive'],table=str(tp),table_sha256=sha(tp),removed=sorted({q for q,b in base}-states),patch=[dict(state=q,read=b,old=base[q,b],new=v)for(q,b),v in sorted(d.items())if base[q,b]!=v],same_as_primary242A_up_to_renaming=True,renaming_from_primaryA={'15':27}if is_alt else {},verified_rows=484,companion241_incoming_and_path_rows_unchanged=True,composed_rows=482,composed_machine_is_current241_up_to_same_renaming=True))
result=dict(status='SIX_LITERAL_TABLES_SAME_MACHINE_UP_TO_ONE_RENAMING',base=str(basepath),primary242A=str(apath),primary241=str(cp),reports=reports,naive_union_dangling_targets=dangling,new_240_machine=False,scope='Static transition relations, complete state-map isomorphism and exact composition with the existing 17/39 patch. No supplied program, simulator, proof compiler, or new runtime replay. Auxiliary research reviewed separately.')
(B/'table-comparison-root.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
