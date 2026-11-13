#!/usr/bin/env python3
"""Independent source/DAG/auxiliary identity review; never invokes Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

D=Path(__file__).resolve().parents[2]
A=D/'research/ordinary14-aux-graph-equivalence-draft'
def sha(data):return hashlib.sha256(data).hexdigest()
def pinned(path,expected):
    data=path.read_bytes()
    assert sha(data)==expected,str(path)
    return data

source=pinned(A/'AuxGraphEquivalence.lean','57caf3a86a1caf93828331c3775d14e13929a9427d3e8b981398a40d1fee84ea').decode()
readme=(A/'README.md').read_bytes()
tail=(b'\nIndependent source review is recorded in\n'
      b'`../../reviews/ordinary14-aux-graph-equivalence-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)])=='2c350ccdcfdc3c76d80e5750d796712750a5c8774f9f9e40a6f3a840e76caf6d'
files={
 'research/ordinary14-direct-pell79/candidate.json':'5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507',
 'research/ordinary14-aux-root78/candidate.json':'d579ba32a40eed91a336b0015086104e1d1a7c6569092f757328769a3128ab43',
 'research/ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean':'c3350a90b8fa909c208ad197acc7a3bbb15bd3e6d8e45ebf097645ae602ec02e',
 'research/ordinary14-aux-root-model-draft/AuxRootBridge.lean':'796819c48d53665e1ee9c90d8d1bfd0fbd00cd4ca5535fe4fad1a3462d74c8b7',
 'Lean/DiophantineConsistency/Compact44/P72Root.lean':'066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091',
}
data={name:pinned(D/name,value) for name,value in files.items()}
old=json.loads(data['research/ordinary14-direct-pell79/candidate.json'])
new=json.loads(data['research/ordinary14-aux-root78/candidate.json'])
assert old['witnesses'][11]=='u' and new['witnesses'][11]=='y'
assert len(old['witnesses'])==len(new['witnesses'])==14 and old['fixed_numerals']==new['fixed_numerals']

def structures(graph,cut=False):
    vals={name:'slot:'+str(i) for i,name in enumerate(graph['witnesses'])}
    vals.update({name:'port:'+str(i) for i,name in enumerate(graph['fixed_numerals'])})
    deps={name:{value} for name,value in vals.items()}
    def token(x):return 'int:'+str(x) if isinstance(x,int) else vals[x]
    for name,op,a,b in graph['source']:
        vals[name]=sha(json.dumps([op,token(a),token(b)],separators=(',',':')).encode())
        deps[name]=(deps[a] if isinstance(a,str) else set())|(deps[b] if isinstance(b,str) else set())
        if cut and name=='Fa':vals[name]='proved:auxiliary-substitution'
    return vals,deps
old_dag,old_dep=structures(old)
new_dag,new_dep=structures(new)
for field in ('A0','A1','g72','guard','R','Q','V'):
    assert old_dag[field]==new_dag[field],field
    assert 'slot:11' not in old_dep[field] and 'slot:11' not in new_dep[field]

# Exact auxiliary residual substitution in Z[z,Q,u], with y=z+u.
def const(n):return {():n} if n else {}
def var(name):return {(name,):1}
def add(a,b,sign=1):
    out=dict(a)
    for key,val in b.items():out[key]=out.get(key,0)+sign*val
    return {key:val for key,val in out.items() if val}
def mul(a,b):
    out={}
    for ka,va in a.items():
        for kb,vb in b.items():
            key=tuple(sorted(ka+kb));out[key]=out.get(key,0)+va*vb
    return {key:val for key,val in out.items() if val}
z,Q,u=map(var,('z','Q','u'));y=add(z,u)
old_aux=add(add(mul(y,y),mul(Q,mul(u,add(y,z))),-1),const(1),-1)
new_aux=add(add(mul(y,y),mul(Q,add(mul(y,y),mul(z,z),-1)),-1),const(1),-1)
assert old_aux==new_aux
old_cut,_=structures(old,True);new_cut,_=structures(new,True)
assert old_cut['guarded_out']==new_cut['guarded_out']

for text in ('def putAux (v : Fin 14 → V) (u : V) : Fin 14 → V := Function.update v 11 u',
             'theorem putAux_self','theorem putAux_positive','theorem common_fields',
             'theorem other_fields_ignore_aux','theorem old_aux_eval','theorem new_aux_eval',
             'theorem old_output_eval','theorem new_output_eval','theorem positive_zero_iff',
             'theorem positive_zero_iff_natural_ports','(hport : (p 0 : DiffRing V)=ι beta)',
             'bounds_of_79_positive_zero p beta v hbeta hport hv hzero',
             'bounds_of_78_positive_zero p beta v hbeta hport hv hzero',
             'positive_aux_coordinate_iff','P72Root.cast_port p 0'):
    assert text in source,text
norm=data['research/ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean'].decode()
aux=data['research/ordinary14-aux-root-model-draft/AuxRootBridge.lean'].decode()
root=data['Lean/DiophantineConsistency/Compact44/P72Root.lean'].decode()
assert 'theorem bounds_of_79_positive_zero' in norm and 'theorem bounds_of_78_positive_zero' in norm
assert 'theorem positive_aux_coordinate_iff' in aux and '(hQ : 1<Q) (hz : 1<z*z)' in aux
assert 'theorem cast_port (p : Fin 4 → ℕ) (j : Fin 4)' in root

def replay(path,receipt):
    run=subprocess.run([sys.executable,'-I','-S','-B',str(path)],cwd=D,
                       stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120,check=True)
    assert not run.stderr and run.stdout==receipt.read_bytes()
replay(A/'check_source.py',A/'observation.json')
for name in ('ordinary14-aux-graph-norm-client-draft-independent',
             'ordinary14-aux-root-model-draft-independent'):
    packet=D/'reviews'/name
    replay(packet/'check.py',packet/'result.json')
print(json.dumps({'scope':'source and exact graph/auxiliary cuts only; no Lean or model theorem',
                  'author_readme_prelink_sha256':sha(readme[:-len(tail)]),
                  'shared_slot11_independent_fields':['A0','A1','g72','guard','R','Q','V'],
                  'exact_auxiliary_and_output_cuts':True,'component_reviews_replayed':2},
                 sort_keys=True,indent=2))
