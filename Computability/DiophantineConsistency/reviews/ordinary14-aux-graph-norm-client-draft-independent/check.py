#!/usr/bin/env python3
"""Independent model-source and exact graph-cut review; no Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

D=Path(__file__).resolve().parents[2]
A=D/'research/ordinary14-aux-graph-norm-client-draft'
G=D/'research/ordinary14-aux-root78-lean-draft'
R=D/'reviews/ordinary14-aux-ring-norm-extraction-draft-independent'
def sha(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data=path.read_bytes()
    assert sha(data)==expected, str(path)
    return data

source=pinned(A/'GraphNormClient.lean','c3350a90b8fa909c208ad197acc7a3bbb15bd3e6d8e45ebf097645ae602ec02e').decode()
readme=(A/'README.md').read_bytes()
tail=(b'\nIndependent source review is recorded in\n'
      b'`../../reviews/ordinary14-aux-graph-norm-client-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)])=='0f4092c6316f5b75beb9890d3262052e2347b3d711658ce8e5c6bc8e60b55c1d'
files={
 'research/ordinary14-direct-pell79/candidate.json':'5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507',
 'research/ordinary14-aux-root78/candidate.json':'d579ba32a40eed91a336b0015086104e1d1a7c6569092f757328769a3128ab43',
 'research/ordinary14-direct-pell79-lean-draft/P79DirectPell.lean':'e5b138f7ea6b5782d66fde5016726e01c9045bf5ba13858dad1d923ca9622cdb',
 'research/ordinary14-aux-root78-lean-draft/P78AuxRoot.lean':'1a412f13645a0c5c91554b71ee67e24e34ab968bf69575292eaf43225a52d9f7',
 'research/ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean':'771cc1bf65a1d0e2b195627a45a4d152671ed0e86dbf12516855bfe8f1c11216',
}
data={name:pinned(D/name,value) for name,value in files.items()}
g79=json.loads(data['research/ordinary14-direct-pell79/candidate.json'])
g78=json.loads(data['research/ordinary14-aux-root78/candidate.json'])
assert len(g79['witnesses'])==len(g78['witnesses'])==14
assert g79['witnesses'][11]=='u' and g78['witnesses'][11]=='y'
assert g79['fixed_numerals']==g78['fixed_numerals']

def op(operator,a,b): return sha(json.dumps([operator,a,b],separators=(',',':')).encode())
def integer(n): return 'int:'+str(n)
def structures(graph):
    values={name:'slot:'+str(i) for i,name in enumerate(graph['witnesses'])}
    values.update({name:'port:'+str(i) for i,name in enumerate(graph['fixed_numerals'])})
    def token(x): return integer(x) if isinstance(x,int) else values[x]
    for name,operator,a,b in graph['source']:values[name]=op(operator,token(a),token(b))
    return values
old,new=structures(g79),structures(g78)
for name in ('A0','A1','g72','Dstar','R','Q','V'):
    assert old[name]==new[name], name

# Reconstruct signed rank/carrier and the direct first, Q and z cuts separately.
s=lambda i:'slot:'+str(i)
p=lambda i:'port:'+str(i)
plus=lambda a,b:op('+',a,b)
minus=lambda a,b:op('-',a,b)
times=lambda a,b:op('*',a,b)
b=times(s(0),p(0)); q=plus(integer(1),b); X=times(q,s(6))
q2=times(q,q); Y=times(times(q,q2),s(7)); U=times(Y,q2)
k=plus(s(9),s(10)); c=plus(s(9),times(Y,k)); a=plus(times(X,Y),Y)
H=plus(integer(3),times(integer(4),a)); Delta=plus(H,times(a,a))
rank=plus(times(plus(s(2),times(minus(q,s(1)),b)),minus(q2,integer(1))),
          times(s(0),plus(p(2),times(p(3),q))))
main=plus(times(U,plus(X,times(a,c))),times(H,minus(times(U,s(12)),minus(minus(k,rank),integer(1)))))
f2=times(s(3),s(3)); Q=times(Delta,minus(f2,integer(1)))
z=minus(times(f2,minus(times(s(5),c),rank)),c)
ell=times(times(X,Y),times(Y,k))
first=minus(times(s(8),s(8)),plus(integer(1),times(ell,plus(ell,k))))
for name,expected in (('R',rank),('Dstar',main),('Q',Q),('V',z),('A0',first)):
    assert old[name]==expected, name

for text in ('theorem first_eval', 'theorem main_eval', 'theorem strong_eval',
             'theorem fields_of_zero', 'theorem common_norm_fields', 'theorem fields_of_78_zero',
             'theorem bounds_of_fields', 'theorem bounds_of_79_positive_zero',
             'theorem bounds_of_78_positive_zero', '(hport : (p 0 : DiffRing V)=ι beta)',
             '(hz : InternalZero (P78AuxRoot.graph p).output v)',
             'bounds_of_direct_field_residuals', 'def rank', 'def mainValue', 'def coeff', 'def zvalue'):
    assert text in source, text
assert 'theorem bounds_of_direct_field_residuals' in data['research/ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean'].decode()

# Ring regroupings: Delta*(c*c)=(Delta*c)*c and (c*c*i)^2=(i*c*c)^2.
def var(name): return {(name,):1}
def multiply(a,b):
    out={}
    for ka,va in a.items():
        for kb,vb in b.items():
            key=tuple(sorted(ka+kb));out[key]=out.get(key,0)+va*vb
    return {key:value for key,value in out.items() if value}
di,cc,ii=map(var,('Delta','c','i'))
assert multiply(di,multiply(cc,cc))==multiply(multiply(di,cc),cc)
left=multiply(multiply(cc,cc),ii);right=multiply(multiply(ii,cc),cc)
assert multiply(left,left)==multiply(right,right)

def replay(path,argv,receipt):
    run=subprocess.run([sys.executable,'-I','-S','-B',str(path),*argv],cwd=D,
                       stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120,check=True)
    assert not run.stderr and run.stdout==receipt.read_bytes()
replay(G/'make_graph.py',['--check'],G/'observation.json')
replay(A/'check_source.py',[],A/'observation.json')
replay(R/'check.py',[],R/'result.json')
print(json.dumps({'scope':'source and exact graph cuts only; no Lean or model theorem',
                  'author_readme_prelink_sha256':sha(readme[:-len(tail)]),
                  'shared_norm_fields':['A0','A1','g72'],'exact_signed_formula_cuts':True,
                  'ring_regroupings':True,'graph_generator_and_factor_review_replayed':True},
                 sort_keys=True,indent=2))
