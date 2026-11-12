from pathlib import Path
from hashlib import sha256
from math import isqrt
import json, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-positive87-to88-aux-independent')
pins=json.loads((D/'pins.json').read_text())
for name, expected in pins.items():
    assert sha256(Path(name).read_bytes()).hexdigest()==expected,name
A=Path('research/ordinary13-positive87-to88-aux-model-audit')
import subprocess
actual=subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])
assert actual==(A/'receipt.json').read_bytes()
child=json.loads(Path('research/ordinary13-aux-root87-36/candidate.json').read_text())
parent=json.loads(Path('research/ordinary13-four-square88-30/candidate.json').read_text())
assert len(child['source'])==87 and len(parent['source'])==88
assert parent['witnesses'][11]=='u' and child['witnesses'][11]=='y'
assert all(parent['witnesses'][i]==child['witnesses'][i] for i in range(13) if i!=11)
assert parent['fixed_numerals']==child['fixed_numerals']
def evaluate(graph, witness, ports):
    v=dict(zip(graph['witnesses'],witness)); v.update(zip(graph['fixed_numerals'],ports))
    for name,op,l,r in graph['source']:
        a=v[l] if isinstance(l,str) else l; b=v[r] if isinstance(r,str) else r
        v[name]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
    return v
# Signed deterministic graph controls with y=V+u, not zero assertions.
count=0
for t in range(180):
    xs=[((t*(2*j+3)+j*j+5)%9)-4 for j in range(13)]
    ps=[((t*(j+2)+j)%7)-3 for j in range(4)]
    old=evaluate(parent,xs,ps); ys=xs.copy(); ys[11]=old['V']+xs[11]
    new=evaluate(child,ys,ps)
    for field in ('A0','A1','g72','V','Q','Fa','out'):
        assert old[field]==new[field],(t,field)
    assert old['out']==old['A0']**2+old['A1']**2+(old['Fa']-1)**2+old['g72']**2
    count+=1
# Direct integer checks of both positive-witness implications at auxiliary zeros.
roots=0; oldroots=0; signs=set()
for Q in range(2,45):
    for z in range(-80,81):
        if z*z<=1: continue
        num=Q*z*z-1; den=Q-1
        if num%den: continue
        y=isqrt(num//den)
        if y*y!=num//den:continue
        assert y>0 and y*y>z*z and y>z
        u=y-z;assert u>0
        assert y*y-Q*(y*y-z*z)-1==0
        assert (z+u)**2-Q*u*(z+u+z)-1==0
        roots+=1;signs.add((z>0,z<0))
        for oldy in (y,-y):
            oldu=oldy-z
            if oldu>0:
                assert oldy>0
                oldroots+=1
assert roots>20 and oldroots>20 and signs=={(True,False),(False,True)}
# Scale-square arithmetic: the scale need not divide Y and root sign is irrelevant.
scales=0
for m in range(1,25):
    for n in range(1,90):
        for z in range(0,200):
            if z*z==m*m*n:
                assert z%m==0 and (z//m)**2==n
                scales+=1
assert scales>100
sources={p:Path(p).read_text() for p in pins if p.endswith('.lean')}
bridge=sources['research/ordinary14-aux-root-model-draft/AuxRootBridge.lean']
extract=sources['research/ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean']
bounds=sources['research/ordinary14-aux-norms-to-bounds-draft/NormsToBounds.lean']
quot=sources['Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean']
for term in ['(hQ : 1<Q) (hz : 1<z*z)','(nonneg_iff).mp','theorem positive_aux_coordinate_iff']:
    assert term in bridge
for term in ['(hU : 0<U)','∃ d : V, d*d=n','scaled_quotient U z n hU hsq','theorem first_norm_of_ring_residual']:
    assert term in extract
for term in ['(heta : 0<eta) (hzeta : 0<zeta) (hi : 0<i)','(hfirst :','(hmain :','(hstrong :','(hQ :','(hz :']:
    assert term in bounds
assert 'theorem scaled_quotient (m z n : V) (hm : 0<m)' in quot
print(json.dumps({'author_receipt_exact':True,'pinned_files':len(pins),'signed_graph_controls':count,'positive_direct_root_controls':roots,'positive_old_root_controls':oldroots,'scaled_square_controls':scales,'model_graph_bindings_proved':False,'lean_executed':False},sort_keys=True,indent=2))
