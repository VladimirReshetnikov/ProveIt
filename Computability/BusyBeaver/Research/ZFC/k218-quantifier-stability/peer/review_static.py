#!/usr/bin/env python3
"""Independent inert proof-DAG reader; never imports or runs the submitted checker."""
from pathlib import Path
import json, hashlib
P = Path('/tmp/k218-quantifier-stability')
OUT = Path(__file__).parent
def desc(p):
    return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
def I(a,b): return ['I',a,b]
def Q(a,b): return ['Q',a,b]
def R(a,b): return ['R',a,b]
def E(a,b): return ['E',a,b]
T=['zero']; F=R(T,T)
def N(a): return I(a,F)
def NN(a): return N(N(a))
def Ex(i,a): return N(Q(i,N(a)))
def req(b,k,m): return Q(b,I(m,N(Q(b,I(m,N(R(b,k)))))))
def clos(a,b,k,m):
    subset=Q(k,I(R(k,a),R(k,b)))
    inner=N(Q(a,I(subset,req(b,k,m))))
    return Q(b,I(R(b,k),N(Q(a,I(m,inner)))))
def primitive(rule,args):
    if rule=='truth': assert not args; return T
    if rule=='K': a,b=args; return I(a,I(b,a))
    if rule=='S': a,b,c=args; return I(I(a,I(b,c)),I(I(a,b),I(a,c)))
    if rule=='rho1': i,a=args; return Ex(i,E(i,a))
    if rule=='rho2': i,a,b=args; return I(Q(i,I(a,b)),I(Q(i,a),Q(i,b)))
    if rule=='rho6': i,a=args; return I(Ex(i,Q(i,a)),a)
    if rule=='G': a,b,c=args; return I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b))))
    if rule=='Q_stability': i,a=args; return I(NN(Q(i,a)),Q(i,a))
    if rule=='bundle':
        a,b,c=args
        assert c==['max_plus_one',a,b]
        core=Q(c,I(clos(a,b,c,c),N(req(b,c,c))))
        return N(I(I(R(a,b),Q(c,R(a,b))),core))
    raise AssertionError(rule)
freeze=json.loads((P/'freeze.json').read_text())
bound=freeze['files']+freeze['history']+freeze['canonical_bindings']+[freeze['submitted_supplement']]
for d in bound: assert desc(Path(d['path']))==d
dag=json.loads((P/'proof-dag.json').read_text()); nodes=dag['nodes']
for k,n in enumerate(nodes):
    r=n['rule']; ps=n['parents']; opened=set(n['open'])
    assert all(type(p) is int and 0<=p<k for p in ps)
    if r=='hyp':
        assert not ps and n['args']==[k] and opened=={k}
    elif r=='mp':
        assert len(ps)==2 and not n['args']
        major,minor=(nodes[p] for p in ps)
        assert major['formula']==I(minor['formula'],n['formula'])
        assert opened==set(major['open'])|set(minor['open'])
    elif r=='gen':
        assert len(ps)==1 and len(n['args'])==1
        parent=nodes[ps[0]]
        assert not opened and not parent['open']
        assert n['formula']==Q(n['args'][0],parent['formula'])
    else:
        assert not ps and not opened
        assert n['formula']==primitive(r,n['args'])
result=json.loads((P/'result.json').read_text())
assert result['nodes']==len(nodes)==2134
assert len(dag['outputs'])==len(result['outputs'])==18
for name,index in dag['outputs'].items():
    assert not nodes[index]['open']
    assert result['outputs'][name]=={'node':index,'formula':nodes[index]['formula'],'closed':True}
stdout=json.loads((P/'run2.stdout.log').read_text())
assert stdout['nodes']==2134 and stdout['outputs']==18
assert not (P/'run2.stderr.log').read_text()
rec={'status':'INDEPENDENT_INERT_PROOF_DAG_READ_PASS','findings':[],
     'nodes':2134,'closed_outputs':18,'bound_descriptors':len(bound),
     'checks':'Every stored primitive axiom, exact bundle transcription/gate, MP edge, open-assumption union, closed-only GEN edge, and reported output checked without executing the author checker.',
     'scope':'Finite schematic evidence only; arbitrary-code induction and bidirectional calibration independently reviewed in prose. No Lean/Rocq, simulation, compiler, or source-size claim.',
     'reviewer_source':desc(Path(__file__)), 'author_freeze':desc(P/'freeze.json')}
(OUT/'static-review.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps(rec,indent=2))
