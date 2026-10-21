#!/usr/bin/env python3
"""Finite Hilbert certificates for fresh-code persistence alternatives.

The proof-building/deduction routines are the repository's attributed
k218-quantifier-stability checker; the new schema and endpoint derivations
are defined here. validate_certificate is a separate rule reader.
No native consistency or machine-size claim is inferred from finite tests.
"""
from pathlib import Path
import json,hashlib
import upstream_quantifier_checker as h
I,Q,R,E,N,NN,Ex=h.I,h.Q,h.R,h.E,h.N,h.NN,h.Ex
original_axiom=h.ax_formula

def axiom(name,args):
    if name=='self_vacuity':
        a,=args;return I(a,Q(a,a))
    if name=='weak_self_vacuity':
        a,=args;return NN(I(a,Q(a,a)))
    if name=='introspection':
        i,a=args;return I(Q(i,a),Q(i,Q(i,a)))
    return original_axiom(name,args)
h.ax_formula=axiom

def validate_certificate(nodes,outputs):
    """Read the serialized proof with independently written MP/GEN/ded rules."""
    def tuplify(x):return tuple(map(tuplify,x)) if isinstance(x,list) else x
    nodes=tuplify(nodes)
    for k,node in enumerate(nodes):
        name=node['rule'];form=tuplify(node['formula']);args=tuplify(node['args'])
        parents=node['parents'];opened=set(node['open'])
        assert all(isinstance(p,int) and 0<=p<k for p in parents)
        if name=='hyp':
            assert not parents and opened=={k} and args==(k,)
        elif name=='mp':
            assert len(parents)==2
            major,minor=(nodes[p]for p in parents)
            assert tuplify(major['formula'])==I(tuplify(minor['formula']),form)
            assert opened==set(major['open'])|set(minor['open'])
        elif name=='gen':
            assert len(parents)==1 and not opened and not nodes[parents[0]]['open']
            assert form==Q(args[0],tuplify(nodes[parents[0]]['formula']))
        else:
            assert name in {'K','S','rho1','rho2','rho6','self_vacuity','weak_self_vacuity','introspection'}
            assert not parents and not opened and form==axiom(name,args)
    assert all(not nodes[v]['open']for v in outputs.values())
    return True

def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled; do not use python -O.')
    a,b,c,u,i=map(h.P,('A','B','C','U','i'));out={}
    out['positive_self_vacuity_implies_DNE']=h.persistence_stable(a,a,h.double(h.ax('self_vacuity',a)))
    out['weak_self_vacuity_implies_DNE']=h.persistence_stable(a,a,h.ax('weak_self_vacuity',a))
    out['introspection_implies_quantifier_DNE']=h.persistence_stable(Q(i,a),i,h.double(h.ax('introspection',i,a)))
    sc=h.persistence_stable(c,c,h.double(h.ax('self_vacuity',c)))
    out['self_vacuity_recovers_unrestricted_rho8']=h.full_L(a,b,c,u,sc)
    wc=h.persistence_stable(c,c,h.ax('weak_self_vacuity',c))
    out['weak_self_vacuity_recovers_unrestricted_rho8']=h.full_L(a,b,c,u,wc)
    assert h.form(out['positive_self_vacuity_implies_DNE'])==I(NN(a),a)
    assert h.form(out['weak_self_vacuity_implies_DNE'])==I(NN(a),a)
    assert h.form(out['introspection_implies_quantifier_DNE'])==I(NN(Q(i,a)),Q(i,a))
    assert all(not h.nodes[p]['open']for p in out.values()) and h.validate()
    nodes=[{**n,'open':sorted(n['open'])}for n in h.nodes]
    proof={'nodes':nodes,'outputs':out}
    raw=json.dumps(proof,separators=(',',':')).encode()+b'\n'
    reloaded=json.loads(raw);assert validate_certificate(reloaded['nodes'],reloaded['outputs'])
    dst=Path(__file__).parent
    (dst/'self_vacuity_proof_dag.json').write_bytes(raw)
    def ancestors(p,seen=None):
        if seen is None:seen=set()
        if p in seen:return seen
        seen.add(p)
        for q in nodes[p]['parents']:ancestors(q,seen)
        return seen
    receipt={'status':'FINITE_HILBERT_RULE_REPLAY_PASS','nodes':len(nodes),'proof_bytes':len(raw),'proof_sha256':hashlib.sha256(raw).hexdigest(),
      'outputs':{k:{'node':p,'formula':h.form(p),'closed':True,'axiom_schemas':sorted({nodes[j]['rule']for j in ancestors(p)}-{'hyp','mp','gen'})}for k,p in out.items()},
      'scope':'Finite schematic derivations from K/S, rho1/rho2/rho6 and the named added persistence schema; no source/runtime/startup certificate.'}
    (dst/'self_vacuity_proof_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'nodes':len(nodes),'bytes':len(raw),'outputs':len(out)}))
if __name__=='__main__':main()
