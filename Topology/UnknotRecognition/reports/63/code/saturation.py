"""Deletion-only research saturation and a source-bound positive braid probe."""
from words import braid_presentation, difference_basis, cyclic_reduce, ResourceLimit
from donors import extract
from power_graph import infer
from source_checker import verify_braid

def saturate(relators,vertices,*,modular=True):
    """Conditional presentation transformer, NOT an arbitrary-group verdict.

    Sound group interpretation requires verified classical-knot provenance.
    The outer probe supplies it; users must not treat this local return as a
    standalone claim of group isomorphism or unknot recognition.
    """
    roots=[cyclic_reduce(w) for w in relators]; alive=set(vertices); rounds=[]
    counts=[]
    while True:
        edges,proofs=extract(roots)
        out=infer(sorted(alive),edges,modular=modular)
        counts.append({'letters':sum(map(len,roots)),'vertices':len(alive),'edges':len(edges),**out['stats']})
        if not out['killed']: break
        graph={k:out[k] for k in ('killed','witnesses')}
        rounds.append({'donors':proofs,'graph':graph})
        dead=set(out['killed']); alive-=dead
        roots=[cyclic_reduce(x for x in w if abs(x) not in dead) for w in roots]
    return roots,sorted(alive),rounds,counts

def probe_braid(strands,braid,*,modular=True,letter_cap=200_000):
    try:
        rels=difference_basis(braid_presentation(strands,braid,letter_cap=letter_cap),strands)
        if sum(map(len,rels))>letter_cap: raise ResourceLimit('difference-basis allowance')
        roots,alive,rounds,counts=saturate(rels,range(1,strands+1),modular=modular)
        proof={'version':1,'basis':'right-differences','rounds':rounds,
               'terminal':{'kind':'rank-one','generator':strands}}
        if alive==[strands] and all(not w for w in roots) and verify_braid(strands,braid,proof,letter_cap=letter_cap):
            return {'status':'UNKNOT','certificate':proof,'counts':counts}
        return {'status':'INCONCLUSIVE','counts':counts,'remaining_generators':alive}
    except ResourceLimit as e:
        return {'status':'RESOURCE_LIMIT','reason':str(e)}
