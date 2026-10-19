#!/usr/bin/env python3
"""Check the two-counter criterion against independent literal local paths."""
from pathlib import Path
import json,hashlib
import exact_reassociate as R

HERE=Path(__file__).resolve().parent
tested=accepted=closed=0;witnesses=[]
for n in sorted(R.live(R.ROOT)):
    x=R.S[n]
    if isinstance(x[0],str):continue
    candidates=[]
    a,bc=x
    if isinstance(R.S[bc][0],int):
        b,c=R.S[bc];candidates.append(('L',a,b,c,R.cons(R.cons(a,b),c)))
    ab,c=x
    if isinstance(R.S[ab][0],int):
        a,b=R.S[ab];candidates.append(('R',a,b,c,R.cons(a,R.cons(b,c))))
    for direction,a,b,c,alt in candidates:
        expected=R.boundary(a)[0]==R.boundary(c)[1]==0
        old=R.signature_by_paths(n);new=R.signature_by_paths(alt)
        assert (old==new)==expected,(n,direction,a,b,c)
        tested+=1;accepted+=expected;closed+=expected and all(map(R.closed,(a,b,c)))
        if not expected and len(witnesses)<6:
            i=next(i for i,(x,y) in enumerate(zip(old,new)) if x!=y)
            witnesses.append(dict(node=n,direction=direction,chunks=[a,b,c],leaf_ordinal=i,old_local_path=R.paths(n)[i][0],new_local_path=R.paths(alt)[i][0],old=old[i],new=new[i],A_escaping_break=R.boundary(a)[0],C_escaping_continue=R.boundary(c)[1]))

# Explicit necessity witnesses independent of any particulars of this source.
def atom(op,arg):
    key=(op,arg)
    if key not in R.I:R.I[key]=len(R.S);R.S.append(key)
    return R.I[key]
ia=atom('CI',0);ib=atom('CI',1);dd=atom('CD',5);cc=atom('CC',1);hh=atom('CH',None)
examples=[]
for label,a,b,c,valid in [('middle_decrement_is_allowed',ia,dd,ib,True),('middle_halt_is_allowed',ia,hh,ib,True),('escaping_break_in_A_changes_target',dd,ia,ib,False),('escaping_continue_in_C_changes_target',ia,ib,cc,False)]:
    p=R.cons(a,R.cons(b,c));q=R.cons(R.cons(a,b),c)
    old=R.signature_by_paths(p);new=R.signature_by_paths(q)
    assert (old==new)==valid
    examples.append(dict(label=label,valid=valid,left=old,right=new))

result=dict(status='LITERAL_LOCAL_CONTROL_SIGNATURES_PASS',criterion='z(A)=0 and o(C)=0',tested_rotations=tested,accepted_rotations=accepted,accepted_under_prior_all_closed_rule=closed,additional_admissible_rotations=accepted-closed,rejected_witnesses=witnesses,explicit_examples=examples,input_sha256=hashlib.sha256((HERE/'boundary_source_input.json').read_bytes()).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),signature_engine_sha256=hashlib.sha256((HERE/'exact_reassociate.py').read_bytes()).hexdigest(),scope='Finite verification of the criterion on every single rotation of the exact inherited source; the general lemma is proved in boundary_associativity.tex.')
(HERE/'associativity_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('rejected_witnesses','explicit_examples')},indent=2))
