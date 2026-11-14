#!/usr/bin/env python3
"""Mutate actual proof premises to check that the known-zero certificate rejects them."""
from pathlib import Path
import argparse, json, tempfile
import check_zero_fold as proof


def encode(T):
    return '#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(T.items()))


def quotient(T):
    return {(q,b):(w,d,proof.f(z)) for (q,b),(w,d,z) in T.items() if q != 200}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('old',type=Path);ap.add_argument('new',type=Path)
    ap.add_argument('--output',type=Path)
    a=ap.parse_args()
    proof.check(a.old,a.new)
    old, states = proof.table(a.old)
    new, _ = proof.table(a.new)
    receipts=[]
    with tempfile.TemporaryDirectory(prefix='u221-proof-controls-') as td:
        root=Path(td)
        def control(name, old_text, new_text):
            op,np=root/'old.tm',root/'new.tm'
            op.write_text(old_text);np.write_text(new_text)
            try:
                proof.check(op,np)
            except ValueError as e:
                receipts.append({'control':name,'status':'REJECTED','reason':str(e)})
            else:
                raise RuntimeError('unsound mutation was accepted: '+name)
        control('wrong_initial_state', encode(old).replace('#! start 0','#! start 200'), encode(new))
        control('missing_initial_state', encode(old).replace('#! start 0\n',''), encode(new))
        control('duplicate_initial_state', '#! start 0\n'+encode(old), encode(new))
        changed=dict(old);changed[172,0]=(1,-1,112)
        control('remove_zero_written_before_bounce',encode(changed),encode(quotient(changed)))
        changed=dict(old);changed[0,0]=(1,1,112)
        control('unexpected_predecessor_of_guard_state',encode(changed),encode(quotient(changed)))
        changed=dict(new);changed[112,1]=(1,1,119)
        control('incorrect_redirect_target',encode(old),encode(changed))
        control('negative_state',encode(old).replace('172 0 0 L 112','-172 0 0 L 112'),encode(new))
        control('negative_target',encode(old).replace('172 0 0 L 112','172 0 0 L -112'),encode(new))
        predicates=[
            ('omit_invariant_at_112',lambda q,h,t:q!=200 or t[h]==0),
            ('omit_invariant_at_200',lambda q,h,t:q!=112 or t[h+1]==0),
            ('omit_all_invariant_clauses',lambda q,h,t:True)]
        for name,p in predicates:
            try:
                proof.verify_local(old,new,states,p)
            except ValueError as e:
                receipts.append({'control':name,'status':'REJECTED','reason':str(e)})
            else:
                raise RuntimeError('unsound invariant omission was accepted: '+name)
    report={'status':'ALL_PROOF_PREMISE_MUTATIONS_REJECTED','controls':receipts,
            'count':len(receipts),'scope':'The controls mutate initial-state parsing, the two-row zero invariant, the quotient target, and state-domain validity. They do not establish the positive theorem; the local proof certificate does.'}
    s=json.dumps(report,indent=2)+'\n'
    if a.output:a.output.write_text(s)
    print(s,end='')

if __name__=='__main__':main()
