#!/usr/bin/env python3
"""Negative controls for actual premises of the source-independent tag fold."""
from pathlib import Path
import argparse,json,tempfile
import check_tagged_fold as proof


def encode(t):
    return '#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for(q,b),(w,d,z) in sorted(t.items()))


def transformed(t):
    r={(q,b):(w,d,proof.rename(z)) for(q,b),(w,d,z) in t.items() if q!=507}
    r[182,0]=(0,-1,209)
    return r


def main():
    ap=argparse.ArgumentParser();ap.add_argument('old',type=Path);ap.add_argument('new',type=Path);ap.add_argument('--output',type=Path)
    a=ap.parse_args();proof.check(a.old,a.new)
    old,states=proof.read(a.old);new,_=proof.read(a.new);results=[]
    with tempfile.TemporaryDirectory(prefix='tag-fold-controls-') as td:
        op,np=Path(td)/'old.tm',Path(td)/'new.tm'
        def check_case(name,ot,nt):
            op.write_text(ot);np.write_text(nt)
            try:proof.check(op,np)
            except ValueError as ex:results.append({'control':name,'status':'REJECTED','reason':str(ex)})
            else:raise RuntimeError('invalid premise accepted: '+name)
        check_case('incorrect_initial_state',encode(old).replace('#! start 0','#! start 507'),encode(new))
        t=dict(old);t[173,1]=(0,1,182)
        check_case('original_predecessor_writes_wrong_tag',encode(t),encode(transformed(t)))
        t=dict(old);t[18,0]=(1,1,507)
        check_case('clone_predecessor_writes_wrong_tag',encode(t),encode(transformed(t)))
        t=dict(old);t[0,0]=(0,1,182)
        check_case('extra_predecessor_breaks_tag',encode(t),encode(transformed(t)))
        t=dict(new);t[182,0]=(0,1,209)
        check_case('tag_reader_moves_wrong_direction',encode(old),encode(t))
        # Mutate BOTH tables consistently, so the exact-transformation check
        # still passes; only the semantic local block proof can reject these.
        t=dict(old);t[133,0]=(0,1,90)
        check_case('reused_tag_one_route_has_wrong_endpoint',encode(t),encode(transformed(t)))
        t=dict(old);t[157,0]=(0,-1,254)
        check_case('reused_tag_zero_route_halts_interior',encode(t),encode(transformed(t)))
        for name,predicate in [
            ('omit_original_tag_invariant',lambda q,h,t:q!=507 or t[h-1]==0),
            ('omit_clone_tag_invariant',lambda q,h,t:q!=182 or t[h-1]==1),
            ('omit_both_tag_invariants',lambda q,h,t:True)]:
            try:proof.local_certificate(old,new,states,predicate)
            except ValueError as ex:results.append({'control':name,'status':'REJECTED','reason':str(ex)})
            else:raise RuntimeError('invalid local invariant accepted: '+name)
    report={'status':'ALL_TAG_FOLD_PREMISE_MUTATIONS_REJECTED','count':len(results),'controls':results,
            'scope':'Mutation controls for initialization, predecessor tags, routing, unknown continuation endpoints, premature interior halt, and invariant hypotheses. They supplement the positive finite local proof certificate.'}
    text=json.dumps(report,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
