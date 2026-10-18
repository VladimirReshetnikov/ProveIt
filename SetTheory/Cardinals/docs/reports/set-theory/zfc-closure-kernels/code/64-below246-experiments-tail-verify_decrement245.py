#!/usr/bin/env python3
"""Universal decrement lemmas for an INCOMPLETE 245-state table.

This table does not satisfy the inherited increment contract. It is not a
claimed smaller consistency machine. The ordinary symbolic-induction rules
are supplied by the separately audited context246 package.
"""
from pathlib import Path
import argparse
import importlib
import json
import os
import sys


def main():
    package_root=Path(__file__).resolve().parents[2]
    default_base=package_root/'baseline/context246'
    if not default_base.exists():
        default_base=package_root/'context246/zfc-context246'
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base',type=Path,default=Path(os.environ.get('ZFC246_BASE',default_base)))
    ap.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
    args=ap.parse_args()
    if not __debug__:
        raise SystemExit('Assertions must be enabled.')
    sys.dont_write_bytecode=True
    sys.path.insert(0,str(args.base.resolve()/'code'))
    m=importlib.import_module('check_macro_inductions')
    table=m.build()
    table[75,0]=(0,'L',112)
    del table[255,0]
    del table[255,1]
    states={q for q,b in table}
    assert len(states)==245 and len(table)==490
    assert all(q in states or q==254 for w,d,q in table.values())
    m.TABLE=table
    m.prove_blocks()
    word=m.prove_word_identity()

    a=m.Blocks('B','prefix')
    p=m.E.var('width_prefix')
    x=m.E.var('positive_value_minus_one')
    y=m.E.var('following_value')
    left=m.Context('arbitrary_left_exterior')
    right=m.Context('arbitrary_right_exterior')
    positive=m.prove('positive_decrement245',
        m.Conf(95,'R',[left],[a,m.bit(0),m.bit(0),m.ones(x+1),right]),
        m.Conf(48,'L',[m.bit(1),left],[a]+m.B(x)+[right]),
        2*p+4,m.E(),allow_lists=True)
    following=m.B(y)+[right]
    zero=m.prove('zero_decrement245',
        m.Conf(95,'R',[left],[a,m.bit(0),m.bit(0)]+following),
        m.Conf(112,'L',[left],[a]+m.B(m.E())+following),
        2*p+5,m.E(-1),allow_lists=True)

    # Smallest valid local example: selected zero and one zero-valued spare.
    # The left exterior has just the ordinary header one at -1.
    q,h,ones=73,0,{-1,3}
    trace=[]
    snapshots=[dict(step=0,state=q,head=h,ones=sorted(ones))]
    for step in range(1,100):
        read=int(h in ones);w,d,nq=table[q,read]
        before=dict(step=step,state=q,head=h,read=read,write=w,direction=d,next_state=nq)
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1;q=nq
        before.update(after_head=h,after_ones=sorted(ones))
        trace.append(before)
        snapshots.append(dict(step=step,state=q,head=h,ones=sorted(ones)))
        if q==48:
            break
    else:
        raise AssertionError('Expected the explicit first return to state48.')
    expected=dict(state=48,head=-1,ones=[-1,1,2,4,6,7],steps=15)
    assert snapshots[15]==dict(step=15,state=131,head=-3,ones=[-2,0,1,3,5])
    assert snapshots[-1]==dict(step=16,state=48,head=-4,ones=[-2,0,1,3,5])
    counterexample=dict(
        selected_index=0,registers_including_spare=[0,0],initial_header=-1,
        initial_state=73,initial_head=0,initial_ones=[-1,3],
        intended_increment_values=[1,0,1],expected=expected,
        actual_at_intended_time=snapshots[15],
        actual_first_return_to_state48=snapshots[-1],trace=trace,
        claim='The inherited increment contract fails; this does not assert a blanket nonexistence theorem for every redesigned increment contract.')
    out=args.output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
    (out/'decrement245_partial.tm').write_text('#! start 95\n'+''.join(
        f'{q} {b} {w} {d} {nq}\n' for (q,b),(w,d,nq) in sorted(table.items())))
    data=dict(status='PARTIAL_RESULT',working_states=245,binary_transitions=490,
        only_changed_surviving_row=[75,0,0,'L',112],removed_state=255,
        ordinary_induction_checker=True,new_proof_assistant_endpoint=False,
        inherited_block_inductions=list(m.BLOCK_PROOFS.values()),word_identity=word,
        positive_decrement=positive,zero_decrement=zero,increment_counterexample=counterexample)
    (out/'decrement245-proof-and-counterexample.json').write_text(json.dumps(data,indent=2)+'\n')
    columns=['step','state','head','read','write','direction','next_state','after_head','after_ones']
    rows=['\t'.join(columns)]+['\t'.join(str(row[k]) for k in columns)for row in trace]
    (out/'decrement245-increment-counterexample.tsv').write_text('\n'.join(rows)+'\n')
    print(json.dumps({'status':data['status'],'states':len(states),
        'positive_steps':positive['steps'],'zero_steps':zero['steps'],
        'arbitrary_left_and_right_exteriors':True,
        'increment_expected':expected,'increment_first_return':snapshots[-1]},indent=2))


if __name__=='__main__':
    main()
