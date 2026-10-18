#!/usr/bin/env python3
"""Prove local identities for a nine-state carry core; prove its global failure.

This core is NOT a ZFC consistency machine. The unchanged control frame cannot
leave its left-moving SCC. The negative integration result is part of this
check, so the arithmetic identities cannot be mistaken for a machine result.
"""
import argparse
from pathlib import Path
import json
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if not __debug__:
        raise SystemExit('Run without -O: assertions are proof checks.')
    sys.path.insert(0, str(args.baseline.resolve() / 'code'))
    import check_macro_inductions as p
    table = p.TABLE.copy()
    del table[255,0]
    del table[255,1]
    table[75,0] = (0,'R',63)
    table[48,0] = (1,'L',131)
    assert all(t != 255 for w,d,t in table.values())
    p.TABLE = table
    p.prove_blocks()
    word = p.prove_word_identity()
    pre, suf = p.E.var('width_pre'), p.E.var('width_suf')
    x, y = p.E.var('x'), p.E.var('y')
    a, b = p.Blocks('B','pre'), p.Blocks('B','suf')
    left, blank = p.Context('arbitrary_left'), p.Blank()
    macros = []
    macros.append(p.prove('positive_decrement',
        p.Conf(95,'R',[left],[a,p.bit(0),p.bit(0),p.ones(x+1),b,blank]),
        p.Conf(48,'L',[p.bit(1),left],[a]+p.B(x)+[b,blank]),
        2*pre+4,p.E(),allow_lists=True))
    suffix = p.B(y)+[b,blank]
    # The old eager C(A)1 rewrite at every visit to48 obscures the new
    # intermediate rollback state. This proof needs no word-identity rewrite;
    # temporarily disable that optional normalization, retaining literal rules.
    p.WORD_IDENTITY_PROVED = False
    macros.append(p.prove('zero_decrement',
        p.Conf(95,'R',[left],[a,p.bit(0),p.bit(0)]+suffix),
        p.Conf(112,'L',[left],[a]+p.B(p.E())+suffix),
        2*pre+7,p.E(-1),allow_lists=True))
    p.WORD_IDENTITY_PROVED = True
    macros.append(p.prove('increment_append_zero',
        p.Conf(73,'R',[left],[a,p.bit(0),p.bit(0),p.ones(x),b,blank]),
        p.Conf(48,'L',[left],[a]+p.B(x+1)+[b]+p.B(p.E())+[blank]),
        2*(pre+x+suf+2)+7,p.E(-1),allow_lists=True))
    marks = p.prove_marks()
    trap = {48,63,112,131}
    assert all(table[q,bit][1]=='L' and table[q,bit][2] in trap
               for q in trap for bit in (0,1))
    head, state, ones, prefix = 0, 95, set(), []
    for step in range(3):
        bit = int(head in ones)
        write, direction, following = table[state,bit]
        prefix.append([state,head,bit,write,direction,following])
        if write: ones.add(head)
        else: ones.discard(head)
        head += 1 if direction=='R' else -1
        state = following
    assert state in trap and state != 254
    result = dict(status='PASS',
        result_kind='Universal local arithmetic identities plus a proved integration obstruction',
        zfc_consistency_machine=False,
        proof_assistant_endpoint=False,
        edits={'remove':[255], '75/0':[0,'R',63], '48/0':[1,'L',131]},
        working_table_states=len(table)//2,
        new_local_arithmetic_state_count=9,
        arithmetic_states=[48,63,73,75,83,95,109,112,131],
        block_theorems=list(p.BLOCK_PROOFS.values()), word_identity=word,
        macro_theorems=macros, mark_theorems=marks,
        closed_left_moving_states=sorted(trap),
        blank_prefix_enters_trap_after=3,
        blank_prefix=prefix,
        global_consequence='The modified table from state95 never halts, by induction on this closed SCC; it does not implement the proof-search program.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('block_theorems','macro_theorems','mark_theorems','word_identity')},indent=2))
    for proof in macros:
        print(proof['name'],proof['status'],proof['steps'])


if __name__=='__main__':
    main()
