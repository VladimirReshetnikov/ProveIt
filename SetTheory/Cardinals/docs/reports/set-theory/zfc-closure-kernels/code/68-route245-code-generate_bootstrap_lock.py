#!/usr/bin/env python3
"""Derive bootstrap grammar locks by two independent exact tape interpreters."""
from collections import Counter
import hashlib
import json
from pathlib import Path

from audit_routing_grammar import BASE, INPUTS, TABLE

STEPS = 410735


def main():
    source = json.loads((INPUTS/'closed-sequence-grammar-next22.json').read_text())
    symbols = json.loads((INPUTS/'semantic-symbols.json').read_text())
    encode = {v:k for k,v in symbols.items()}
    names = {int(q):''.join(encode[x] for x in w) for q,w in source['flattened_semantic_words'].items()}
    seq = set(source['sequence_states'])
    grammar = {}
    for line in (INPUTS/'semantic.txt').read_text().splitlines()[1:128]:
        split, word, q = line.split()
        grammar[word] = word[:int(split)], word[int(split):]
    table = {}
    for line in TABLE.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q,b,w,d,t = line.split()
        table[int(q),int(b)] = int(w),d,int(t)
    routes = {}
    for c in source['left_entry_projection_constraints']:
        r = c['reason']
        prefix = str(r['previous'])+c['prefix'] if 'via' in r else c['prefix']
        routes[r['source'],r['read'],r['previous']] = prefix
    # Sparse interpreter, with local routing blocks marked separately.
    q,head,ones = 95,0,set()
    used, outside, routed = Counter(),Counter(),Counter()
    pending = 0
    scanner_blocks = 0
    for _ in range(STEPS):
        bit = int(head in ones)
        used[q,bit] += 1
        if (q,bit)==(58,0):
            assert head-1 not in ones and head-2 not in ones
            scanner_blocks += 1
        interior = pending > 0
        if interior:
            pending -= 1
        else:
            outside[q,bit] += 1
            key = q,bit,int(head-1 in ones)
            if key in routes:
                routed[key] += 1
                pending = len(routes[key])
        write,direction,q = table[q,bit]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction=='R' else -1
    assert pending==0
    # Dense interpreter: array-indexed rows, array tape, integer displacement.
    rows = [None] * (2*(1+max(q for q,b in table)))
    for (state,bit),(write,direction,target) in table.items():
        rows[2*state+bit] = write,1 if direction=='R' else -1,target
    tape = bytearray(2*STEPS+3)
    origin = STEPS+1
    position,state = origin,95
    dense_used = [0]*len(rows)
    for _ in range(STEPS):
        index = 2*state+tape[position]
        dense_used[index] += 1
        write,displacement,state = rows[index]
        tape[position] = write
        position += displacement
    dense_ones = [i-origin for i,bit in enumerate(tape) if bit]
    dense_counts = Counter({(i//2,i%2):n for i,n in enumerate(dense_used) if n})
    assert (state,position-origin,dense_ones)==(q,head,sorted(ones))
    assert dense_counts==used
    assert q==96 and head==-5 and len(ones)==351
    cached = json.loads((BASE/'reference/context246/results/bootstrap.json').read_text())['old_labels']
    assert sorted(ones)==cached['all_one_positions']
    assert [[s,b,n] for (s,b),n in sorted(used.items())]==cached['used_rows']
    assert scanner_blocks==used[74,0]==1410 and used[74,1]==0
    assert table[58,0]==(0,'L',74) and table[74,0]==(0,'L',84) and table[84,0]==(0,'R',84)
    short_rows=rows.copy()
    short_rows[2*58]=(0,-1,84)
    short_rows[2*74]=short_rows[2*74+1]=None
    short_steps=STEPS-2*scanner_blocks
    short_tape=bytearray(2*short_steps+3)
    short_origin=short_steps+1
    short_position,short_state=short_origin,95
    for _ in range(short_steps):
        write,displacement,short_state=short_rows[2*short_state+short_tape[short_position]]
        short_tape[short_position]=write
        short_position+=displacement
    short_ones=[i-short_origin for i,bit in enumerate(short_tape) if bit]
    assert (short_state,short_position-short_origin,short_ones)==(q,head,sorted(ones))

    def constraints(counts):
        return [dict(root=s,word=names[s],bit=b,target_word=grammar[names[s]][b],
                     original_target=table[s,b][2],occurrences=n)
                for (s,b),n in sorted(counts.items()) if s in seq]

    full,block_aware = constraints(used),constraints(outside)
    assert len(full)==55 and len(block_aware)==54
    assert {(c['root'],c['bit']) for c in full} - {(c['root'],c['bit']) for c in block_aware} == {(89,1)}
    out = dict(status='EXACT_FINITE_BASELINE_BOOT_LOCK',
               baseline_table_sha256=hashlib.sha256(TABLE.read_bytes()).hexdigest(),
               blank_steps=STEPS, independent_sparse_dense_exact_agreement=True,
               sparse_dense_used_row_counters_identical=True,
               sequence_rows=len(full),sequence_states=len({c['root'] for c in full}),
               constraints=full,block_aware_sequence_rows=len(block_aware),
               block_aware_sequence_states=len({c['root'] for c in block_aware}),
               block_aware_constraints=block_aware,
               routed_contexts=[dict(source=s,read=b,previous=p,prefix=routes[s,b,p],occurrences=n)
                                for (s,b,p),n in sorted(routed.items())],
               short_scanner_boot=dict(status='PASS_EXACT_FINITE_REPLAY',removed_state=74,
                                       patched_row=[58,0,0,'L',84],
                                       old_three_step_block=[[58,0],[74,0],[84,0]],
                                       old_block_steps=3,new_block_steps=1,occurrences=scanner_blocks,
                                       each_block_reads_three_zero_cells=True,
                                       expected_blank_steps=short_steps,
                                       dense_replay_endpoint_equals_baseline=True),
               expected_dispatcher=96,expected_head=-5,
               expected_one_positions=sorted(ones),
               proof_scope='Freeze the selected immediate projections with retained old-word labels; certified same-length rerouting blocks may replace caller rows. The 54-row version omits sequence-row occurrences internal to those blocks. Both preserve the exact endpoint after410735steps.')
    target=BASE/'replay/bootstrap_lock.json'
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('constraints','block_aware_constraints','expected_one_positions')},indent=2))


if __name__=='__main__':
    main()
