#!/usr/bin/env python3
"""Deterministically construct K220 from the pinned K221 delivery.

Two closed source reassociations, literal decoder re-encoding, and one
contextual state identification. No optimizer or discovery search is run.
Full primitive runtime and exact blank startup are separate required checks.
"""
from pathlib import Path
import argparse, hashlib, json, sys

BASE_TABLE = 'e6dc479f09ded05dd1c0639b60a0c453483f42e6b77c29562d433cac528c1ecc'
BASE_SOURCE = '691684ec948c972bf67727d6d4cd1181a90a9203644ee3db3eae363280e3fac9'
FINAL_TABLE = '4466ec4f947a9c5112397c30ca25b0e70e3ac39ee54878b3e4493a0297d732e4'
FINAL_SOURCE = '837e92d7b1c107330f160f654f6c36ff0b03dfbf6bc2b89c6f782eb7db4c4ce7'

def need(x, message):
    if not x: raise ValueError(message)

def sha(raw): return hashlib.sha256(raw).hexdigest()

def dump(path, obj): path.write_text(json.dumps(obj, indent=2, sort_keys=True)+'\n')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args=ap.parse_args()
    need(__debug__ and not sys.flags.optimize, 'Run without Python -O')
    base=args.baseline.resolve(); out=args.output.resolve(); out.mkdir(parents=True, exist_ok=True)
    sys.path.insert(0, str(base/'portable'))
    import source_language as s
    import build221 as b
    raw=(base/'machine/k221.native.tm').read_bytes()
    source=(base/'machine/sites221.json').read_bytes()
    need(sha(raw)==BASE_TABLE and sha(source)==BASE_SOURCE, 'Pinned K221 inputs differ')
    original=b.read_table(raw); table=dict(original)
    rows=json.loads(source); tree=s.tree(rows); original_tree=tree
    original_graph,nchecks=s.graph_arithmetic(rows)
    need(original_graph==s.graph_intervals(rows), 'Baseline CFG resolvers disagree')
    original_word=[r[1:] for r in rows]
    original_groups,_=b.decoder_map(table,tree)
    stages=[]
    recipes=[
        ('11101001001101', 'right', [52,27,295],
         {(132,0):(0,1,90), (132,1):(1,1,202),
          (203,0):(0,1,147), (203,1):(1,1,132)}),
        ('111010010011011', 'left', [27,52,243],
         {(132,0):(0,1,202), (132,1):(1,1,201),
          (202,0):(0,1,90), (202,1):(1,1,149)})]
    for number,(path,direction,sizes,patch) in enumerate(recipes,1):
        n=s.subtree(tree,path)
        if direction=='right':
            need(not s.leaf(n[0]), 'Missing left pair')
            A,B=n[0]; C=n[1]; replacement=(A,(B,C))
        else:
            need(not s.leaf(n[1]), 'Missing right pair')
            A=n[0]; B,C=n[1]; replacement=((A,B),C)
        components=[A,B,C]
        need([len(s.sites(x)) for x in components]==sizes, 'Unexpected rotation components')
        need(all(s.boundary(x)==(0,0,False) for x in components), 'Rotation is not closed')
        old_table=dict(table); tree=s.replace(tree,path,replacement); table.update(patch)
        rr=s.sites(tree); graph,checks=s.graph_arithmetic(rr)
        need(graph==original_graph==s.graph_intervals(rr), 'Complete guarded CFG changed')
        need([r[1:] for r in rr]==original_word, 'Primitive word changed')
        groups,paths=b.decoder_map(table,tree)
        need(len(table)==442, 'A reassociation changed the state census')
        (out/f'stage{number}.native.tm').write_bytes(b.table_bytes(table))
        (out/f'stage{number}.sites.json').write_bytes(s.compact(rr))
        stages.append(dict(number=number,path=path,direction=direction,
            component_leaf_counts=sizes,component_boundaries=[s.boundary(x) for x in components],
            patch=[list(k)+list(v) for k,v in sorted(patch.items())],
            table_sha256=sha(b.table_bytes(table)),source_sha256=sha(s.compact(rr)),
            source_metrics=s.metrics(tree),source_location_checks=checks,
            guarded_successor_checks=checks-1,initial_leaf_checks=1,
            decoder_states=len(groups),decoder_aliases=sum(len(v)-1 for v in groups.values()),
            complete_primitive_word_preserved=True,complete_guarded_CFG_preserved=True))
    prefold=dict(table)
    (out/'prefold.tm').write_bytes(b.table_bytes(prefold))
    old_groups,paths=b.decoder_map(prefold,tree)
    need(prefold[171,0]==(0,1,183) and prefold[202,0]==(0,1,90), 'Unexpected folded zero rows')
    need(prefold[171,1]==prefold[202,1]==(1,1,149), 'Folded one rows differ')
    need(all(p.endswith('1') for p in paths[171]), 'Wrong decoder prefix at 171')
    need(all(p.endswith('0') for p in paths[202]), 'Wrong decoder prefix at 202')
    phi=lambda q:171 if q==202 else q
    table={(q,c):(w,d,phi(z)) for (q,c),(w,d,z) in prefold.items() if q!=202}
    table[171,0]=(0,-1,7)
    # These blocks quantify over the whole untouched exterior tape. Their tag
    # premises are proved here at SOURCE DECODER entries only. They are not an
    # invariant for arbitrary machine entries into 171. The separate full
    # primitive proof checks every use inside arithmetic as well.
    blocks=[]
    for q,tag in ((171,1),(202,0)):
        for read in (0,1):
            tape={-1:tag,0:read}; initial=dict(tape); state=171; head=0; trace=[]
            steps=3 if read==0 else 1
            for _ in range(steps):
                need(head in tape and state!=254, 'Block reads exterior or halts internally')
                bit=tape[head]; w,d,z=table[state,bit]
                trace.append([state,head,bit,w,d,z]); tape[head]=w; head+=d; state=z
            w,d,z=prefold[q,read]; expected=dict(initial); expected[0]=w
            need((state,head,tape)==(phi(z),d,expected), 'Fold block does not commute')
            blocks.append(dict(old_state=q,read=read,previous_bit=tag,steps=steps,
                trace=trace,endpoint=[state,head],entire_exterior_untouched=True))
    final_rows=s.sites(tree); final_raw=b.table_bytes(table); final_source=s.compact(final_rows)
    need(sha(final_raw)==FINAL_TABLE and sha(final_source)==FINAL_SOURCE, 'Final byte identity differs')
    states={q for q,c in table}
    need(len(states)==220 and len(table)==440 and set(table)=={(q,c) for q in states for c in (0,1)}, 'Final state/row census')
    need({z for w,d,z in table.values()}-states=={254}, 'Unexpected terminal')
    reached={0}; todo=[0]
    for q in todo:
        for bit in (0,1):
            z=table[q,bit][2]
            if z!=254 and z not in reached: reached.add(z); todo.append(z)
    need(reached==states, 'Unreachable working state in transition graph')
    groups,final_paths=b.decoder_map(table,tree)
    need(len(groups)==171 and sum(len(v) for v in groups.values())==185, 'Final decoder role census')
    need(len(states-set(groups))==49, 'Final nondecoder state census')
    need(s.metrics(tree)==s.metrics(original_tree), 'Unexpected source metrics')
    (out/'candidate.tm').write_bytes(final_raw); (out/'sites.json').write_bytes(final_source)
    allocation=[dict(state=q,subtree_sha256=sha(s.compact(n)),leaf_count=len(s.sites(n)))
                for q,ns in sorted(groups.items()) for n in sorted(ns,key=lambda n:sha(s.compact(n)))]
    dump(out/'allocation.json',allocation)
    changes=[dict(state=q,read=c,old=list(original[q,c]),new=list(v))
             for (q,c),v in sorted(table.items()) if original[q,c]!=v]
    need(len(changes)==5 and states=={q for q,c in original}-{202}, 'Unexpected final delta')
    receipt=dict(status='DETERMINISTIC_K220_SOURCE_AND_DECODER_CONSTRUCTION_PASS',
        baseline_native_sha256=BASE_TABLE,baseline_source_sha256=BASE_SOURCE,
        native_sha256=FINAL_TABLE,source_sha256=FINAL_SOURCE,
        source_metrics=s.metrics(tree),source_word_sha256=sha(s.compact(original_word)),
        guarded_CFG_sha256=sha(s.compact(original_graph)),guarded_cases=sum(2 if r[1]=='CD' else 1 for r in rows),
        stages=stages,working_states=220,transition_rows=440,start=0,dispatcher=84,halt=254,
        decoder_states=171,interior_roles=185,shared_decoder_roles=14,nondecoder_states=49,
        final_changed_rows=changes,deleted_state=202,
        fold=dict(keep=171,drop=202,helper=7,decoder_prefixes={str(q):paths[q] for q in (171,202)},blocks=blocks,
            scope='Whole-tape local blocks at decoder entries satisfying the previous-bit premises; not an arbitrary-initial-tape simulation theorem.'),
        proof_boundary='Unchanged calibrated primitive word and guarded CFG. The final unbounded primitive runtime and complete blank startup are separately required. No new proof-assistant kernel endpoint.')
    dump(out/'construction.json',receipt)
    print(json.dumps({k:receipt[k] for k in ('status','working_states','transition_rows','native_sha256','source_sha256','source_metrics')},indent=2))

if __name__=='__main__': main()
