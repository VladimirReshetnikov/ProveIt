#!/usr/bin/env python3
"""Reproduce the new composed 246-state control and its ordinary certificates.

No third-party Python packages or compiler are required. This is a mathematical
certificate checker, not a proof-assistant endpoint. Imported checker sources
remain byte-identical and are identified in sources/import_manifest.json.
"""
from __future__ import annotations
from pathlib import Path
from collections import Counter
import sys,json,hashlib,time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'vendor/code'))
import rebuild_machines as rebuild
import prefix_affine as affine
import check_macro_inductions as macro
from verify_reassociation import Decoder,read_json,read_literal

EXPECTED='29377d9d8abc876187cb3fdac430f9dc92999802a848c0c2403874763214951f'
PHYSICAL=(6,2,0,4,3,7,8,5,1)
ROTATION={(178,0):(0,'R',16),(178,1):(1,'R',206),
          (208,0):(0,'R',23),(208,1):(1,'R',70),
          (218,0):(0,'R',105),(237,0):(0,'R',208)}
DETECTOR={(13,1):(1,'R',19),(19,0):(0,'L',58),(19,1):(1,'R',19),
          (29,1):(1,'R',29),(41,0):(0,'L',74),(58,0):(0,'L',29),
          (58,1):(1,'R',6),(74,0):(0,'R',84)}

class Tracked(dict):
    def __init__(self,table):super().__init__(table);self.used=set()
    def __getitem__(self,key):self.used.add(key);return super().__getitem__(key)

def expected_ones():
    ones={-6,176};p=177
    for value in [0,0,0,3,0,0,3,0,0]+[1]*167:
        p+=1
        for _ in range(value+1):ones.add(p);p+=1
    assert len(ones)==351 and p==702
    return ones

def sparse(table,start,steps):
    state,head,ones=start,0,set();lo=hi=0;used=Counter()
    for _ in range(steps):
        symbol=int(head in ones);used[state,symbol]+=1
        w,d,state=table[state,symbol]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=1 if d=='R' else -1;lo=min(lo,head);hi=max(hi,head)
    return state,head,ones,(lo,hi),used

def dense(table,start,steps):
    origin=steps+1;tape=bytearray(2*steps+3);head=origin;state=start
    for _ in range(steps):
        w,d,state=table[state,tape[head]];tape[head]=w
        head+=1 if d=='R' else -1
    return state,head-origin,{i-origin for i,bit in enumerate(tape) if bit}

def instructions(table,source):
    tracked=Tracked({(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in table.items()})
    counts=Counter();rule_counts=Counter();minimum=10**9
    for pc,edge in source.sites:
        op=edge[0];arg=edge[1] if len(edge)==2 else None
        physical=PHYSICAL[arg] if op in ('I','D') else arg
        for zero in ((True,False) if op=='D' else (None,)):
            branch=(physical,zero) if op=='D' else None
            extra=0;effect=None;overflow=False
            if op=='I' or (op=='D' and not zero):
                after=Decoder.increment(pc);overflow=all(c=='1' for c in pc)
                effect=('inc' if op=='I' else 'dec',physical)
                extra=int(op=='D')
            elif op=='D':
                stripped=Decoder.strip(pc,'0',1);after=Decoder.increment(stripped)
                overflow=all(c=='1' for c in stripped)
            elif op=='B':
                stripped=Decoder.strip(pc,'0',arg);after=Decoder.increment(stripped)
                overflow=all(c=='1' for c in stripped)
            elif op=='C':after=Decoder.strip(pc,'1',arg)
            else:assert op=='H';after=''
            gap=40+extra+int(overflow)-len(after);assert gap>=0
            target=affine.canon([('b',1)],[('b',int(c)) for c in after]+[
                ('r',0,1,gap),('b',1),('box',('plain',effect))])
            rules,steps=affine.run(tracked,pc,branch,target,halt=op=='H',fuel=1500)
            assert steps>0
            counts[op+('/zero' if zero else '/positive') if op=='D' else op]+=1
            rule_counts.update(rules);minimum=min(minimum,steps)
    assert sum(counts.values())==8391
    return {'guarded_cases':sum(counts.values()),'by_operation':dict(counts),
            'minimum_literal_steps':minimum,'rule_counts':dict(rule_counts)},\
           {(int(q),b) for q,b in tracked.used}

def main():
    assert __debug__,'Python assertions are required; do not use -O.'
    began=time.monotonic()
    manifest=json.loads((ROOT/'sources/import_manifest.json').read_text())
    for filename,record in manifest.items():
        assert hashlib.sha256((ROOT/filename).read_bytes()).hexdigest()==record['sha256'],filename
    baseline=rebuild.build();assert not ROTATION.keys()&DETECTOR.keys()
    table={**baseline,**ROTATION,**DETECTOR}
    raw=rebuild.encode(table,95).encode('ascii')
    assert hashlib.sha256(raw).hexdigest()==EXPECTED
    assert raw==(ROOT/'machine/zfc_composed246_old.tm').read_bytes()
    states={q for q,b in table}
    assert len(states)==246 and set(table)=={(q,b) for q in states for b in (0,1)}
    assert {s for w,d,s in table.values()}-states=={254}
    assert [k for k,v in table.items() if v[2]==254]==[(77,1)]
    assert table[77,1]==(1,'R',254)

    n,nroot,_=read_json(ROOT/'sources/rotated202.json')
    o,oroot,_=read_json(ROOT/'sources/original203.json')
    l,lroot=read_literal(ROOT/'vendor/sources/Prog254.v')
    new,old,literal=Decoder(n,nroot),Decoder(o,oroot),Decoder(l,lroot)
    assert new.graph()==old.graph()
    assert new.normal(('N',nroot))==old.normal(('N',oroot))
    assert old.tree(('N',oroot))==literal.tree(('N',lroot))
    assert len(n)==202 and len(new.sites)==6460

    mt=Tracked(table);macro.TABLE=mt
    macro.DERIVED.clear();macro.BLOCK_PROOFS.clear();macro.WORD_IDENTITY_PROVED=False
    macro.prove_blocks();macro.prove_word_identity();macro.prove_macros();macro.prove_marks()
    support=mt.used;assert len(support)==42
    assert all(table[k]==baseline[k] for k in support)
    instruction_report,usage=instructions(table,new)
    assert support|usage==set(table)

    steps=409449
    q,h,ones,head_interval,used=sparse(table,95,steps)
    assert (q,h,ones)==(96,-5,expected_ones())
    assert dense(table,95,steps)==(q,h,ones)
    labels=[95]+sorted(states-{95});rename={q:i for i,q in enumerate(labels)}|{254:246}
    canonical={(rename[q],b):(w,d,rename[t]) for (q,b),(w,d,t) in table.items()}
    canonical_bytes=rebuild.encode(canonical,0).encode('ascii')
    assert set(canonical)=={(q,b) for q in range(246) for b in (0,1)}
    assert dense(canonical,0,steps)==(rename[96],h,ones)
    reached=set();todo=[0]
    while todo:
        state=todo.pop()
        if state in reached:continue
        reached.add(state)
        if state!=246:todo.extend(canonical[state,b][2] for b in (0,1))
    assert reached==set(range(247))
    (ROOT/'machine/zfc_composed246.tm').write_bytes(canonical_bytes)
    mapping={'canonical_to_old':labels,'old_to_canonical':rename,
             'start_old':95,'start_canonical':0,'dispatch_old':96,'dispatch_canonical':rename[96],
             'halt_old':254,'halt_canonical':246}
    (ROOT/'machine/renumbering.json').write_text(json.dumps(mapping,indent=2)+'\n')
    boot={'steps':steps,'state_old':q,'state_canonical':rename[q],'head':h,
          'marker':-6,'header':176,'program_counter':'','header_distance':181,
          'logical_registers':[3,0,0,0,3,0,0,0,0],
          'physical_registers':[0,0,0,3,0,0,3,0,0],
          'spares':[1]*167,'one_positions':sorted(ones),'all_other_cells_zero':True,
          'head_interval_visited':head_interval,'transition_usage':[[q,b,c] for (q,b),c in sorted(used.items())],
          'independent_representations':['sparse set','dense byte array'],
          'canonical_dense_replay':True}
    (ROOT/'results/bootstrap.json').write_text(json.dumps(boot,indent=2)+'\n')
    result={'status':'PASS','working_states':246,'transition_rows':492,
            'old_table_sha256':EXPECTED,'canonical_table_sha256':hashlib.sha256(canonical_bytes).hexdigest(),
            'exact_source_guarded_cfg_equal':True,'ordered_source_normal_forms_equal':True,
            'literal_original_source_tree_equal':True,'source_leaves':6460,'source_dag_nodes':202,
            'protected_macro_support_rows':42,'all_492_rows_covered':True,
            'instructions':instruction_report,'blank_steps':steps,'exact_blank_one_cells':len(ones),
            'sparse_dense_equal_entire_tape':True,'canonical_dense_replay_equal':True,
            'all_working_states_graph_reachable':True,
            'scope':'Ordinary mathematical certificates; no new Lean or PA endpoint and no sub246 claim.',
            'seconds':time.monotonic()-began}
    (ROOT/'results/verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
