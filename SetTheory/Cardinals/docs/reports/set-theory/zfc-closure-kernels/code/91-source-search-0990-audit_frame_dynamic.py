#!/usr/bin/env python3
"""Independent dynamic audit of exact numbering, full pointers and blank frame.

No inherited source decoder, symbolic executor, path operation or simulator is
imported. Expected source/tree/case/state counts are derived from explicit data.
The sole fixed interface is the nine-register prefix engine's physical layout.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json

PHYSICAL=(6,2,0,4,3,7,8,5,1)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def read_table(path):
    t={};start=None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            assert start is None;start=int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,b,w,d,s=line.split();q,b,w,s=map(int,(q,b,w,s))
            assert b in(0,1)and w in(0,1)and d in('L','R')and(q,b)not in t
            t[q,b]=w,d,s
    states={q for q,b in t};assert start in states
    assert set(t)=={(q,b)for q in states for b in(0,1)}
    halt={s for w,d,s in t.values()}-states;assert len(halt)==1
    return t,start,states,next(iter(halt))

def validate_sites(data):
    assert isinstance(data,list)and data
    leaves={};trie={}
    for row in data:
        assert isinstance(row,list)and len(row)==3
        p,op,r=row
        assert isinstance(p,str)and p and set(p)<=set('01')
        assert op in('CI','CD','CB','CC','CH')
        assert (r is None)if op=='CH'else(type(r)is int and r>=0)
        if op in('CI','CD'):assert r in range(9)
        assert p not in leaves;leaves[p]=op,r;node=trie
        for b in p:
            assert 'leaf'not in node
            node=node.setdefault(b,{})
        assert not node;node['leaf']=True
    nodes=0
    def visit(node):
        nonlocal nodes
        assert set(node)=={'leaf'}or set(node)=={'0','1'}
        if 'leaf'not in node:nodes+=1;visit(node['0']);visit(node['1'])
    visit(trie);assert nodes==len(leaves)-1
    return leaves,nodes

def increment(word):
    width=len(word);number=int(word,2)if width else 0
    overflow=number+1==2**width;residue=(number+1)%(2**width)
    return (format(residue,f'0{width}b')if width else''),overflow

def strip(word,bit,count):
    if count==0:return word
    where=[i for i,b in enumerate(word)if b==bit]
    return word[:where[-count]]if len(where)>=count else''

def blank_replay(t,start,ticks):
    q=start;head=0;ones=set()
    for _ in range(ticks):
        w,d,q=t[q,int(head in ones)]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=1 if d=='R'else-1
    return q,head,sorted(ones)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--old-table',type=Path,required=True)
    ap.add_argument('--table',type=Path,required=True,help='Dense canonical table, start0 and working states0..n-1.')
    ap.add_argument('--renumbering',type=Path,required=True)
    ap.add_argument('--logical-sites',type=Path,required=True)
    ap.add_argument('--physical-sites',type=Path,required=True)
    ap.add_argument('--bootstrap',type=Path,required=True)
    ap.add_argument('--padding',type=int,default=64)
    ap.add_argument('--whole-frame-report',type=Path)
    ap.add_argument('--grammar',type=Path,help='Optional grammar whose word alphabet is already that of --locks.')
    ap.add_argument('--locks',type=Path,help='Optional direct word/bit/child lock projections; paired with --grammar.')
    ap.add_argument('--require-seed',help='Optional exact comma-separated logical seed.')
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();assert __debug__ and args.padding>=1
    assert bool(args.grammar)==bool(args.locks)
    old,old_start,old_states,old_halt=read_table(args.old_table)
    new,start,states,halt=read_table(args.table);n=len(states)
    assert states==set(range(n))and start==0 and halt==n
    ren=json.loads(args.renumbering.read_text())
    mapping={int(k):v for k,v in ren['old_to_canonical'].items()}
    order=ren['canonical_to_old']
    assert len(order)==n and len(set(order))==n and set(order)==old_states
    assert set(mapping)==old_states|{old_halt}and set(mapping.values())==set(range(n+1))
    assert all(type(v)is int for v in mapping.values())
    assert mapping[old_halt]==halt and mapping[old_start]==start
    assert all(mapping[q]==i for i,q in enumerate(order))
    assert {(mapping[q],b):(w,d,mapping[s])for(q,b),(w,d,s)in old.items()}==new
    logical=json.loads(args.logical_sites.read_text());physical=json.loads(args.physical_sites.read_text())
    leaves,nodes=validate_sites(logical);validate_sites(physical)
    assert physical==[[p,op,PHYSICAL[r]if op in('CI','CD')else r]for p,op,r in logical]
    maximum=max(map(len,leaves));assert maximum<=args.padding
    maxzero=max(len(run)for p in leaves for run in p.split('1'))
    def decode(word):
        p=''
        for i in range(maximum):
            p+=word[i]if i<len(word)else'0'
            if p in leaves:
                assert '1'not in word[len(p):],(word,p,'Nonzero ignored residual suffix.')
                return p
        raise AssertionError('No source leaf in complete finite tree.')
    cases=0;normalized=0;deltas=Counter();ops=Counter();min_gap=args.padding;overflows=0
    for p,op,r in logical:
        for zero in((True,False)if op=='CD'else(None,)):
            cases+=1;ops[op+('/zero'if zero else'/positive')if op=='CD'else op]+=1
            if op=='CH':continue
            extra=int(op=='CD'and not zero)
            if op=='CI'or(op=='CD'and not zero):q,overflow=increment(p)
            elif op=='CD':q,overflow=increment(strip(p,'0',1))
            elif op=='CB':q,overflow=increment(strip(p,'0',r))
            else:q,overflow=strip(p,'1',r),False
            delta=extra+int(overflow);following=decode(q)
            c=args.padding+delta-len(q);d=args.padding+delta-len(following)
            assert c>=0 and d>=0
            # Appending the same arbitrary n zeros proves equality at every
            # header distance >= padding, including overflow/trailing zeros.
            assert q+'0'*c==following+'0'*d
            min_gap=min(min_gap,c);deltas[delta]+=1;overflows+=int(overflow);normalized+=1
    assert cases==sum(2 if op=='CD'else 1 for p,op,r in logical)
    assert normalized==cases-sum(op=='CH'for p,op,r in logical)
    first=decode('');assert first+'0'*(args.padding-len(first))=='0'*args.padding
    boot=json.loads(args.bootstrap.read_text());ticks=boot.get('blank_steps',boot.get('steps'))
    assert type(ticks)is int and ticks>=0 and boot['start']==old_start and boot['dispatcher']==96
    assert boot.get('pc','')==''
    head=boot['head'];header=boot['header'];assert boot['marker']==head-1
    assert type(head)is int and type(header)is int and header-head>=args.padding
    assert boot['header_distance']==header-head
    regs=boot['physical_registers'];spares=boot['spare_values']
    assert len(regs)==9 and spares and all(type(v)is int and v>=0 for v in regs+spares)
    seed=[regs[i]for i in PHYSICAL];assert seed==boot['logical_registers']and all(seed[i]==0 for i in(1,2,5))
    if args.require_seed:assert seed==list(map(int,args.require_seed.split(',')))
    expected={head-1,header};position=header+1
    for value in regs+spares:
        position+=1;expected.update(range(position,position+value+1));position+=value+1
    ones=boot['all_one_positions'];assert ones==sorted(expected)and boot['one_count']==len(ones)
    assert boot['all_other_cells_zero']is True
    q,actual_head,actual_ones=blank_replay(old,old_start,ticks)
    assert(q,actual_head,actual_ones)==(96,head,ones)
    locks_count=0
    if args.grammar:
        g=json.loads(args.grammar.read_text());rules={w:(a,b)for w,a,b in g['rules']}
        assert len(rules)==len(g['rules'])and all(w==a+b for w,(a,b)in rules.items())
        lines=args.locks.read_text().splitlines();assert int(lines[0])==len(lines)-1
        for line in lines[1:]:
            w,b,t=line.split();assert b in('0','1')and rules[w][int(b)]==t;locks_count+=1
    linked=False
    if args.whole_frame_report:
        report=json.loads(args.whole_frame_report.read_text())
        assert report['status']=='PASS'and report['complete']is True and report['all_values']is True
        assert report['expected_cases']==report['counts']['cases']==cases
        assert report['table_sha256']==sha(args.old_table)and report['sites_sha256']==sha(args.physical_sites)
        assert report['frame_padding']==args.padding and report['positive_progress_checked']is True
        assert report['exact_table_macro_support']['status']=='PASS';linked=True
    inputs=dict(old_table=args.old_table,table=args.table,renumbering=args.renumbering,
        logical_sites=args.logical_sites,physical_sites=args.physical_sites,bootstrap=args.bootstrap)
    result=dict(status='PASS',working_states=n,binary_rows=len(new),start=start,halt=halt,
        old_start=old_start,old_halt=old_halt,source_leaves=len(logical),source_tree_nodes=nodes,
        guarded_cases=cases,nonhalting_successor_cases=normalized,case_counts=dict(ops),
        maximum_source_depth=maximum,maximum_source_zero_run=maxzero,frame_padding=args.padding,
        target_path_preserves_full_width=True,arbitrary_extra_gap_word_identity=True,
        residual_pointer_cases=normalized,overflow_cases=overflows,gap_deltas=dict(deltas),
        minimum_constant_gap=min_gap,nonempty_spare_suffix=True,optional_lock_projections=locks_count,
        exact_blank_replay_steps=ticks,logical_seed=seed,
        same_seed_as_routing245=seed==[3,0,0,0,3,0,0,0,0],complete_boot_one_cells=len(ones),
        all_other_boot_cells_zero=True,renumbering_exact=True,linked_all_values_whole_frame=linked,
        input_sha256={k:sha(v)for k,v in inputs.items()},audit_code_sha256=sha(Path(__file__)),
        scope='Independent finite arithmetic, complete-tape blank replay, state renumbering and universal residual-word identities. Source semantic/calculus correspondence is a separate proof obligation.')
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
