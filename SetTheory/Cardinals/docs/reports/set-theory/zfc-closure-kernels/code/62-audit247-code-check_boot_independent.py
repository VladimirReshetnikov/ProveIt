#!/usr/bin/env python3
"""Independent literal construction, graph audit and dense blank-tape replay.

This is a finite audit, not a proof of the unbounded runtime or ZFC calibration.
The accompanying results/independent-proof-review.md specifies the transfer argument.
"""
from pathlib import Path
import argparse,hashlib,json,sys,time

EXPECTED_SOURCE_SHA='fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43'

def parse(raw):
    table={}
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            start=int(line[9:]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert (q,b)not in table and d in ('L','R') and b in (0,1) and w in(0,1)
        table[q,b]=(w,d,t)
    return table,start

def encode(table,start):
    return ('#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {d} {t}\n' for(q,b),(w,d,t)in sorted(table.items()))).encode('ascii')

def audit(source250,candidate_old,candidate_canonical,output):
    began=time.monotonic();raw=source250.read_bytes();assert hashlib.sha256(raw).hexdigest()==EXPECTED_SOURCE_SHA
    old,start=parse(raw);assert start==97
    incoming={str(t):[[q,b]for(q,b),(w,d,u)in sorted(old.items())if u==t]for t in(0,1,3)}
    assert incoming=={'0':[[60,0]],'1':[[0,0],[1,1],[3,1]],'3':[[1,0]]}
    assert old[0,1]==old[20,1]==(0,'L',2)
    table={k:v for k,v in old.items()if k[0]not in(0,1,3)}
    table[60,0]=(0,'R',20)
    states={q for q,b in table}
    assert len(states)==247 and len(table)==494
    assert set(table)=={(q,b)for q in states for b in(0,1)}
    assert {t for w,d,t in table.values()}-states=={254}
    assert [(q,b)for(q,b),(w,d,t)in table.items()if t==254]==[(77,1)]
    skip=[60,44,31,56,38,40,28,64,69]
    for r,state in enumerate(skip):
        assert table[state,1]==(1,'R',state)
        assert table[state,0]==(0,'R',20 if r==0 else skip[r-1])
    assert table[20,1]==(0,'L',2)
    reachable=set();pending=[97]
    while pending:
        q=pending.pop()
        if q==254 or q in reachable:continue
        reachable.add(q);pending.extend(table[q,b][2]for b in(0,1))
    assert reachable==states
    # Largest exact state bisimulation: partition by write/move/next-class.
    part={q:0 for q in states};part[254]=1
    while True:
        signatures={q:tuple((table[q,b][0],table[q,b][1],part[table[q,b][2]])for b in(0,1))for q in states}
        keys={k:i for i,k in enumerate(sorted(set(signatures.values())))}
        newer={q:keys[signatures[q]]for q in states};newer[254]=len(keys)
        if all((part[q]==part[r])==(newer[q]==newer[r])for q in states for r in states):break
        part=newer
    classes=len(set(newer[q]for q in states))
    assert classes==247
    oldbytes=encode(table,97)
    order=[97]+sorted(states-{97});m={q:i for i,q in enumerate(order)}
    canonical={(m[q],b):(w,d,247 if t==254 else m[t])for(q,b),(w,d,t)in table.items()}
    canonbytes=encode(canonical,0)
    assert candidate_old.read_bytes()==oldbytes,'Candidate old-label table differs from the one-row construction'
    assert candidate_canonical.read_bytes()==canonbytes,'Candidate canonical table differs from the canonical construction'
    actual_table,actual_start=parse(candidate_old.read_bytes())
    assert actual_start==97 and actual_table==table
    # Distinct dense representation. One extra cell outside every possible path
    # keeps absolute signed coordinates explicit throughout literal execution.
    endpoint_time=741241
    origin=endpoint_time+1
    tape=bytearray(2*endpoint_time+3)
    q=97;head=origin
    visited_rows=set();initial_97_0_count=0
    for clock in range(endpoint_time):
        assert q in states,(clock,q)
        bit=tape[head];visited_rows.add((q,bit))
        initial_97_0_count+=(q==97 and bit==0)
        w,d,q=actual_table[q,bit]
        tape[head]=w
        head+=1 if d=='R' else -1
    assert q==96 and head-origin==-5
    assert initial_97_0_count==1
    ones=[i-origin for i,b in enumerate(tape)if b]
    assert ones[0]==-6 and ones[1]==245
    assert [p for p in ones if p<head-origin]==[head-origin-1]
    assert all(tape[i]==0 for i in range(head,origin+245))
    header=245;cursor=origin+header+1;last=origin+ones[-1];values=[]
    while cursor<=last:
        assert tape[cursor]==0
        cursor+=1;n=0
        while cursor<=last and tape[cursor]:cursor+=1;n+=1
        assert n>=1;values.append(n-1)
    assert values[:9]==[0,0,0,3,0,0,3,0,0]
    assert len(values)>=10 and all(v==1 for v in values[9:])
    expected_ones=sorted({-6,245,247,249,251,253,254,255,256,258,260,262,263,264,265,267,269}
                         |{271+3*j for j in range(235)}|{272+3*j for j in range(235)})
    assert ones==expected_ones
    # Repaint *all* cells from the declared frame; compare entire dense tape.
    rebuilt=bytearray(len(tape));rebuilt[head-1]=rebuilt[origin+header]=1;cursor=origin+header+1
    for v in values:
        cursor+=1
        for _ in range(v+1):rebuilt[cursor]=1;cursor+=1
    assert rebuilt==tape
    physmap=[6,2,0,4,3,7,8,5,1]
    logical=[values[i]for i in physmap]
    # All recurrent entries to97 read1, by the complete incoming-edge identity.
    assert [(q,b)for(q,b),(w,d,t)in table.items()if t==97]==[(255,0)]
    assert [(q,b)for(q,b),(w,d,t)in table.items()if t==255]==[(75,0)]
    assert table[75,0]==(1,'R',255) and table[255,0]==(1,'L',97)
    assert table[97,1]==(1,'L',131)
    result={'status':'PASS finite independent literal audit',
        'source250_sha256':EXPECTED_SOURCE_SHA,
        'old247_sha256':hashlib.sha256(oldbytes).hexdigest(),
        'canonical247_sha256':hashlib.sha256(canonbytes).hexdigest(),
        'states':247,'rows':494,'canonical_start':0,'canonical_halt':247,'canonical_dispatch':m[96],
        'graph_reachable_working_states':len(reachable),
        'ordinary_exact_bisimulation_classes':classes,
        'removed_states':[0,1,3],'source250_legacy_incoming':incoming,
        'patch':{'60,0':[0,'R',20]},
        'marking_support':{'skip_states_by_physical_index':skip,'all_skip_read1_rows_are_preserving_right_selfloops':True,
            'all_skip_read0_rows_follow_preceding_index':True,'old0_read1_equals_retained20_read1':[0,'L',2]},
        'blank_endpoint':{'literal_steps':endpoint_time,'old_state':q,'canonical_state':m[q],'head':head-origin,'marker':head-origin-1,
            'header':header,'gap':header-(head-origin),'physical_primary':values[:9],
            'logical_primary':logical,'spares_count':len(values)-9,'spares_all_value_one':True,
            'one_count':len(ones),'rightmost_one':ones[-1],'whole_one_positions':ones,'all_other_cells_zero':True},
        'initial97_read0_visits':initial_97_0_count,
        'visited_transition_count':len(visited_rows),
        'elapsed_seconds':time.monotonic()-began,
        'limits':['No new proof-assistant theorem or ZFC calibration is established by this finite audit.',
                  'Ordinary exact bisimulation does not supply a minimal-state lower bound.']}
    # The audit variable q was reused in graph edge comprehensions (which do not
    # escape in Python3), so it still denotes the literal endpoint state96.
    assert result['blank_endpoint']['old_state']==96
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='blank_endpoint'},indent=2))
    print(json.dumps({k:v for k,v in result['blank_endpoint'].items()if k!='whole_one_positions'},indent=2))

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must be enabled')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source250',type=Path,required=True)
    parser.add_argument('--candidate-old',type=Path,required=True)
    parser.add_argument('--candidate-canonical',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    audit(args.source250,args.candidate_old,args.candidate_canonical,args.output)
