#!/usr/bin/env python3
"""Finite two-cell deletion/fold search on a fixed binary machine.

Includes asymmetric aliases with unchanged keeper rows, using either a known
left neighbor or known right neighbor inferred from ALL incoming rows. Also
includes contextual pair folds with one arbitrary new transition per keeper
branch and any finite excursion through unchanged controls on the two cells.
Pair-fold helper excursions may not re-enter either merged state except at the
required endpoint. Loops are rejected by exact finite configuration equality.
This is a bounded transformation family, not a general minimization result.
"""
import ast, hashlib, itertools, json, re, sys, time
from collections import Counter, defaultdict
from pathlib import Path
INPUT=Path(sys.argv[1])
OUT=Path(sys.argv[2]) if len(sys.argv)>2 else Path(__file__).resolve().parent
rows={}
for line in INPUT.read_text().splitlines():
    if not line or line.startswith('#'):continue
    q,r,w,d,n=line.split();rows[int(q),int(r)]=(int(w),1 if d=='R' else -1,int(n))
states=sorted({q for q,r in rows})
assert set(rows)=={(q,r) for q in states for r in (0,1)}
assert all(n in set(states)|{254} for w,d,n in rows.values())
incoming=defaultdict(set)
for (q,r),(w,d,n) in rows.items():incoming[n].add((w,d))
start=time.time();alias_trials=0;pair_trials=0;action_trials=0
aliases=[];folds=[];orientations={}

# For direction +1 the known preceding cell is -1; for -1 it is +1.
def simulate_alias(q,keeper,entry_direction,neighbor,read):
    neighborpos=-entry_direction
    tape={0:read,neighborpos:neighbor}
    w,d,n=rows[q,read]
    target=(keeper if n==q else n,d,w,neighbor)
    state,head=keeper,0;seen=set();length=0
    while True:
        if length and (state,head,tape[0],tape[neighborpos])==target:return length
        if head not in tape or state==254:return None
        key=(state,head,tape[0],tape[neighborpos])
        if key in seen:return None
        seen.add(key)
        w,d,n=rows[state,tape[head]]
        tape[head]=w;head+=d;state=keeper if n==q else n;length+=1

for direction in (1,-1):
    eligible=[q for q in states if q!=74 and incoming[q] and all(d==direction for w,d in incoming[q])]
    orientations[str(direction)]={'alias_deletable_controls':len(eligible)}
    for q in eligible:
        neighbors=sorted({w for w,d in incoming[q]})
        for keeper in states:
            if keeper==q:continue
            alias_trials+=1;lengths=[]
            for neighbor,read in itertools.product(neighbors,(0,1)):
                n=simulate_alias(q,keeper,direction,neighbor,read)
                if n is None:break
                lengths.append(n)
            else:aliases.append({'deleted':q,'keeper':keeper,'entry_direction':direction,'neighbor_bits':neighbors,'durations':lengths})
print('ASYMMETRIC_ALIASES',alias_trials,'survivors',len(aliases),'seconds',time.time()-start,flush=True)

# Initial transition may write either bit, move either way, and enter any
# existing control (including the endpoint halt). Thereafter both pair states
# are blocked until the target configuration; this yields nonrecursive helpers.
def branch_options(a,b,direction,read):
    global action_trials
    neighborpos=-direction
    targets=[]
    for q,neighbor in ((a,0),(b,1)):
        w,d,n=rows[q,read]
        targets.append((b if n==a else n,d,w,neighbor))
    opts=[]
    for write,move,nxt in itertools.product((0,1),(-1,1),states+[254]):
        if nxt==a:continue
        action_trials+=1;durations=[]
        for neighbor,target in enumerate(targets):
            tape={0:write,neighborpos:neighbor}
            state,head,length=nxt,move,1;seen=set()
            while (state,head,tape[0],tape[neighborpos])!=target:
                if head not in tape or state in (a,b,254):break
                key=(state,head,tape[0],tape[neighborpos])
                if key in seen:break
                seen.add(key)
                w,d,n=rows[state,tape[head]]
                tape[head]=w;head+=d;state=b if n==a else n;length+=1
            else:
                durations.append(length);continue
            break
        else:opts.append({'action':[write,move,nxt],'durations':durations})
    return opts

for direction in (1,-1):
    zeros=[q for q in states if q!=74 and incoming[q]=={(0,direction)}]
    ones=[q for q in states if q!=74 and incoming[q]=={(1,direction)}]
    orientations[str(direction)].update({'zero_context_controls':len(zeros),'one_context_controls':len(ones)})
    for a,b in itertools.product(zeros,ones):
        pair_trials+=1
        opt0=branch_options(a,b,direction,0)
        if not opt0:continue
        opt1=branch_options(a,b,direction,1)
        if opt1:folds.append({'deleted':a,'keeper':b,'entry_direction':direction,'zero_actions':opt0,'one_actions':opt1})
    print('PAIR_DIRECTION',direction,'total_pairs',pair_trials,'survivors',len(folds),'seconds',time.time()-start,flush=True)
receipt={'input':str(INPUT),'native_sha256':hashlib.sha256(INPUT.read_bytes()).hexdigest(),
         'working_controls':len(states),'all_controls_except_start_eligible':True,'orientations':orientations,
         'asymmetric_alias_trials':alias_trials,'contextual_pair_trials':pair_trials,'initial_branch_actions_tested':action_trials,
         'asymmetric_aliases':aliases,'contextual_pair_folds':folds,'exact_cycle_detection':True,'seconds':time.time()-start,
         'scope':'Two-cell aliases with unchanged keeper and two-cell contextual pair folds whose helpers do not revisit the merged states before the endpoint. Not a lower bound for arbitrary TMs.'}
(OUT/'two_cell_screen.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
