"""Sparse deterministic-TM rewriting with fixed state orientations.

This module is stdlib-only.  It emits symbolic rewrite rules, not an
arithmetic certificate.  The all-before default retains the old input word
and every original L/S rule.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random


def validate_tm(tape,transitions,accept):
    tape=tuple(tape)
    assert tape and len(set(tape))==len(tape) and '_' in tape
    assert not set(tape)&{'[',']','#'}
    states={accept}
    for (state,read),(target,write,direction) in transitions.items():
        assert state!=accept and read in tape and write in tape and direction in ('L','R','S')
        states.update((state,target))
    assert not states&(set(tape)|{'[',']','#'})
    return tape,states


def orientation_map(states,orientations=None):
    supplied={} if orientations is None else dict(orientations)
    assert set(supplied)<=set(states)
    assert all(v in ('before','after') for v in supplied.values())
    return {state:supplied.get(state,'before') for state in states}


def right_repair_states(transitions,accept,orientations=None):
    states={accept}|{state for state,_ in transitions}|{target for target,_,_ in transitions.values()}
    orientation=orientation_map(states,orientations)
    return tuple(sorted({target for target,_,direction in transitions.values()
                         if direction=='R' and target!=accept and orientation[target]=='before'}))


def left_repair_states(transitions,accept,orientations=None):
    states={accept}|{state for state,_ in transitions}|{target for target,_,_ in transitions.values()}
    orientation=orientation_map(states,orientations)
    return tuple(sorted({target for target,_,direction in transitions.values()
                         if direction=='L' and target!=accept and orientation[target]=='after'}))


def rewriting_rules_sparse(tape,transitions,accept,orientations=None):
    """Return tuple((upper_word,lower_word),...), matching the old rule API.

    Default all-before has local right moves and shared right repairs.
    An after-state sits just after its scanned cell and permits local left
    moves with shared left repairs. Other orientations retain one neighbor.
    """
    tape,states=validate_tm(tape,transitions,accept);rules=[]
    orientation=orientation_map(states,orientations)
    for (state,read),(target,write,direction) in sorted(transitions.items()):
        pair=(state,read) if orientation[state]=='before' else (read,state)
        if direction=='R' and orientation[target]=='before':rules.append((pair,(write,target)))
        elif direction=='L' and orientation[target]=='after':rules.append((pair,(target,write)))
        elif direction=='R':
            rules += [(pair+(c,),(write,c,target)) for c in tape]
            rules.append((pair+(']',),(write,'_',target,']')))
        elif direction=='L':
            rules += [((c,)+pair,(target,c,write)) for c in tape]
            rules.append((('[',)+pair,('[',target,'_',write)))
        else:rules.append((pair,(target,write) if orientation[target]=='before' else (write,target)))
    rules += [((state,']'),(state,'_',']')) for state in right_repair_states(transitions,accept,orientation)]
    rules += [(('[',state),('[','_',state)) for state in left_repair_states(transitions,accept,orientation)]
    rules += [((accept,a),(accept,)) for a in tape]
    rules += [((a,accept),(accept,)) for a in tape]
    assert len(set(rules))==len(rules)
    return tuple(rules)


def original_rules(tape,transitions,accept):
    """Independent literal reference to the context-enumerated construction."""
    tape,_=validate_tm(tape,transitions,accept);rules=[]
    for (state,read),(target,write,direction) in sorted(transitions.items()):
        if direction=='R':
            rules += [((state,read,c),(write,target,c)) for c in tape]
            rules.append(((state,read,']'),(write,target,'_',']')))
        elif direction=='L':
            rules += [((c,state,read),(target,c,write)) for c in tape]
            rules.append((('[',state,read),('[',target,'_',write)))
        else:rules.append(((state,read),(target,write)))
    rules += [((accept,a),(accept,)) for a in tape]
    rules += [((a,accept),(accept,)) for a in tape]
    return tuple(rules)


def successors(word,rules):
    return [(i,p,word[:p]+right+word[p+len(left):])
            for i,(left,right) in enumerate(rules)
            for p in range(len(word)-len(left)+1) if word[p:p+len(left)]==left]


def state_position(word,tape,states):
    assert word[0]=='[' and word[-1]==']' and word.count('[')==word.count(']')==1
    places=[i for i,c in enumerate(word) if c in states];assert len(places)==1
    pos=places[0]
    assert all(c in tape for c in word[1:pos]+word[pos+1:-1])
    return pos,word[pos]


def pending_side(word,tape,states,orientations=None):
    pos,state=state_position(word,tape,states);orientation=orientation_map(states,orientations)
    if orientation[state]=='before' and pos==len(word)-2:return 'R'
    if orientation[state]=='after' and pos==1:return 'L'
    return None


def normalize_configuration(word,tape,states,orientations=None):
    """Fill a missing scanned blank, including virtual normalization at halt.

    At nonaccepting pending states the generated repair performs this exact
    change. At acceptance it is only a semantic comparison operation.
    """
    side=pending_side(word,tape,states,orientations)
    if side=='R':return word[:-1]+('_',']')
    if side=='L':return ('[','_')+word[1:]
    return word


def configuration(word,tape,states,orientations=None):
    assert pending_side(word,tape,states,orientations) is None
    pos,state=state_position(word,tape,states);orientation=orientation_map(states,orientations)
    if orientation[state]=='before':return word[1:pos],state,word[pos+1:-1]
    return word[1:pos-1],state,(word[pos-1],)+word[pos+1:-1]


def encode_configuration(left,state,right,orientations=None):
    """Encode the semantic left tape, state, and nonempty scanned/right tape."""
    assert right
    orientation=(orientations or {}).get(state,'before');assert orientation in ('before','after')
    if orientation=='before':return ('[',)+tuple(left)+(state,)+tuple(right)+(']',)
    return ('[',)+tuple(left)+(right[0],state)+tuple(right[1:])+(']',)


def reference_step(word,tape,transitions,accept,orientations=None):
    """Direct bounded tape action; does not inspect either rewrite list."""
    _,states=validate_tm(tape,transitions,accept)
    left,state,right=configuration(word,tape,states,orientations)
    if state==accept or (state,right[0]) not in transitions:return None
    target,write,direction=transitions[state,right[0]]
    if direction=='S':return encode_configuration(left,target,(write,)+right[1:],orientations)
    if direction=='R':return encode_configuration(left+(write,),target,right[1:] or ('_',),orientations)
    if left:return encode_configuration(left[:-1],target,(left[-1],write)+right[1:],orientations)
    return encode_configuration((),target,('_',write)+right[1:],orientations)


def normalized_macro_step(word,tape,transitions,accept,orientations=None):
    """One sparse transition, plus its forced nonaccepting repair if any.

    At acceptance only, returned normalization may add an implicit blank
    for comparison with the reference. That is not a sparse repair rule.
    """
    _,states=validate_tm(tape,transitions,accept);rules=rewriting_rules_sparse(tape,transitions,accept,orientations)
    left,state,right=configuration(word,tape,states,orientations);assert state!=accept and right
    following=successors(word,rules);expected=reference_step(word,tape,transitions,accept,orientations)
    if expected is None:assert not following;return None,[]
    assert len(following)==1
    path=[following[0]];result=path[-1][2]
    _,s=state_position(result,tape,states);side=pending_side(result,tape,states,orientations)
    if side:
        assert transitions[state,right[0]][2]==side
        if s==accept:
            assert all(rules[i][0][0]==accept or rules[i][0][-1]==accept
                       for i,_,_ in successors(result,rules))
            assert normalize_configuration(result,tape,states,orientations)==expected
            return expected,path
        repair=successors(result,rules);assert len(repair)==1
        expected_repair=((s,']'),(s,'_',']')) if side=='R' else (('[',s),('[','_',s))
        assert rules[repair[0][0]]==expected_repair
        path+=repair;result=path[-1][2]
        assert pending_side(result,tape,states,orientations) is None
    assert result==expected
    return result,path


def cleanup_all(word,tape,accept):
    """Check every cleanup order from a bounded accepting configuration."""
    rules=rewriting_rules_sparse(tape,{},accept);pending=[word];seen=set()
    while pending:
        w=pending.pop()
        if w in seen:continue
        seen.add(w);nxt=successors(w,rules)
        if w==('[',accept,']'):assert not nxt;continue
        assert nxt and all(len(v)==len(w)-1 for _,_,v in nxt)
        pending += [v for _,_,v in nxt]
    return len(seen)


def run_check(tape,transitions,start,accept,left,right,limit,orientations=None):
    """Compare sparse runs with independent normalized tape transitions."""
    assert start!=accept and right
    word=encode_configuration(left,start,right,orientations)
    initial=word;steps=repairs=0;accepted=False
    _,states=validate_tm(tape,transitions,accept)
    assert start not in set(tape)|{'[',']','#'}
    if start not in states:
        # An isolated declared start has no instructions and cannot accept.
        assert not successors(word,rewriting_rules_sparse(tape,transitions,accept,
            {s:o for s,o in (orientations or {}).items() if s in states}))
        return dict(initial=list(initial),machine_steps=0,blank_repairs=0,
                    accepted=False,normalized_final=list(word),orientations=orientations or {})
    for _ in range(limit):
        new,path=normalized_macro_step(word,tape,transitions,accept,orientations)
        if new is None:break
        steps+=1;repairs+=len(path)-1;word=new
        if configuration(word,tape,validate_tm(tape,transitions,accept)[1],orientations)[1]==accept:
            accepted=True
            cleanup_all(path[-1][2],tape,accept)
            break
    return dict(initial=list(initial),machine_steps=steps,blank_repairs=repairs,
                accepted=accepted,normalized_final=list(word),orientations=orientations or {})


def ledger(tape,transitions,accept,orientations=None):
    rules=rewriting_rules_sparse(tape,transitions,accept,orientations);old=original_rules(tape,transitions,accept)
    directions=Counter(direction for _,_,direction in transitions.values())
    _,states=validate_tm(tape,transitions,accept);orientation=orientation_map(states,orientations)
    right=right_repair_states(transitions,accept,orientation);left=left_repair_states(transitions,accept,orientation)
    repairs=len(right)+len(left);p=len(tape)
    local=sum((direction=='R' and orientation[target]=='before') or
              (direction=='L' and orientation[target]=='after') for target,_,direction in transitions.values())
    contextual=directions['R']+directions['L']-local
    assert len(rules)==local+(p+1)*contextual+directions['S']+repairs+2*p
    assert len(old)-len(rules)==p*local-repairs
    return dict(tape_symbols=p,transitions=len(transitions),right_moves=directions['R'],
        left_moves=directions['L'],stationary_moves=directions['S'],
        local_moves=local,contextual_moves=contextual,
        right_repair_states=list(right),left_repair_states=list(left),
        original_rules=len(old),sparse_rules=len(rules),saved_rules=len(old)-len(rules))


def verify():
    rng=random.Random(729331);cases=cleanup=0;records=[];runs=[]
    for tape in (('_',),('0','_'),('0','1','_')):
      for direction in ('L','R','S'):
       for target in ('next','halt'):
        for read in tape:
         for write in tape:
          tm={('start',read):(target,write,direction)}
          for left in ((),(tape[0],),(tape[-1],tape[0])):
           for tail in ((),(tape[0],),(tape[-1],tape[0])):
            word=('[',)+left+('start',read)+tail+(']',)
            expected=reference_step(word,tape,tm,'halt')
            old=successors(word,original_rules(tape,tm,'halt'))
            assert len(old)==1 and old[0][2]==expected
            got,path=normalized_macro_step(word,tape,tm,'halt')
            assert got==expected;cases+=1
            if target=='halt':cleanup+=cleanup_all(path[-1][2],tape,'halt')
          records.append(ledger(tape,tm,'halt'))
    # Every source/target orientation, both tape boundaries, and acceptance.
    oriented_cases=0;oriented_ledgers=[]
    for tape in (('_',),('0','_'),('0','1','_')):
      for direction in ('L','R','S'):
       for target in ('next','halt'):
        for source_orientation in ('before','after'):
         for target_orientation in ('before','after'):
          orientation={'start':source_orientation,target:target_orientation}
          for read in tape:
           for write in tape:
            tm={('start',read):(target,write,direction)}
            for left in ((),(tape[0],),(tape[-1],tape[0])):
             for tail in ((),(tape[0],),(tape[-1],tape[0])):
              word=encode_configuration(left,'start',(read,)+tail,orientation)
              got,path=normalized_macro_step(word,tape,tm,'halt',orientation)
              before=encode_configuration(left,'start',(read,)+tail)
              reference=successors(before,original_rules(tape,tm,'halt'))
              assert len(reference)==1
              _,states=validate_tm(tape,tm,'halt')
              normalized=configuration(reference[0][2],tape,states)
              assert got==encode_configuration(*normalized,orientation)
              if target=='halt':cleanup_all(path[-1][2],tape,'halt')
              oriented_cases+=1
          oriented_ledgers.append(ledger(tape,tm,'halt',orientation))
    # Shared targets, partial transitions, loops, and all three directions.
    random_cases=0
    for trial in range(48):
        tape=('_','0','1')[:1+trial%3];states=('s','p','q')[:1+trial%3]
        tm={(s,a):(rng.choice(states+('halt',)),rng.choice(tape),rng.choice(('L','R','S')))
            for s in states for a in tape if rng.randrange(4)}
        actual_states=validate_tm(tape,tm,'halt')[1]
        orientation={s:rng.choice(('before','after')) for s in sorted(actual_states)}
        rules=rewriting_rules_sparse(tape,tm,'halt',orientation)
        for lhs,rhs in rules:
            assert sum(c in set(states)|{'halt'} for c in lhs)==sum(c in set(states)|{'halt'} for c in rhs)==1
            for w in (lhs,rhs):
                assert '[' not in w or w[0]=='['
                assert ']' not in w or w[-1]==']'
                assert '#' not in w
        for _ in range(8):
            state=rng.choice(states);right=tuple(rng.choice(tape) for _ in range(rng.randrange(1,8)))
            left=tuple(rng.choice(tape) for _ in range(rng.randrange(6)))
            # A state with no transitions/targets still belongs to the machine.
            if state not in validate_tm(tape,tm,'halt')[1]:continue
            runs.append(run_check(tape,tm,state,'halt',left,right,40,orientation));random_cases+=1
        records.append(ledger(tape,tm,'halt',orientation))
    scan={('s',a):('s',a,'R') for a in ('0','1')};scan['s','_']=('back','_','L')
    scan.update({('back',a):('back',a,'L') for a in ('0','1')});scan['back','_']=('halt','_','S')
    for n in (1,2,9,32,96):
        r=run_check(('0','1','_'),scan,'s','halt',(),tuple(('01'*n)[:n]),4*n+20)
        assert r['accepted'] and r['blank_repairs']==1;runs.append(r)
        r=run_check(('0','1','_'),scan,'s','halt',(),tuple(('01'*n)[:n]),4*n+20,{'back':'after'})
        assert r['accepted'] and r['blank_repairs']==2;runs.append(r)
    pending_reject={('s','0'):('dead','0','R')}
    r=run_check(('0','_'),pending_reject,'s','halt',(),('0',),4)
    assert not r['accepted'] and r['blank_repairs']==1 and r['machine_steps']==1;runs.append(r)
    pending_accept={('s','0'):('halt','0','R')}
    r=run_check(('0','_'),pending_accept,'s','halt',(),('0',),4)
    assert r['accepted'] and r['blank_repairs']==0;runs.append(r)
    forever={('s',a):('s',a,'R') for a in ('0','_')}
    r=run_check(('0','_'),forever,'s','halt',(),('0',),64)
    assert not r['accepted'] and r['blank_repairs']==64;runs.append(r)
    left_forever={('s',a):('s',a,'L') for a in ('0','_')}
    r=run_check(('0','_'),left_forever,'s','halt',(),('0',),64,{'s':'after'})
    assert not r['accepted'] and r['blank_repairs']==64;runs.append(r)
    left_reject={('s','0'):('dead','0','L')}
    r=run_check(('0','_'),left_reject,'s','halt',(),('0',),4,{'dead':'after'})
    assert not r['accepted'] and r['blank_repairs']==1;runs.append(r)
    left_accept={('s','0'):('halt','0','L')}
    r=run_check(('0','_'),left_accept,'s','halt',(),('0',),4,{'halt':'after'})
    assert r['accepted'] and r['blank_repairs']==0;runs.append(r)
    for orientation in ('before','after'):
        r=run_check(('_',),{},'isolated','halt',(),('_',),4,{'isolated':orientation})
        assert not r['accepted'] and r['machine_steps']==0;runs.append(r)
    sample={('s',a):('p',a,'R') for a in ('0','1','_')}
    sample.update({('p',a):('halt',a,'R') for a in ('0','1','_')})
    return dict(status='PASS_SPARSE_TM_ORIENTED_REPAIRS',local_transition_contexts=cases,
        oriented_transition_contexts=oriented_cases,oriented_ledgers=oriented_ledgers,
        accepting_cleanup_configurations=cleanup,random_bounded_runs=random_cases,
        ledgers=records,bounded_runs=runs,
        example=dict(ledger=ledger(('0','1','_'),sample,'halt'),
                     rules=rewriting_rules_sparse(('0','1','_'),sample,'halt')),
        scope='Exact accepting-run equivalence under fixed state orientations. Normalized initial words are unchanged in that representation; ordinary fixed-prefix input requires initial-state orientation before. Pending nonaccepting states force one blank repair on the missing scanned side; accepting pending states may clean up immediately. No arithmetic compiler count, universal bound or finite-test universality claim is made.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
