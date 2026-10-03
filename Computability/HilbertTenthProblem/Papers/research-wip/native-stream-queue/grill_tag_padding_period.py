#!/usr/bin/env python3
"""Whole-period zero-padding theorem: exact prefix couplings and finite evidence."""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import types

SOURCE_SHA256='144129bb04e271588ed1c95d9c91f5682d30c6b5a540154c6c0b9b0c40331d96'

def need(ok,message):
    if not ok:raise ValueError(message)

def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def program_check(program):
    need(type(program) is tuple and program and all(type(n) is int and n>=0 for n in program),'nonempty exact natural program tuple')

def word_check(word):
    need(type(word) is str and set(word)<=set('01'),'binary word')

def step(program,state):
    program_check(program);phase,word=state;word_check(word)
    need(type(phase) is int and 0<=phase<len(program),'phase in program')
    if not word:return None
    rest=word[1:]
    if word[0]=='1':rest+='0'+'10'*program[phase]
    return ((phase+1)%len(program),rest)

def advance(program,state,steps):
    need(type(steps) is int and steps>=0,'natural step count')
    for _ in range(steps):
        state=step(program,state);need(state is not None,'no firing after halt')
    return state

def prefix_coupling(program,word,blocks,phase=0):
    program_check(program);word_check(word)
    need(type(blocks) is int and blocks>=0,'natural full-period blocks')
    need(type(phase) is int and 0<=phase<len(program),'initial phase')
    k=blocks*len(program);n=len(word)
    old=advance(program,(phase,word),n)
    middle=advance(program,(phase,word+'0'*k),n)
    appended=''.join('0'+'10'*program[(phase+i)%len(program)] for i,b in enumerate(word) if b=='1')
    need(old==((phase+n)%len(program),appended),'initial-word exhaustion')
    need(middle==(old[0],'0'*k+appended),'extra zeros precede all appendants')
    padded=advance(program,middle,k)
    need(padded==old,'exact post-initial-word configuration equality')
    return dict(initial_phase=phase,original_word=word,added_zeros=k,old_join_step=n,new_join_step=n+k,
                shared_phase=old[0],shared_queue=old[1])

def classify(program,word,*,phase=0,limit=400,word_limit=1024):
    program_check(program);word_check(word)
    need(type(phase) is int and 0<=phase<len(program),'initial phase')
    need(type(limit) is int and limit>=0 and type(word_limit) is int and word_limit>=1,'bounds')
    state=(phase,word);seen={};trace=[]
    for time in range(limit+1):
        p,w=state
        if not w:return dict(status='halt',first_halt=time,trace=trace,terminal_phase=p)
        if state in seen:
            return dict(status='cycle',entry=seen[state],period=time-seen[state],trace=trace,repeated_state=[p,w],repeat_step=time)
        if len(w)>word_limit:return dict(status='unresolved',reason='word_limit',checked_steps=time)
        if time==limit:return dict(status='unresolved',reason='step_limit',checked_steps=time)
        seen[state]=time;trace.append([time,p,w]);state=step(program,state)
    raise ValueError('unreachable')

def padded_word(x,length):
    need(type(x) is int and x>0 and type(length) is int and length>=x.bit_length(),'positive input and enough bits')
    return ''.join(str((x>>i)&1) for i in range(length))

def canonical_lengths(x,period,*,strong=True):
    need(type(x) is int and x>0 and type(period) is int and period>0 and type(strong) is bool,'canonical parameters')
    first=(3*x).bit_length() if strong else x.bit_length()
    return list(range(first,first+period))

def load_reference(path):
    data=path.read_bytes();need(hashlib.sha256(data).hexdigest()==SOURCE_SHA256,'frozen direct macro source')
    module=types.ModuleType('_padding_reference');module.__file__=str(path)
    exec(compile(data,str(path),'exec'),module.__dict__)
    return module

def verify(source):
    reference=load_reference(source);counts=Counter()
    programs=[p for m in range(1,5) for p in itertools.product(range(3),repeat=m)]
    words=[''.join(w) for n in range(6) for w in itertools.product('01',repeat=n)]
    for program in programs:
        for phase,word in itertools.product(range(len(program)),words):
            got=step(program,(phase,word));old=reference.macro(word,program[phase])
            need((None if got is None else got[1])==old,'pinned macro agreement');counts['literal_reference_steps']+=1
            for blocks in range(4):
                prefix_coupling(program,word,blocks,phase);counts['exact_prefix_couplings']+=1
    # Bounded classification only labels repeated full configurations as nonhalting.
    for program in programs[:39]:
        for x in range(1,17):
            for length in canonical_lengths(x,len(program)):
                word=padded_word(x,length);original=classify(program,word)
                counts['classified_canonical_runs']+=1
                if original['status']=='unresolved':
                    counts['unresolved_runs_not_classified_as_nonhalting']+=1;continue
                for blocks in (1,2):
                    k=blocks*len(program)
                    extended=classify(program,word+'0'*k,limit=400+k,word_limit=1024+k)
                    need(extended['status']==original['status'],'period padding preserves classified truth')
                    if original['status']=='halt':
                        need(extended['first_halt']==original['first_halt']+k,'exact first-halt delay')
                        counts['halting_time_shifts']+=1
                    else:
                        # Restore the exact original cycle after the common prefix.
                        entry=original['entry'];period=original['period']
                        while entry<len(word):entry+=period
                        a=advance(program,(0,word),entry)
                        b=advance(program,(0,word+'0'*k),entry+k)
                        c=advance(program,b,period)
                        need(a==b==c,'exact shifted cycle certificate')
                        counts['shifted_nonhalting_cycles']+=1
    # Finite canonical-residue reduction and the strong/weak cone correspondence.
    for x,m in itertools.product(range(1,129),range(1,9)):
        strong=canonical_lengths(x,m);weak=canonical_lengths(x,m,strong=False)
        need(len({ell%m for ell in strong})==len({ell%m for ell in weak})==m,'complete distinct residues')
        for length in range(strong[0],strong[0]+5*m):
            representative=strong[(length-strong[0])%m];q=(length-representative)//m
            need(q>=0 and padded_word(x,length)==padded_word(x,representative)+'0'*(q*m),'canonical padding factorization')
            counts['strong_canonical_factorizations']+=1
        for length in weak:
            target=strong[(length-strong[0])%m];q=(target-length)//m
            need(q in (0,1,2) and target==length+q*m,'weak-to-strong residue lift')
            need(2**length>x and 2**target>3*x,'both exact width cones')
            need((2**length)*(4**m)>3*x,'uniform two-period cone lift')
            counts['weak_strong_canonical_residue_pairs']+=1
    examples=[]
    for program,x,lengths in [((2,0),1,(2,3)),((1,0),1,(2,3)),((1,0,0),1,(2,3,4)),((0,1,1),2,(3,4,5))]:
        record=dict(program=list(program),x=x,runs=[])
        for length in lengths:
            word=padded_word(x,length);need(2**length>3*x,'counterexample admissible strong cone')
            outcome=classify(program,word,limit=100)
            need(outcome['status']!='unresolved','fully certified counterexample')
            record['runs'].append(dict(length=length,width=2**length,word=word,**outcome))
        examples.append(record)
    need(examples[0]['runs'][0]['first_halt']==9,'two-phase ordinary input halt')
    cycle=examples[0]['runs'][1]
    need(cycle['status']=='cycle' and cycle['entry']==7 and cycle['period']==12,'two-phase truth-changing one-zero extension')
    need(examples[1]['runs'][0]['first_halt']==6 and examples[1]['runs'][1]['first_halt']==10,'nonperiod delay is not one')
    need(examples[3]['runs'][0]['status']=='cycle' and examples[3]['runs'][1]['status']=='cycle' and examples[3]['runs'][2]['first_halt']==9,'all three canonical residue outcomes')
    counts['certified_counterexample_runs']=sum(len(r['runs']) for r in examples)
    def reject(fn):
        try:fn()
        except (ValueError,TypeError):counts['malformed_rejected']+=1
        else:raise ValueError('malformed accepted')
    for bad in ([],(),(True,),(1.0,),(-1,),None):reject(lambda bad=bad:prefix_coupling(bad,'10',1))
    for bad in (True,1.0,-1,None):reject(lambda bad=bad:prefix_coupling((0,1),'10',bad))
    for bad in (True,1.0,0,-1,None):reject(lambda bad=bad:canonical_lengths(bad,2))
    for bad in (True,1.0,0,-1,None):reject(lambda bad=bad:canonical_lengths(1,bad))
    return json.loads(json.dumps(dict(status='PASS_GRILL_PERIOD_PADDING',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),reference_source_sha256=SOURCE_SHA256,
        checks=dict(counts),coupling_scope=dict(program_exponents=[0,1,2],program_periods=[1,2,3,4],binary_word_lengths=[0,1,2,3,4,5],all_initial_phases=True,whole_period_padding_blocks=[0,1,2,3]),
        examples=examples,limits=['Whole-period padding preserves halting and shifts first halt by the added length; proof is independent of the finite census.',
        'Unresolved bounded runs are not classified as nonhalting. Nonhalting examples carry exact repeated full configurations.',
        'Finite canonical-width union is a semantic reduction; evaluating bit length or running its alternatives is not a free arithmetic compiler operation.',
        'The weak-cone native saving is one fixed multiplication after a separate source adaptation; no parent polynomial or positive witness bijection is asserted here.',
        'No universal Grill program or raw-input decoder is proved.'])))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',type=Path,default=Path(__file__).with_name('grill_tag_word_closure.py'));p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.source)
    if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact saved receipt differs')
    if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status=r['status'],checks=r['checks']),sort_keys=True))
