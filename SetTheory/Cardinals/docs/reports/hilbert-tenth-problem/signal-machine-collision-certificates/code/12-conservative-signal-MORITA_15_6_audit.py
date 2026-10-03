#!/usr/bin/env python3
"""Independent visual transcription and checks for Morita (2008), Table 5."""
import json, itertools
from pathlib import Path
from collections import defaultdict
OUT = Path(__file__).resolve().parent.parent/'data'
SYMBOLS = ['b','Y','N','*','$','1']
# Entries are write/direction/next-state, in the exact left-to-right printed order.
# '-' is an empty table cell; HALT and NULL are annotations, not quintuples.
ROWS = [
    ['$,-,q2','$,-,q1','b,-,q11','-','-','-'],
    ['HALT','Y,-,q1','N,-,q1','*,+,q0','b,-,q1','-'],
    ['*,-,q3','Y,-,q2','N,-,q2','*,-,q2','NULL','-'],
    ['b,+,q10','1,+,q4','b,+,q5','b,+,q8','-','-'],
    ['Y,+,q6','Y,+,q4','N,+,q4','*,+,q4','$,+,q4','-'],
    ['N,+,q6','Y,+,q5','N,+,q5','*,+,q5','$,+,q5','-'],
    ['b,-,q7','-','-','-','-','-'],
    ['N,-,q3','Y,-,q7','N,-,q7','*,-,q7','$,-,q7','Y,-,q3'],
    ['-','Y,+,q8','N,+,q8','*,+,q8','$,+,q9','-'],
    ['-','Y,+,q9','N,+,q9','*,+,q9','Y,+,q0','-'],
    ['-','Y,+,q10','N,+,q10','*,+,q10','$,-,q3','-'],
    ['*,-,q12','Y,-,q11','N,-,q11','*,-,q11','$,-,q11','-'],
    ['b,+,q14','Y,-,q12','N,-,q12','b,+,q13','-','-'],
    ['N,+,q0','Y,+,q13','N,+,q13','*,+,q13','$,+,q13','-'],
    ['-','Y,+,q14','N,+,q14','*,+,q14','$,-,q12','-'],
]
TRANSITIONS = []
UNDEFINED = []
for i, row in enumerate(ROWS):
    for read, entry in zip(SYMBOLS,row):
        if entry in ('-','HALT','NULL'):
            UNDEFINED.append({'state':f'q{i}','read':read,'kind':{'-':'unspecified','HALT':'halt','NULL':'null'}[entry]})
        else:
            write,direction,nxt=entry.split(',')
            TRANSITIONS.append({'state':f'q{i}','read':read,'write':write,'move':1 if direction=='+' else -1,'next_state':nxt})
DELTA={(t['state'],t['read']):t for t in TRANSITIONS}
assert len(TRANSITIONS)==len(DELTA)==62
assert len(UNDEFINED)==28
assert sum(x['kind']=='unspecified' for x in UNDEFINED)==26
incoming=defaultdict(list)
for t in TRANSITIONS: incoming[t['next_state']].append(t)
for state, ts in incoming.items():
    assert len({t['move'] for t in ts})==1,(state,'directions')
    assert len({t['write'] for t in ts})==len(ts),(state,'written symbols')

def encode(productions, word, phase=0):
    """productions[0] must be None (halt); remaining productions are finite Y/N words."""
    assert productions and productions[0] is None
    assert all(set(p)<=set('YN') for p in productions[1:])
    assert set(word)<=set('YN')
    assert 0<=phase<len(productions)
    rules=''.join((p or '')[::-1]+'*' for p in reversed(productions))
    delimiters=[i for i,s in enumerate(rules) if s=='*']
    marker=delimiters[-phase-1]
    rules=rules[:marker]+'b'+rules[marker+1:]
    raw=rules+'$'+word
    tape={i:s for i,s in enumerate(raw) if s!='b'}
    return tape, len(rules)+1, 'q0'

def step(tape,head,state):
    t=DELTA.get((state,tape.get(head,'b')))
    if t is None: return None
    tape=dict(tape)
    if t['write']=='b': tape.pop(head,None)
    else: tape[head]=t['write']
    return tape,head+t['move'],t['next_state']

def window(tape,lo=-1,hi=17): return ''.join(tape.get(i,'b') for i in range(lo,hi+1))

def replay(productions,word,phase=0,max_steps=100000):
    config=encode(productions,word,phase)
    snapshots=[]
    for time in range(max_steps+1):
        tape,head,state=config
        snapshots.append({'time':time,'state':state,'head':head,'read':tape.get(head,'b'),'tape':[[i,s] for i,s in sorted(tape.items())]})
        nxt=step(*config)
        if nxt is None: break
        config=nxt
    return snapshots

example=replay([None,'YN','YYN'],'NYY')
assert len(example)-1==184
assert (example[-1]['state'],example[-1]['read'])==('q1','b')
# Visually transcribed Fig. 28 configurations. Index 0 is the first N of NYY*NY*b$NYY.
EXPECTED={
    0:('q0',9,'bNYY*NY*b$NYYbbbbbbb'),
    6:('q13',9,'bNYY*NYb*$bYYbbbbbbb'),
    59:('q9',10,'bNYYbNY**$N$YYNbbbb'),
    178:('q9',11,'bNYY*NY*b$NY$YNYYNb'),
    184:('q1',7,'bNYY*NY*bbNYY$NYYNb'),
}
figure_audit=[]
for time,(state,head,expected_window) in EXPECTED.items():
    s=example[time]; tape=dict(s['tape']); actual_window=window(tape,hi=len(expected_window)-2)
    assert s['state']==state,(time,s['state'],state)
    assert s['head']==head,(time,s['head'],head)
    assert actual_window==expected_window,(time,actual_window,expected_window)
    figure_audit.append({'time':time,'state':state,'head':head,'window_origin':-1,'window':actual_window,'matches_visual_figure':True})
# Check the unique predecessor of every example transition using the destination
# state's fixed incoming direction and the symbol at the prior head position.
for before,after in zip(example,example[1:]):
    tape=dict(after['tape']); d=incoming[after['state']][0]['move']; oldhead=after['head']-d
    written=tape.get(oldhead,'b')
    candidates=[t for t in incoming[after['state']] if t['write']==written]
    assert len(candidates)==1
    t=candidates[0]
    if t['read']=='b': tape.pop(oldhead,None)
    else: tape[oldhead]=t['read']
    assert (t['state'],oldhead,sorted(tape.items()))==(before['state'],before['head'],[tuple(x) for x in before['tape']])

# Differential tests compare CTAG macrosteps with RTM observations at q0.
# At q0 the prefix before head is retained history, and the active word begins at head.
def ctag_step(prods,word,phase):
    if not word: return 'null',word,phase
    if word[0]=='Y' and phase==0: return 'halt',word,phase
    return 'running', word[1:]+(prods[phase] if word[0]=='Y' else ''),(phase+1)%len(prods)

def active_word(tape,head):
    chars=[]
    while tape.get(head,'b') in 'YN': chars.append(tape[head]); head+=1
    return ''.join(chars)

def test_case(prods,word,phase,macro_limit=12,micro_limit=50000):
    config=encode(prods,word,phase)
    initial_rule_right=config[1]-2
    microsteps=0; checks=0
    for macro in range(macro_limit):
        tape,head,state=config
        assert state=='q0'
        assert active_word(tape,head)==word
        # Recover marker ordinal among rule delimiters from right, treating the
        # sole rule-region blank as one delimiter. Rule 0 occupies rightmost slot.
        marks=[i for i in range(initial_rule_right+1) if tape.get(i,'b') in '*b']
        assert tape.get(marks[-phase-1],'b')=='b',(prods,word,phase,macro,config,marks,initial_rule_right)
        status,next_word,next_phase=ctag_step(prods,word,phase)
        while True:
            nxt=step(*config)
            if nxt is None:
                got={'q1':'halt','q2':'null'}.get(config[2],'unexpected')
                assert status==got,(prods,word,phase,status,got,config)
                return checks+1,microsteps,got
            config=nxt; microsteps+=1
            if microsteps>micro_limit: return checks,microsteps,'cap'
            if config[2]=='q0' and config[0].get(marks[-next_phase-1],'b')=='b':
                assert status=='running',(prods,word,phase,status)
                assert active_word(config[0],config[1])==next_word,(prods,word,phase,next_word,config)
                expected_program=encode(prods,'',next_phase)[0]
                assert all(config[0].get(i,'b')==expected_program.get(i,'b') for i in range(initial_rule_right+1))
                word,phase=next_word,next_phase
                checks+=1
                break
    return checks,microsteps,'macro_cap'

# Reproducible finite suite: k=1,2,3; each nonhalting production has length <=2;
# each initial word length <=3; every phase. Max 12 CTAG macrosteps per instance.
words=['']+[''.join(s) for n in (1,2,3) for s in itertools.product('YN',repeat=n)]
productions=['','Y','N','YY','YN','NY','NN']
suite={'cases':0,'macro_checks':0,'microsteps':0,'terminal_cases':0,'bounded_nonterminal_cases':0}
for k in (1,2,3):
    for ps in itertools.product(productions,repeat=k-1):
        for word in words:
            for phase in range(k):
                checks,micro,status=test_case([None,*ps],word,phase)
                suite['cases']+=1; suite['macro_checks']+=checks; suite['microsteps']+=micro
                suite['terminal_cases']+=status in ('halt','null')
                suite['bounded_nonterminal_cases']+=status not in ('halt','null')

source={'title':'Reversible computing and cellular automata','author':'Kenichi Morita','year':2008,'url':'https://hiroshima.repo.nii.ac.jp/record/2008964/files/TCS_395_101.pdf','pdf_sha256':'b29b066db12aa72b67f6dcf23b59efa1facf4482d398a84dc2f734317c7f0355','table':'Table 5','printed_page':24,'pdf_page_one_based':24,'visual_verification':'Source pages 19, 23, 24, 25 were visually inspected during preparation; source images are not bundled','definition':'Definition 3.2, printed page 19','input_convention':'Definition 3.3 and Example 3.3, printed page 23; Figure 28 and surrounding discussion, pages 24-25'}
model={'schema':'morita-15-6-table-v1','source':source,'states':[f'q{i}' for i in range(15)],'symbols':SYMBOLS,'blank':'b','initial_state':'q0','move_semantics':{'-1':'write then move one cell left','1':'write then move one cell right'},'transitions':TRANSITIONS,'undefined_cells':UNDEFINED,'transition_count':62,'input_encoding':{'productions':'[None, p1, ..., p[k-1]], where None is halt and each pi is a finite Y/N word','rules':'concatenate reverse(p[k-1])+* through reverse(p1)+*, followed by * for halt; for k=1 this is just *','phase_marker':'replace the (phase+1)-th delimiter * from the right by b','tape':'rules+$+word; b everywhere outside this finite block; input word may be empty','initial_head':'first cell of word, immediately to the right of $','initial_state':'q0','halt':'undefined pair (q1,b), representing phase-0 Y halting; q1 alone is not a terminal state','null':'undefined pair (q2,$), representing empty CTAG string; q2 alone is not a terminal state','scope':'Morita Definition 3.3 halting CTAG variant, with distinguished halt at phase 0'},'audit':{'deterministic':True,'reversible':True,'unique_read_pair_count':len(DELTA),'unique_incoming_write_per_target':True,'fixed_incoming_move_per_target':True,'explicit_terminal_cells':2,'unlabeled_empty_cells':26,'incoming_directions':{q:ts[0]['move'] for q,ts in sorted(incoming.items(),key=lambda kv:int(kv[0][1:]))},'example_final_time':184,'example_inverse_replay_verified_steps':184,'figure_28_checkpoints':figure_audit,'bounded_differential_test':suite,'source_typo':'Page 24 last paragraph reverses the letters of p1 relative to Example 3.3 and Figure 28. Example 3.3 p1=YN and Figure 28 initial tape NYY*NY*b$NYY agree with all 184 table-driven steps. The paragraph instead prints p1=NY and NYY*YN**. Use the general reversal convention and the figure, not those inconsistent example letters.'}}
(OUT/'MORITA_15_6_TABLE.json').write_text(json.dumps(model,indent=2)+'\n')
(OUT/'MORITA_15_6_FIGURE28_REPLAY.json').write_text(json.dumps({'source':source,'input':{'productions':[None,'YN','YYN'],'word':'NYY','phase':0},'snapshots':example},indent=2)+'\n')
print(json.dumps(model['audit'],indent=2))
