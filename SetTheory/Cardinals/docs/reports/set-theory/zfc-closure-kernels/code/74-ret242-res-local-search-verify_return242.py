#!/usr/bin/env python3
"""Check the finite premises of the whole-tape 243 -> 242 simulation.

This checker proves local, universally quantified finite identities by symbolic
execution with unknown cells left untouched. The ordinary induction argument is
in return242-proof.tex. The optional sparse blank replay is a separate regression.
"""
from pathlib import Path
import hashlib, json

ROOT=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError('Assertions are required; do not run with Python -O.')

def read_table(name):
    text=(ROOT/name).read_text()
    out={}
    for line in text.splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,r=line.split();q,b,w,r=map(int,(q,b,w,r))
        assert b in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,b) not in out
        out[q,b]=(w,-1 if d=='L' else 1,r)
    qs={q for q,b in out}
    assert len(out)==2*len(qs)
    assert all((q,b) in out for q in qs for b in (0,1))
    assert all(r in qs or r==254 for w,d,r in out.values())
    return out,hashlib.sha256(text.encode()).hexdigest()

OLD,old_hash=read_table('base243.tm')
NEW,new_hash=read_table('zfc_return242_old.tm')
assert old_hash=='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
assert new_hash=='6b700aa713418cfe347a6ff2d0a92de7c31810d1cf69814b4684c7fb463876a0'
assert len(OLD)==486 and len(NEW)==484
assert {q for q,b in OLD}-{q for q,b in NEW}=={15}
assert NEW[11,0]==(0,1,27) and NEW[27,1]==(1,1,22)
assert {row for row in NEW if NEW[row]!=OLD[row]}=={(11,0),(27,1)}
assert OLD[15,0]==(0,1,21) and OLD[15,1]==(1,1,22)
assert all(r!=15 for w,d,r in NEW.values())

# This is the complete static induction proof of invariant I for OLD.
# I: states15,18,47,65 have a zero just left; state27 reads zero.
left_zero={15,18,47,65}
incoming={q:[] for q in left_zero|{27}}
for edge,row in OLD.items():
    if row[2] in incoming:incoming[row[2]].append([*edge,*row])
for q in left_zero:
    assert incoming[q]
    assert all((w,d)==(0,1) for p,b,w,d,r in incoming[q])
assert incoming[27]
assert all(p in left_zero and (b,w,d)==(0,0,-1)
           for p,b,w,d,r in incoming[27])
assert 95 not in left_zero|{27}

def finite_run(table,state,known,steps):
    # The initial tape is an arbitrary function subject only to `known`.
    # A read outside `known` is rejected, so the finite proof has no hidden
    # assumption about any other cell. Only assignments at read cells occur.
    tape=dict(known);head=0;states=[state];heads=[head];rows=[]
    for _ in range(steps):
        assert head in tape,('unconstrained cell read',state,head)
        b=tape[head];rows.append([state,b])
        w,d,state=table[state,b];tape[head]=w;head+=d
        states.append(state);heads.append(head)
    # Since cells outside `known` are untouched, dictionary equality proves
    # equality of the entire two-way infinite tapes, for every completion.
    return {'state':state,'head':head,'known_tape':tape,
            'states':states,'heads':heads,'rows':rows,'steps':steps}

blocks=[]
for next_bit,new_steps,endpoint in [(0,4,21),(1,2,22)]:
    known={0:0,1:next_bit}
    a=finite_run(OLD,11,known,2)
    b=finite_run(NEW,11,known,new_steps)
    for key in ('state','head','known_tape'):assert a[key]==b[key]
    assert a['state']==endpoint and a['head']==2
    blocks.append({'premises':known,'old':a,'new':b})

# Every admissible retained, nonexceptional row has the same one-step behavior.
# The inadmissible old27/read1 pair is ruled out by I.
ordinary=0
for row,action in OLD.items():
    if row[0]==15 or row in {(11,0),(27,1)}:continue
    assert row in NEW and NEW[row]==action
    assert action[2]!=15
    ordinary+=1
assert ordinary==482

def blank(table,limit=1000000):
    expected={-6,176};pos=177
    for value in [0,0,0,3,0,0,3,0,0]+[1]*167:
        expected.update(range(pos+1,pos+value+2));pos+=value+2
    tape=set();head=0;q=95;low=0;high=0;slow_blocks=0
    for n in range(limit+1):
        if q==96 and head==-5 and tape==expected:
            return {'steps':n,'state':q,'head':head,'ones':sorted(tape),
                    'head_min':low,'head_max':high,'slow_blocks':slow_blocks}
        assert q!=254
        b=int(head in tape)
        if q==11 and b==0 and head+1 not in tape:slow_blocks+=1
        w,d,q=table[q,b]
        if w:tape.add(head)
        else:tape.discard(head)
        head+=d;low=min(low,head);high=max(high,head)
    raise AssertionError('bootstrap limit reached')

old_boot=blank(OLD);new_boot=blank(NEW)
assert {k:v for k,v in old_boot.items() if k!='steps'}=={
    k:v for k,v in new_boot.items() if k!='steps'}
assert old_boot['steps']==407967
assert new_boot['steps']==old_boot['steps']+2*old_boot['slow_blocks']
assert old_boot['slow_blocks']==6
data={'old_sha256':old_hash,'new_sha256':new_hash,'old_working_states':243,
      'new_working_states':242,'new_binary_rows':484,'start':95,'halt':254,
      'invariant_incoming':incoming,'blocks':blocks,'ordinary_rows':ordinary,
      'blank_old':old_boot,'blank_new':new_boot,
      'proof_scope':'Exact local whole-tape identities + complete static induction premises; see ordinary proof.'}
(ROOT/'return242-certificate.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'passed':True,'working_states':242,'rows':484,
                 'old_boot_steps':old_boot['steps'],'new_boot_steps':new_boot['steps'],
                 'bootstrap_ones':len(new_boot['ones']),
                 'new_sha256':new_hash},indent=2))
