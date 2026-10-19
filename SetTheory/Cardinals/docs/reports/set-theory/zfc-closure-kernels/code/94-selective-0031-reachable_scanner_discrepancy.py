#!/usr/bin/env python3
"""Exact blank-reachable first-clean-frame disagreement, not halting inequivalence."""
from pathlib import Path
import hashlib,json,os

HERE=Path(__file__).resolve().parent
BASE=Path(os.environ.get('ZFC245_REFERENCE',str(HERE.parent/'packages/zfc245-proof-20261018'))).resolve()
raw=(BASE/'certificate/machine_old.tm').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
reference={}
for line in raw.decode().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,t=line.split();reference[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(t))
mutant={k:v for k,v in reference.items()if k[0]!=58};mutant[41,0]=(0,-1,84)

def sparse(table,steps,q=95,h=0,ones=()):
    tape=set(ones)
    for _ in range(steps):
        w,d,q=table[q,int(h in tape)]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d
    return q,h,sorted(tape)

def dense(table,steps,q=95,h=0,ones=()):
    origin=steps+2-min([h,0,*ones]);cells=bytearray(origin+max([h,0,*ones])+steps+3)
    for x in ones:cells[origin+x]=1
    position=origin+h
    for _ in range(steps):
        w,d,q=table[q,cells[position]];cells[position]=w;position+=d
    return q,position-origin,[i-origin for i,x in enumerate(cells)if x]

prefix=835524
q,h,coords=sparse(mutant,prefix)
assert dense(mutant,prefix)==(q,h,coords)
initial=set(coords);assert(q,h)==(96,-8)and min(initial)==h-1
sites=json.loads((BASE/'certificate/sites_logical.json').read_text())
pc,op,r=sites[6367];assert(pc,op,r)==('1111000000','CD',1)
assert {x-h for x in initial if h<=x<h+51}=={i for i,b in enumerate(pc)if b=='1'}
header=min(x for x in initial if x>=h+51);assert header==238
values=[];position=header+1
while position<=max(initial):
    assert position not in initial and position+1 in initial
    first=position+1;position=first
    while position in initial:position+=1
    values.append(position-first-1)
assert values[:9]==[0,0,0,4,0,0,6,0,0] and values[9:]==[1]*233
assert not any(h+51<=x<header for x in initial)
successor=pc[:-1];successor=format(int(successor,2)+1,f'0{len(successor)}b')
expected={x for x in initial if not h<=x<h+51}|{h+i for i,b in enumerate(successor)if b=='1'}

def first_clean(table,limit=5000):
    tape=set(initial);state,head=q,h
    for step in range(1,limit+1):
        w,d,state=table[state,int(head in tape)]
        if w:tape.add(head)
        else:tape.discard(head)
        head+=d
        clean=(state==96 and head==h and {x for x in tape if x<h}=={h-1}
            and not any(h+51<=x<header for x in tape)
            and {x for x in tape if x>=header}=={x for x in initial if x>=header})
        if clean:
            pointer=''.join(str(int(h+i in tape))for i in range(51)).rstrip('0')
            answer={'steps_from_frame':step,'state':state,'head':head,'residual_pointer':pointer,
                'all_one_positions':sorted(tape),'agrees_with_zero_decrement_successor':tape==expected,
                'added_one_cells':sorted(tape-initial),'removed_one_cells':sorted(initial-tape)}
            assert dense(table,step,q,h,coords)==(state,head,sorted(tape))
            return answer
    raise AssertionError('No clean frame within the explicitly bounded replay')

baseline=first_clean(reference);changed=first_clean(mutant)
assert (baseline['steps_from_frame'],baseline['added_one_cells'],baseline['removed_one_cells'])==(2044,[0],[])
assert (changed['steps_from_frame'],changed['added_one_cells'],changed['removed_one_cells'])==(2102,[-2],[])
assert baseline['agrees_with_zero_decrement_successor']and not changed['agrees_with_zero_decrement_successor']
assert dense(mutant,prefix+2102)==(changed['state'],changed['head'],changed['all_one_positions'])

# Distinguish a wrong first boundary from a merely harmless skipped loop.
# These are finite executions of the ideal source from the two return frames;
# they are not a claim about all subsequent execution of the shortened TM.
lookup={p:(i,op,r)for i,(p,op,r)in enumerate(sites)}
def source_decode(word):
    path=''
    for i in range(51):
        path+=word[i]if i<len(word)else'0'
        if path in lookup:return path,lookup[path]
    raise AssertionError('Source decoder depth')
def source_inc(word):
    return format((int(word,2)+1)%(1<<len(word)),f'0{len(word)}b')if word else''
def source_strip(word,bit,count):
    while word and count:count-=word[-1]==bit;word=word[:-1]
    return word
def first_source_root(word):
    regs=[6,0,0,0,4,0,0,0,0]
    for step in range(1000):
        path,(i,op,r)=source_decode(word)
        if i==0:return {'source_instructions':step,'normalized_path':path,'logical_registers':regs}
        assert op!='CH'
        if op=='CI':regs[r]+=1;word=source_inc(path)
        elif op=='CD':
            if regs[r]:regs[r]-=1;word=source_inc(path)
            else:word=source_inc(source_strip(path,'0',1))
        elif op=='CB':word=source_inc(source_strip(path,'0',r))
        elif op=='CC':word=source_strip(path,'1',r)
        else:raise AssertionError(op)
    raise AssertionError('Source root not reached within 1000 instructions')
root_expected=first_source_root(successor);root_changed=first_source_root(changed['residual_pointer'])
assert (root_expected['source_instructions'],root_expected['logical_registers'])==(652,[6,0,0,0,4,0,0,0,0])
assert (root_changed['source_instructions'],root_changed['logical_registers'])==(43,[6,4,0,0,4,0,0,0,0])
result={'status':'EXACT_BLANK_REACHABLE_FIRST_CLEAN_FRAME_DISAGREEMENT',
    'scope':'The wrong first clean source-control return occurs on the contracted machine blank trajectory. This does not prove different eventual halting or refute the requested consistency equivalence.',
    'blank_prefix_steps':prefix,'source_index':6367,'source_path':pc,'opcode':op,'logical_register':'T','physical_register':2,'guard':'zero',
    'reachable_frame':{'state':q,'head':h,'header':header,'header_distance':header-h,
        'physical_registers':values[:9],'spare_values':values[9:],'all_one_positions':coords,'all_other_cells_zero':True},
    'expected_residual_pointer':successor,'reference245_from_same_frame':baseline,'contracted244_from_same_frame':changed,
    'ideal_source_forks_to_next_root':{'expected_return':root_expected,'contracted_return':root_changed,
        'scope':'Finite ordinary-source forks from the two exact frames. Their next root register files differ. This alone does not prove different eventual halting or failure of ZFC consistency equivalence.'},
    'contracted244_wrong_return_step_from_blank':prefix+2102,'independent_sparse_dense_exact_agreement':True,
    'first_return_replay_fuel':5000,'all_unlisted_tape_cells_zero':True}
(HERE/'reachable-scanner-discrepancy.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in('reachable_frame','reference245_from_same_frame','contracted244_from_same_frame')},indent=2))
