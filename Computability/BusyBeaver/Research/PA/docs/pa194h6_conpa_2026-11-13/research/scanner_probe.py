#!/usr/bin/env python3
"""Exact rejection witness for deleting native scanner state 34.
This is a counterexample to one transformation, not a state lower bound.
"""
from pathlib import Path
import argparse, json, hashlib

def load(p):
    r={}
    for line in p.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'): continue
        q,b,w,d,n=line.split()
        r[int(q),int(b)]=int(w), d=='R', int(n)
    return r

def frame(path,head,physical,width=48):
    tape={head-1,head+width}
    tape.update(head+i for i,b in enumerate(path) if int(b))
    pos=head+width+1
    for v in physical:
        pos+=1
        tape.update(range(pos,pos+v+1))
        pos+=v+1
    return tape

def run(rows,initial,target,limit):
    q,h,t=initial[0],initial[1],set(initial[2]); visits=[]
    for step in range(1,limit+1):
        if (q,int(h in t)) not in rows:
            return {'reached_target':False,'halted':True,'steps':step-1,'state':q,'head':h,'visits':visits}
        w,d,q=rows[q,int(h in t)]
        (t.add if w else t.discard)(h);h+=1 if d else -1
        if q==84:visits.append([step,h])
        if (q,h,t)==target:
            return {'reached_target':True,'steps':step,'state':q,'head':h,'visits':visits}
    return {'reached_target':False,'steps':limit,'state':q,'head':h,'visits':visits,'one_cells':sorted(t)}

def first_state(rows, initial, target, limit):
    q,h,t=initial[0],initial[1],set(initial[2])
    for step in range(1,limit+1):
        w,d,q=rows[q,int(h in t)]
        (t.add if w else t.discard)(h);h+=1 if d else -1
        if q==target:return step,(q,h,t)
    raise ValueError('specified local trace did not reach its exit')

def main():
    a=argparse.ArgumentParser();a.add_argument('package',type=Path);a.add_argument('--output',type=Path);args=a.parse_args()
    p=args.package/'machine'; rows=load(p/'machine.native.tm')
    sites=json.loads((p/'sites.json').read_text());ins=json.loads((p/'instructions.json').read_text())
    rc=json.loads((p/'receipt.json').read_text()); seed=rc['startup']
    # A clean source boundary reached by the delivered machine from blank tape.
    site=25; assert sites[site][0]=='1000000' and ins[site][0:2]==['dec',8]
    head=seed['head'];physical=seed['physical_file']; assert physical[1]==0
    initial=(84,head,set(seed['one_cells']))
    assert initial[2]==frame(sites[site][0],head,physical)
    nxt=ins[site][2];target=(84,head,frame(sites[nxt][0],head,physical))
    short={k:(w,d,75 if n==34 else n)for k,(w,d,n)in rows.items()if k[0]!=34}
    good=run(rows,initial,target,2000);bad=run(short,initial,target,2000)
    entry_steps,entry=first_state(rows,initial,2,2000)
    old_steps,old_exit=first_state(rows,entry,84,2000)
    new_steps,new_exit=first_state(short,entry,84,2000)
    assert old_exit!=new_exit
    assert good['reached_target'] and not bad['reached_target']
    result={'scope':'Exact finite witness that deleting scanner state34 fails to preserve the old scanner contract on a context reached by the parent from blank. This does not prove a state lower bound or determine the complete modified machine halting behavior.',
            'original_native_sha256':hashlib.sha256((p/'machine.native.tm').read_bytes()).hexdigest(),
            'original_states':len(rows)//2,'candidate_states':len(short)//2,
            'changed_rule':'Redirect every target34 to75; delete state34.',
            'source_site':site,'source_path':sites[site][0], 'instruction':ins[site],
            'next_site_zero_branch':nxt,'complete_initial_state':{'state':84,'head':head,'one_cells':sorted(initial[2])},
            'expected_state':{'state':84,'head':head,'one_cells':sorted(target[2])},
            'parent':good,'shortened':bad,
            'scanner_contract':{'entry_after_steps':entry_steps, 'entry':{'state':entry[0],'head':entry[1],'one_cells':sorted(entry[2])},
            'parent_exit':{'steps':old_steps,'state':old_exit[0],'head':old_exit[1],'one_cells':sorted(old_exit[2])},
            'short_exit':{'steps':new_steps,'state':new_exit[0],'head':new_exit[1],'one_cells':sorted(new_exit[2])}}}
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
