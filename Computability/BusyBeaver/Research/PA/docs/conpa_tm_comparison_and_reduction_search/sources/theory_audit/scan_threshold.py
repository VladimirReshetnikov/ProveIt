#!/usr/bin/env python3
"""Check concrete frame witnesses for seven-to-six-zero scan modification."""
from pathlib import Path
import sys,json,time
BASE=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(BASE/'sources/history209'))
sys.path.insert(0,str(BASE/'research'))
from grammar_search import parse_program,flatten,resolve
from search_folds import read_table

def frame(path,vs,gap=0):
    tape={-1}
    tape.update(i for i,b in enumerate(path) if b)
    j=48+gap;tape.add(j);j+=1
    for v in vs:
        j+=1
        tape.update(range(j,j+v+1));j+=v+1
    return 75,0,tape

def run(rows,state,target=None,limit=20000):
    q,h,tape=state[0],state[1],state[2].copy()
    seen=[]
    for k in range(limit):
        if target is not None and (q,h,tape)==target and k>0:return k,(q,h,tape),seen
        if q==196:return k,(q,h,tape),seen
        if q==75 and k>0 and len(seen)<12:seen.append((k,h,''.join(str(int(h+i in tape)) for i in range(55))))
        b=int(h in tape);w,d,q=rows[q,b]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d
    return None,(q,h,tape),seen

def main():
    rows=read_table(BASE/'sources/bb196/data/pa196.tm');mut=rows.copy();mut[23,0]=(0,-1,69)
    if '--bypass2' in sys.argv:
        mut={key:(w,d,3 if q==2 else q) for key,(w,d,q) in rows.items()}
    nodes=parse_program();tree=nodes['trie'];flat=flatten(tree);code=resolve(tree)
    failure=[];start=time.time()
    for i,((p,leaf),inst) in enumerate(zip(flat,code)):
        if inst[0]=='halt':continue
        for pos in (False,True) if inst[0]=='dec' else (False,):
            vs=[0]*10+[1]*25
            physical=[6,2,0,4,3,7,8,5,1]
            if inst[0]=='dec' and pos:vs[physical[inst[1]]]=1
            ws=vs.copy();gap=0
            if inst[0]=='inc':ws[physical[inst[1]]]+=1;ws.append(1);j=inst[2]
            elif inst[0]=='dec':
                if pos:ws[physical[inst[1]]]-=1;gap=1;j=inst[3]
                else:j=inst[2]
            else:j=inst[1]
            if j is None:j=0
            st=frame(p,vs);target=frame(flat[j][0],ws,gap)
            orig=run(rows,st,target)
            if orig[0] is None:
                print('BAD BASELINE',i,p,inst,pos,orig[2]);return
            new=run(mut,st,target)
            if new[0] is None or new[1]!=target:
                item={'site':i,'path':p,'instruction':inst,'positive':pos,'target':j,'baseline_steps':orig[0],'new_root_visits':new[2], 'initial_ones':sorted(st[2]),'target_ones':sorted(target[2])}
                print('FAIL',json.dumps(item),flush=True);failure.append(item)
                if len(failure)>=12:break
        if len(failure)>=12:break
    suffix='_bypass2' if '--bypass2' in sys.argv else ''
    (BASE/f'sources/theory_audit/scan_threshold{suffix}_failures.json').write_text(json.dumps(failure,indent=2))
    print('DONE',len(failure),'seconds',time.time()-start,flush=True)

if __name__=='__main__':main()
