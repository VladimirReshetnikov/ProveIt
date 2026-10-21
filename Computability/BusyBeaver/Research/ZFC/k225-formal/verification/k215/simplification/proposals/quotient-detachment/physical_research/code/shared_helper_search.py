#!/usr/bin/env python3
"""Search two context-dependent role fusions paid for by one shared selector."""
from pathlib import Path
import argparse,itertools,json,time,hashlib
import build221 as b
from local_history_search import contexts

def block2(T,q,m,radius,bit,marker_dir,action,target,write,move,forbid,limit=31):
    tape={i-radius:(m>>i)&1 for i in range(2*radius+1)};expected=dict(tape);expected[0]=write
    tape[0]=bit;h=marker_dir;state=-1;seen=set();used=set()
    for tick in range(1,limit+1):
        if tick>1 and h==move and state==target and tape==expected:return tick,used
        if h not in tape:return None
        key=(state,h,tuple(tape.values()))
        if key in seen:return None
        seen.add(key)
        if tick==1:w,d,state=action
        else:
            if state in forbid:return None
            row=(state,tape[h]);used.add(row)
            if row not in T:return None
            w,d,state=T[row]
        tape[h]=w;h+=d
    return None

def run(path,radius=5,limit=31):
    raw=path.read_bytes();start=int(raw.decode().splitlines()[0].split()[-1]);T=b.read_table(raw.replace(f'#! start {start}'.encode(),b'#! start 0',1));C=contexts(T,start,radius);states=sorted(C);profiles=[];count=0;t=time.monotonic()
    actions=list(itertools.product((0,1),(-1,1),states))
    for q,r in itertools.combinations(states,2):
        if start in(q,r):continue
        for bit in(0,1):
            if T[q,1-bit]!=T[r,1-bit]or T[q,bit]==T[r,bit]:continue
            for direction in(-1,1):
                choices=[]
                for marker in(0,1):
                    conditions=[(z,m)for z in(q,r)for m in sorted(C[z])if((m>>radius)&1)==bit and((m>>(radius+direction))&1)==marker]
                    allowed={}
                    for action in actions:
                        used=set();dur=set();good=True
                        for z,m in conditions:
                            w,d,target=T[z,bit]
                            ans=block2(T,z,m,radius,bit,direction,action,target,w,d,{q,r},limit)
                            if ans is None:good=False;break
                            dur.add(ans[0]);used.update(ans[1])
                        if good:allowed[action]=(used,dur)
                    choices.append(allowed)
                    if not allowed:break
                count+=1
                if len(choices)==2 and all(choices):profiles.append((q,r,bit,direction,choices))
    survivors=[]
    for p1,p2 in itertools.combinations(profiles,2):
        q,r,bit,di,aa=p1;s,tj,bit2,di2,bb=p2
        if len({q,r,s,tj})<4:continue
        opts=[]
        for marker in(0,1):
            zz=[]
            for action in sorted(set(aa[marker])&set(bb[marker])):
                used=aa[marker][action][0]|bb[marker][action][0]
                if any(z in(q,r,s,tj)for z,bv in used):continue
                if action[2]in(q,r,s,tj):continue
                zz.append(dict(action=action,used=sorted(used),durations=sorted(aa[marker][action][1]|bb[marker][action][1])))
            opts.append(zz)
        if all(opts):survivors.append(dict(pair1=p1[:4],pair2=p2[:4],choices=opts))
    return dict(table_sha256=hashlib.sha256(raw).hexdigest(),radius=radius,limit=limit,pair_directions=count,profiles=[dict(pair=p[:4],choices=[list(c)for c in p[4]])for p in profiles],survivors=survivors,seconds=time.monotonic()-t)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();r=run(a.table);a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
