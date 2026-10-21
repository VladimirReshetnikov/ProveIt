#!/usr/bin/env python3
"""Fold two controls by shared bounded helper walks on BOTH read branches.

Unlike the earlier one-common-row family, both replacement rows may change.
The only rewritten rows are the two retained-state rows, every target of the
removed control is redirected, and all strict block-interior controls must
avoid both controls. Every accepted block restores the complete known window
with precisely the old write and reaches the old moved head and mapped target.
Reads outside the inductive window or runs beyond the step cap are unresolved,
not semantic refutations. This is a synthesis/finite-certificate search.
"""
from pathlib import Path
from collections import Counter
import itertools,json,hashlib,argparse,time
from search_two_branch_folds import parse,windows,serialize

def profile(T,W,q,b,a,radius,maxsteps):
    w,d,t=T[q,b];ww,dd,h=a;used=set();lens=[]
    xs=[x for x in W[q]if(x>>radius)&1==b]
    for x in xs:
        y=(x&~(1<<radius))|(ww<<radius);goal=(x&~(1<<radius))|(w<<radius)
        pos=dd;z=h;seen=set();local=set()
        for k in range(1,maxsteps+1):
            if z==t and pos==d and y==goal:
                used.update(local);lens.append(k);break
            if abs(pos)>radius:return None,'outside_window'
            key=z,pos,y
            if key in seen:return None,'local_cycle'
            seen.add(key)
            bb=(y>>(radius+pos))&1
            if(z,bb)not in T:return None,'terminal'
            local.add(z)
            v,move,z=T[z,bb];y=(y&~(1<<(radius+pos)))|(v<<(radius+pos));pos+=move
        else:return None,'step_limit'
    return {'interior':sorted(used),'max_steps':max(lens,default=0),'windows':len(xs)},'pass'

def search(table,out,radius=3,maxsteps=32):
    T,S,start,halt=parse(table);W=windows(T,S,start,halt,radius);checks=Counter();profiles={}
    total=time.monotonic()
    for qi,q in enumerate(S):
        for b in(0,1):
            w,d,t=T[q,b];good={}
            for dd in(-1,1):
                for h in S+[halt]:
                    a=w,dd,h;pr,status=profile(T,W,q,b,a,radius,maxsteps);checks[status]+=1
                    if pr is not None:good[a]=pr
            profiles[q,b]=good
        if(qi+1)%50==0:print('profiles',qi+1,round(time.monotonic()-total,2),flush=True)
    pairs=0;twodiff=0;solutions=[];branch=Counter()
    for q,r in itertools.permutations(S,2):
        if r==start:continue
        if any(T[q,b][:2]!=T[r,b][:2]for b in(0,1)):continue
        # Literal target correspondence is checked here; target redirects at a
        # boundary are applied afterward. Different action targets q/r cannot
        # be shared through the intersection, so this is an explicit restriction.
        pairs+=1;twodiff+=all(T[q,b][2]!=T[r,b][2]for b in(0,1))
        choices=[]
        for b in(0,1):
            choices.append([a for a in profiles[q,b].keys()&profiles[r,b].keys()
                            if not(set(profiles[q,b][a]['interior'])|set(profiles[r,b][a]['interior']))&{q,r}])
        branch[str(tuple(bool(c)for c in choices))]+=1
        if not all(choices):continue
        phi=lambda z:q if z==r else z
        for aa in itertools.product(*choices):
            N={(z,b):(w,d,phi(t))for(z,b),(w,d,t)in T.items()if z!=r}
            for b,(w,d,z)in enumerate(aa):N[q,b]=w,d,phi(z)
            raw=serialize(N,start);sid=len(solutions);record={'keep':q,'drop':r,'actions':aa,'sha256':hashlib.sha256(raw).hexdigest(),
                 'profiles':[[profiles[z,b][aa[b]]for z in(q,r)]for b in(0,1)]}
            solutions.append(record);(out/f'candidate_{sid:04d}.native.tm').write_bytes(raw)
    result={'scope':__doc__,'input_sha256':hashlib.sha256(table.read_bytes()).hexdigest(),'radius':radius,'max_steps':maxsteps,'window_count':sum(map(len,W.values())),
            'profile_results':dict(checks),'pair_retention_choices':pairs,'both_literal_target_branches_differ':twodiff,'branch_pass':dict(branch),'solutions':solutions,'seconds':time.monotonic()-total,
            'code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');return result

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('table',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--radius',type=int,default=3);ap.add_argument('--maxsteps',type=int,default=32);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    r=search(a.table,a.output,a.radius,a.maxsteps);print(json.dumps(r,indent=2))
if __name__=='__main__':main()
