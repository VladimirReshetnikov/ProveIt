#!/usr/bin/env python3
"""Positive joint diagrams with a state-dependent head displacement.

All old states except `drop` relate to the same new head. State `drop`
relates to `keep` with new head old_head+shift and identical whole tape.
The source invariant overapproximates every tape from the common initial
state. Both block lengths must be strictly positive. This checker does not
search for tables or prove that a failed bounded diagram is impossible.
"""
from collections import Counter
from pathlib import Path
import argparse, hashlib, importlib.util, json, time

BASE = Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-k219/variant-row157/check_joint_fold.py')
BASE_SHA='82d0b364dfdbc7433a58c3c3e7166ec6a32ac9268e0e516f5f113f1287f44031'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(BASE)==BASE_SHA
spec=importlib.util.spec_from_file_location('old_window_domain',BASE)
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
def need(p,msg):
    if not p: raise ValueError(msg)

def check(old,new,oldstart,newstart,keep,drop,shift,radius=7,fuel=97):
    Q={q for q,b in old}; S={q for q,b in new}
    need(keep in Q and drop in Q and keep!=drop,'Invalid merge')
    need(S==Q-{drop},'Wrong surviving state set')
    need(set(new)=={(q,b) for q in S for b in (0,1)},'Incomplete new table')
    need(all(w in (0,1) and d in (-1,1) and z in S|{254} for w,d,z in new.values()),'Bad action')
    need(shift in (-2,2) and radius>=abs(shift) and fuel>0,'Invalid bounds or shift')
    # The initialized tapes are literally the same, with the same head.
    need(oldstart!=drop and newstart==oldstart,'Initial relation not established')
    phi=lambda q:keep if q==drop else q
    offset=lambda q:shift if q==drop else 0
    inv=base.domain(old,oldstart,radius)
    histogram=Counter(); changed=[]; contexts=0; nontrivial=0
    for q in sorted(Q):
        for b in (0,1):
            words=sorted(m for m in inv[q] if ((m>>radius)&1)==b)
            contexts+=len(words)
            w,d,z=old[q,b]
            # For an unshifted source state both machines write the same
            # cell; their one-step heads match exactly when this equation
            # holds. Do not use this shortcut at the shifted source state.
            if q!=drop and new[q,b]==(w,d+offset(z),phi(z)):
                histogram[1,1]+=len(words);continue
            changed.append([q,b]);nontrivial+=len(words)
            for word in words:
                goals={};old_halt=None;oq,oh,om=q,0,word
                for oldn in range(1,fuel+1):
                    if oq==254 or not -radius<=oh<=radius:break
                    ob=(om>>(oh+radius))&1;ow,od,oq=old[oq,ob]
                    om=(om&~(1<<(oh+radius)))|(ow<<(oh+radius));oh+=od
                    if oq==254:old_halt=oldn
                    goals.setdefault((phi(oq),oh+offset(oq),om),oldn)
                nq,nh,nm=phi(q),offset(q),word
                for newn in range(1,fuel+1):
                    need(nq!=254 and -radius<=nh<=radius,f'new exits: row{(q,b)} word{word}')
                    nb=(nm>>(nh+radius))&1;nw,nd,nq=new[nq,nb]
                    nm=(nm&~(1<<(nh+radius)))|(nw<<(nh+radius));nh+=nd
                    if nq==254:
                        need(old_halt is not None,f'new halt unproved: row{(q,b)} word{word}')
                        histogram[old_halt,newn]+=1;break
                    oldn=goals.get((nq,nh,nm))
                    if oldn is not None:
                        histogram[oldn,newn]+=1;break
                else:raise ValueError(f'no positive join: row{(q,b)} word{word}')
    need(sum(histogram.values())==contexts,'Context census mismatch')
    return {'status':'ALL_TAPE_SHIFTED_JOINT_DIAGRAM_PASS','old_states':len(Q),'new_states':len(S),
            'old_start':oldstart,'new_start':newstart,'keep':keep,'drop':drop,'shift':shift,
            'radius':radius,'fuel':fuel,'contexts':contexts,'nontrivial_contexts':nontrivial,
            'changed_old_rows':changed,'positive_blocks':[[a,b,n] for (a,b),n in sorted(histogram.items())],
            'scope':'All binary initial tapes, identical starts/heads. At drop, new head is old head+shift; elsewhere equal. Whole tapes equal at nonhalting related endpoints, or both runs halt. Source reachability overapproximation from pinned prior domain algorithm. No Lean or PA endpoint.'}

def controls():
    O={(0,0):(0,1,2),(0,1):(1,1,1),
       (1,0):(0,1,4),(1,1):(1,1,4),(4,0):(0,1,5),(4,1):(1,1,5),
       (5,0):(0,1,3),(5,1):(1,1,3),(2,0):(0,1,3),(2,1):(1,1,3),
       (3,0):(0,1,3),(3,1):(1,1,254)}
    results=[]
    for sign in (1,-1):
        old={k:(w,d*sign,z) for k,(w,d,z) in O.items()}
        new={k:v for k,v in old.items() if k[0]!=2};new[0,0]=(0,-sign,1)
        good=check(old,new,0,0,1,2,-2*sign,3,97)
        need(any(a==1 and b==3 for a,b,n in good['positive_blocks']),'Missing 1/3 block')
        bad=new.copy();bad[0,0]=(0,sign,254)
        try:check(old,bad,0,0,1,2,-2*sign,3,97)
        except ValueError as exc:negative=str(exc)
        else:raise AssertionError('Early halt accepted')
        # A wrong incoming direction must also fail, despite the correct
        # number of states and a valid shifted-state local detour.
        bad=new.copy();bad[0,0]=(0,sign,1)
        try:check(old,bad,0,0,1,2,-2*sign,3,97)
        except ValueError as exc:direction_negative=str(exc)
        else:raise AssertionError('Wrong incoming direction accepted')
        results.append({'positive':good,'early_halt_negative':negative,'wrong_direction_negative':direction_negative})
    return {'status':'PASS','cases':results,'scope':'Two mirrored synthetic 6-to-5-state shifted folds only; early-halt and wrong-direction negatives.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--old',type=Path)
    ap.add_argument('--new',type=Path);ap.add_argument('--keep',type=int);ap.add_argument('--drop',type=int)
    ap.add_argument('--shift',type=int);ap.add_argument('--output',required=True,type=Path)
    ap.add_argument('--radius',type=int,default=7);ap.add_argument('--fuel',type=int,default=97)
    ap.add_argument('--controls',action='store_true');a=ap.parse_args()
    need(not a.output.exists(),'Output exists');now=time.monotonic()
    if a.controls:r=controls()
    else:
        old,os=base.read(a.old);new,ns=base.read(a.new)
        r=check(old,new,os,ns,a.keep,a.drop,a.shift,a.radius,a.fuel)
        r.update(old_sha256=sha(a.old),new_sha256=sha(a.new))
    r.update(checker_sha256=sha(Path(__file__)),domain_checker_sha256=BASE_SHA,seconds=time.monotonic()-now)
    a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
