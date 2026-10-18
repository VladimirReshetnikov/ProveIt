#!/usr/bin/env python3
"""Source-invariant strengthening of the attributed strict affine checker.

The tape rules below are the context246 package's prefix_affine.py rules,
derived from the attributed source27 checker. The only new macro allowance is
a zero decrement of a physical register proved initially zero at this exact
source leaf. It preserves the complete file and therefore permits subsequent
zero tests, until the first nonzero register effect. Marking remains possible
only from ('plain',None); increments and positive decrements retain one effect.

The imported finite invariant is checked for initial inclusion and closure
under every possible source transition before it is used. This is an ordinary
mathematical checker, not a new proof-assistant kernel.
"""
from collections import Counter
from pathlib import Path
import json,sys

HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path:sys.path.insert(0,str(HERE))
import source_abstract_invariant as source_inv
from program import site_map,audit

_certificate=json.loads((HERE.parent/'data/source-abstract-invariant.json').read_text())
_initial=tuple(_certificate['initial_masks'])
assert _initial==(7,1,1,7,7,1,7,7,7)
INVARIANT={p:tuple(v) for p,v in _certificate['invariant'].items()}
CHECKED_TRANSFERS=source_inv.check(_initial,INVARIANT)
# The fixed point already contains every possible initial value at the first
# root leaf. A fresh all-arbitrary-root solve yields exactly the same map;
# checking initial inclusion and closure here establishes the stronger scope
# directly, without trusting that separate solve or its output file.
ARBITRARY_ROOT_CHECKED_TRANSFERS=source_inv.check((7,)*9,INVARIANT)
PHYSICAL=tuple(audit.PHYSICAL)

SKIP={'60':0,'44':1,'31':2,'56':3,'38':4,'40':5,'28':6,'64':7,'69':8}

def case_allowed(pc,branch):
    """Only the six proved-impossible source guard cases are excluded."""
    assert pc in site_map,('not a source leaf',pc)
    _,op,logical,_,_=site_map[pc]
    if op=='CD':
        assert branch is not None and branch[0]==PHYSICAL[logical]
        assert isinstance(branch[1],bool)
    else:assert branch is None
    if pc not in INVARIANT:return False
    return branch is None or bool(INVARIANT[pc][logical]&(1 if branch[1] else 6))

def zero_registers(pc,branch):
    assert case_allowed(pc,branch),('source guard excluded by inductive invariant',pc,branch)
    zeros={PHYSICAL[r] for r,mask in enumerate(INVARIANT[pc]) if mask==1}
    if branch is not None and branch[1]:zeros.add(branch[0])
    if branch is not None and not branch[1]:assert branch[0] not in zeros
    return frozenset(zeros)

def oracle(q,branch,state,zeros=frozenset()):
    if state==('plain',None) and q in SKIP:
        r=SKIP[q];return ('2' if r==0 else '6'),('mark',r),0
    if state[0]=='mark':
        r=state[1]
        if not 0<=r<9:return None
        if q=='73':return '48',('plain',('inc',r)),0
        if q=='95':
            if branch is not None and branch[0]==r:
                return ('112',('plain',None),0) if branch[1] else ('48',('plain',('dec',r)),1)
            if r in zeros:return '112',('plain',None),0
    return None

def canon_side(segs,left):
    out=[]
    for seg in segs:
        if seg[0]=='box':out.append(('box',seg[1]));continue
        b,a,c=(seg[1],0,1) if seg[0]=='b' else seg[1:]
        assert a>=0 and c>=0
        if (a,c)==(0,0):continue
        if out and out[-1][0]==b:out[-1]=(b,out[-1][1]+a,out[-1][2]+c)
        else:out.append((b,a,c))
    if left:
        while out and out[-1][0]==0:out.pop()
    return tuple(out)

def canon(left,right):return canon_side(left,True),canon_side(right,False)

def run(table,pc,branch,target,halt=False,fuel=20000):
    zeros=zero_registers(pc,branch)
    q='96';onleft=False;left=[('b',1)]
    right=[('b',int(b)) for b in pc]+[('r',0,1,40-len(pc)),('b',1),('box',('plain',None))]
    literal_steps=0;rule_count=Counter()
    for _ in range(fuel):
        if literal_steps>0:
            if halt and q=='254':return rule_count,literal_steps
            if not halt and not onleft and q=='96' and canon(left,right)==target:return rule_count,literal_steps
        if onleft:
            if not left:right=[('b',0)]+right;onleft=False;rule_count['pad_left']+=1;continue
            seg=left[0]
            if seg[0]=='b':left=left[1:];right=[seg]+right;onleft=False;rule_count['recenter']+=1;continue
            assert seg[0]=='r','box cannot occur on the left'
            _,b,a,c=seg;write,move,following=table[q,b]
            if move=='L' and following==q:
                left=left[1:];right=[('r',write,a,c)]+right;rule_count['scan_left']+=1;continue
            if c>0:
                left=[('b',b),('r',b,a,c-1)]+left[1:];rule_count['peel_left']+=1;continue
            if a==0:left=left[1:];rule_count['empty_left']+=1;continue
            raise AssertionError(('unknown left-run length',q,a,c))
        assert right,'right exterior has no rule'
        seg=right[0]
        if seg[0]=='b':
            write,move,following=table[q,seg[1]];q=following;literal_steps+=1;rule_count['literal']+=1
            if move=='R':left=[('b',write)]+left;right=right[1:]
            else:right=[('b',write)]+right[1:];onleft=True
            continue
        if seg[0]=='r':
            _,b,a,c=seg;write,move,following=table[q,b]
            if move=='R' and following==q:
                left=[('r',write,a,c)]+left;right=right[1:];rule_count['scan_right']+=1;continue
            if c>0:
                right=[('b',b),('r',b,a,c-1)]+right[1:];rule_count['peel_right']+=1;continue
            if a==0:right=right[1:];rule_count['empty_right']+=1;continue
            raise AssertionError(('unknown right-run length',q,a,c))
        assert seg[0]=='box' and len(right)==1
        answer=oracle(q,branch,seg[1],zeros)
        if answer is not None:
            if (q=='95' and seg[1][0]=='mark' and
                    (branch is None or branch[0]!=seg[1][1])):
                rule_count['source_zero_box']+=1
            q,newstate,extra=answer;left=[('b',1)]*extra+left;right=[('box',newstate)];onleft=True;rule_count['box']+=1;continue
        write,move,following=table[q,0]
        assert write==0 and move=='L',('no justified box operation',q,branch,seg[1],sorted(zeros))
        q=following;onleft=True;literal_steps+=1;rule_count['literal_box_boundary']+=1
    raise AssertionError('symbolic fuel exhausted')
