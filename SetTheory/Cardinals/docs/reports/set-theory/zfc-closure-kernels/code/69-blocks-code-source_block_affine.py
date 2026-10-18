#!/usr/bin/env python3
"""Finite quiet-source-block extension of the reviewed affine checker.

Default scope: every nine-register source root. A block executes its named
first source instruction and then zero or more CB, CC, or certified-zero CD
instructions. Every accepted target carries an explicit positive source-step
count. CH is never crossed. The register macros remain the proved context246
macros; only complete dispatcher-frame endpoints are relaxed.

This is an ordinary mathematical checker, not a new proof-assistant endpoint.
"""
from collections import Counter
from functools import lru_cache
from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parent
if str(HERE) not in sys.path:sys.path.insert(0,str(HERE))
import source_invariant_affine as A
from program import site_map,lookup,audit

SKIP=A.SKIP
canon=A.canon
canon_side=A.canon_side
PHYSICAL=A.PHYSICAL

def source_step(pc,branch=None):
    """Full-width successor, register effect, header shift, PC overflow."""
    _,op,r,_,_=site_map[pc]
    effect=None;extra=0;overflow=False
    if op=='CI':
        successor,overflow=audit.full_inc(pc);effect=('inc',PHYSICAL[r])
    elif op=='CD':
        assert branch is not None and branch[0]==PHYSICAL[r]
        if branch[1]:successor,overflow=audit.full_inc(audit.full_strip(pc,'0',1))
        else:
            successor,overflow=audit.full_inc(pc)
            effect=('dec',PHYSICAL[r]);extra=1
    elif op=='CB':successor,overflow=audit.full_inc(audit.full_strip(pc,'0',r))
    elif op=='CC':successor=audit.full_strip(pc,'1',r)
    else:
        assert op=='CH'
        return None,None,0,False
    return successor,effect,extra,overflow

def oracle(q,branch,state,zeros=frozenset(),after_zeros=frozenset(),expected_effect=None):
    """At most one nonzero effect, with certified zero tests on either side."""
    if state[0]=='plain' and q in SKIP:
        effect=state[1];r=SKIP[q]
        if effect is None:
            return ('2' if r==0 else '6'),('mark',r),0
        if effect==expected_effect:
            return ('2' if r==0 else '6'),('mark',r,effect),0
    if state[0]=='mark':
        r=state[1]
        if not 0<=r<9:return None
        carried=state[2] if len(state)==3 else None
        if carried is not None:
            if carried==expected_effect and q=='95' and r in after_zeros:
                return '112',('plain',carried),0
            return None
        if q=='73':return '48',('plain',('inc',r)),0
        if q=='95':
            if branch is not None and branch[0]==r:
                return ('112',('plain',None),0) if branch[1] else ('48',('plain',('dec',r)),1)
            if r in zeros:return '112',('plain',None),0
    return None

class BlockChecker:
    def __init__(self,invariant_checker=A,max_instructions=64):
        assert max_instructions>=1
        self.A=invariant_checker
        self.max_instructions=max_instructions
        self.CHECKED_TRANSFERS=invariant_checker.CHECKED_TRANSFERS
        self.case_allowed=invariant_checker.case_allowed
        self.zero_registers=invariant_checker.zero_registers

    @lru_cache(maxsize=None)
    def endpoints(self,pc,branch=None):
        assert self.case_allowed(pc,branch)
        successor,effect,extra,overflow=source_step(pc,branch)
        if successor is None:return ()
        count=1;overflows=int(overflow);seen={pc};out=[]
        while True:
            post_leaf,op,r,_,_=lookup(successor)
            # No ignored nonzero PC suffix is permitted. Extra zeros are the
            # same cells already represented by the affine zero gap.
            assert post_leaf.rstrip('0')==successor.rstrip('0')
            assert post_leaf in self.A.INVARIANT
            distance=extra+overflows
            gap=40+distance-len(successor)
            assert gap>=0
            target=canon([('b',1)],
                [('b',int(b)) for b in successor]+
                [('r',0,1,gap),('b',1),('box',('plain',effect))])
            zeros=tuple(PHYSICAL[i] for i,m in enumerate(self.A.INVARIANT[post_leaf]) if m==1)
            out.append(dict(source_steps=count,successor_full=successor,
                successor_normalized=successor.rstrip('0'),post_leaf=post_leaf,
                effect=effect,positive_decrements=extra,pc_overflows=overflows,
                head_shift=-overflows,distance_increment=distance,
                certified_zero_physical=zeros,affine_target=target))
            if count>=self.max_instructions or post_leaf in seen:break
            quiet=(op in ('CB','CC') or (op=='CD' and self.A.INVARIANT[post_leaf][r]==1))
            if not quiet:break
            seen.add(post_leaf)
            next_branch=(PHYSICAL[r],True) if op=='CD' else None
            assert self.case_allowed(post_leaf,next_branch)
            successor,quiet_effect,quiet_extra,carry=source_step(post_leaf,next_branch)
            assert successor is not None and quiet_effect is None and quiet_extra==0
            overflows+=int(carry);count+=1
        return tuple(out)

    def run(self,table,pc,branch,target,halt=False,fuel=20000):
        assert self.case_allowed(pc,branch)
        assert halt==(site_map[pc][1]=='CH')
        endpoints=self.endpoints(pc,branch)
        zeros=self.zero_registers(pc,branch)
        if not halt:
            assert target==endpoints[0]['affine_target'],('wrong immediate source target',pc,branch)
            expected_effect=endpoints[0]['effect']
            after_zeros=frozenset(r for e in endpoints for r in e['certified_zero_physical'])
            if expected_effect is None:zeros|=after_zeros
            targets={}
            for e in endpoints:targets.setdefault(e['affine_target'],e['source_steps'])
        else:expected_effect=None;after_zeros=frozenset();targets={}
        q='96';onleft=False;left=[('b',1)]
        right=[('b',int(b)) for b in pc]+[('r',0,1,40-len(pc)),('b',1),('box',('plain',None))]
        literal_steps=0;rule_count=Counter()
        for _ in range(fuel):
            if q=='254':
                assert halt and literal_steps>0,('unexpected halt in nonhalting source block',pc,branch)
                rule_count['source_instructions']+=1
                return rule_count,literal_steps
            if literal_steps>0 and not halt and not onleft and q=='96':
                normalized=canon(left,right)
                if normalized in targets:
                    count=targets[normalized]
                    assert count>=1
                    rule_count['source_instructions']+=count
                    rule_count['quiet_source_instructions']+=count-1
                    return rule_count,literal_steps
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
            answer=oracle(q,branch,seg[1],zeros,after_zeros,expected_effect)
            if answer is not None:
                if q=='95' and seg[1][0]=='mark':
                    if len(seg[1])==3:rule_count['zero_box_after_effect']+=1
                    elif branch is None or branch[0]!=seg[1][1]:rule_count['source_zero_box']+=1
                q,newstate,extra=answer;left=[('b',1)]*extra+left;right=[('box',newstate)];onleft=True;rule_count['box']+=1;continue
            write,move,following=table[q,0]
            assert write==0 and move=='L',('no justified box operation',q,branch,seg[1],sorted(zeros),sorted(after_zeros))
            q=following;onleft=True;literal_steps+=1;rule_count['literal_box_boundary']+=1
        raise AssertionError('symbolic fuel exhausted')

DEFAULT=BlockChecker()
run=DEFAULT.run
endpoints=DEFAULT.endpoints
case_allowed=DEFAULT.case_allowed
zero_registers=DEFAULT.zero_registers
CHECKED_TRANSFERS=A.CHECKED_TRANSFERS
ARBITRARY_ROOT_CHECKED_TRANSFERS=A.ARBITRARY_ROOT_CHECKED_TRANSFERS

if __name__=='__main__':
    import source_exactroot_affine as exact
    for name,checker in [('quiet-block-targets',DEFAULT),('quiet-block-targets-exactroot',BlockChecker(exact))]:
        out=[]
        for pc,op,r,_,_ in site_map.values():
            for zero in ((True,False) if op=='CD' else (None,)):
                branch=(PHYSICAL[r],zero) if op=='CD' else None
                if not checker.case_allowed(pc,branch):continue
                out.append(dict(pc=pc,branch=branch,halt=op=='CH',targets=checker.endpoints(pc,branch)))
        scope='all nine-register roots' if checker is DEFAULT else dict(exact_root=exact.EXACT_BOOTSTRAP_ROOT)
        summary=dict(scope=scope,case_count=len(out),
            maximum_source_instructions=max((e['source_steps'] for c in out for e in c['targets']),default=1),
            cases_with_quiet_targets=sum(len(c['targets'])>1 for c in out),
            total_targets=sum(len(c['targets']) for c in out),cases=out)
        (Path(__file__).resolve().parent/(name+'.json')).write_text(json.dumps(summary,indent=2)+'\n')
        print(json.dumps({k:v for k,v in summary.items() if k!='cases'}))
