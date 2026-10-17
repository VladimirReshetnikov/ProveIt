#!/usr/bin/env python3
"""A small explicit port of the sound symbolic rules in M253.SymExec.

Unlike the upstream design prototype, this checker uses the Coq oracle's
single-effect box states, checks the register named by each decrement guard,
and records positive progress only for a literal transition. Each successful
run denotes all n>=0 and all register files satisfying its named guard.
The four unchanged register-box lemmas remain the only macro contracts.
"""
from collections import Counter
import cost_search as s

SKIP={'60':0,'44':1,'31':2,'56':3,'38':4,'40':5,'28':6,'64':7,'69':8}

def oracle(q,branch,state):
    if state==('plain',None) and q in SKIP:
        r=SKIP[q];return ('2' if r==0 else '6'),('mark',r)
    if state[0]=='mark':
        r=state[1]
        if not 0<=r<9:return None
        if q=='73':return '48',('plain',('inc',r))
        if q=='43' and branch is not None and branch[0]==r:
            return ('3',('plain',None)) if branch[1] else ('63' if r==0 else '48',('plain',('dec',r)))
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
        answer=oracle(q,branch,seg[1])
        if answer is not None:
            q,newstate=answer;right=[('box',newstate)];onleft=True;rule_count['box']+=1;continue
        write,move,following=table[q,0]
        assert write==0 and move=='L',('no justified box operation',q,branch,seg[1])
        q=following;onleft=True;literal_steps+=1;rule_count['literal_box_boundary']+=1
    raise AssertionError('symbolic fuel exhausted')

def audit(table,nodes,root):
    assert all(table[p]==s.BASE253[p] for p in s.BOX_PAIRS)
    proto=s.ctx.executor(table,s.BASE/'tools/tm/symexec.py')
    totals=Counter();cases=0;minimum=10**9
    for pc,op,r in s.sites(nodes,root):
        for zero in ((True,False) if op=='CD' else (None,)):
            branch=(r,zero) if zero is not None else None
            if op=='CI' or(op=='CD' and not zero):successor=proto['inc'](pc)
            elif op=='CD':successor=proto['inc'](proto['strip']('0',1,pc))
            elif op=='CB':successor=proto['inc'](proto['strip']('0',r,pc))
            elif op=='CC':successor=proto['strip']('1',r,pc)
            else:successor=''
            effect=('inc',r) if op=='CI' else ('dec',r) if op=='CD' and not zero else None
            if successor is None:right=[('r',0,1,41),('b',1),('box',('plain',effect))]
            else:right=[('b',int(b)) for b in successor]+[('r',0,1,40-len(successor)),('b',1),('box',('plain',effect))]
            rules,literal=run(table,pc,branch,canon([('b',1)],right),halt=op=='CH')
            totals.update(rules);minimum=min(minimum,literal);cases+=1
    assert cases==8391 and minimum>0
    return {'cases':cases,'minimum_literal_steps_per_case':minimum,'rule_totals':dict(totals),
            'semantics':'All free gap n>=0 and all >=9-register files subject only to the named decrement zero/nonzero guard.',
            'contracts':'Exactly the four published Box.v excursions, preserved by unchanged protected rows.',
            'status':'Ordinary rule-by-rule mathematical verification; checker not newly kernel verified.'}

def main():
    import json
    import verify_candidate as v
    rows,*_=v.construct();n,e,k=s.rot.options(s.NODES)[0];nodes,root=s.rot.mutate(s.NODES,s.ROOT,n,e)
    result=audit(rows,nodes,root)
    assert oracle('43',None,('mark',0)) is None
    assert oracle('43',(1,True),('mark',0)) is None
    assert oracle('64',None,('plain',('inc',0))) is None
    damaged=rows.copy();damaged['256',0]=(0,'R','148')
    try:audit(damaged,nodes,root)
    except (AssertionError,KeyError):pass
    else:raise AssertionError('single damaged decoder row was accepted')
    result['negative_checks']={'unguarded_decrement_rejected':True,'wrong_register_guard_rejected':True,
                               'remark_after_increment_rejected':True,'single_decoder_row_corruption_rejected':True}
    (s.HERE/'candidate/strict_affine_result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
