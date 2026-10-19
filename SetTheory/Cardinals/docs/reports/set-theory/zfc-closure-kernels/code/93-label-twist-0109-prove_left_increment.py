#!/usr/bin/env python3
"""Universally check an alternative increment macro; NOT a full 244-state machine.

The three proposed edits fail existing whole-instruction fixtures. This file
proves only register-box contracts under explicit two-zero left clearance.
It uses inherited audited unary/list inference rules, with a new elementary
word identity and one derived list rule. No sampled register values occur.
"""
from pathlib import Path
import sys,json,hashlib
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE/'reference/context246/code'))
import check_macro_inductions as m
from rebuild_machines import read_table
m.TABLE,_=read_table(Path(__file__).with_name('left_increment_local244_old.tm'))
m.DERIVED.clear();m.BLOCK_PROOFS.clear();m.WORD_IDENTITY_PROVED=False
oldnorm=m.norm

def norm(word,rewrite=False):
    w=oldnorm(word,rewrite)
    # 0 D(A) = B(A) 0, proved by induction from D(v)=1^(v+1)0.
    for i in range(len(w)-1):
        a,b=w[i:i+2]
        if isinstance(a,m.Run) and a.bit==0 and a.length.c>=1 and isinstance(b,m.Blocks) and b.family=='D' and not b.rev:
            return norm(w[:i]+[m.Run(0,a.length+-1),m.Blocks('B',b.name),m.bit(0)]+w[i+2:],rewrite)
    return w
m.norm=norm
x=m.E.var('x');v=m.E.var('v');p=m.E.var('width_pre')
l,r=m.Context('left'),m.Context('right')
D=lambda n:[m.ones(n+1),m.bit(0)]
# Empty-list and cons equations are exact free-word identities.
assert norm([m.bit(0)])==norm([m.bit(0)])
assert norm([m.bit(0)]+D(v))==norm(m.B(v)+[m.bit(0)])
identity=dict(status='PASS',base='0 D([]) = B([]) 0',cons='0 D(v) D(A) = B(v) 0 D(A) = B(v) B(A) 0',quantification='all finite lists A of natural numbers')
blocks=[]
for name,q,source,target in [('seek73_block',73,'B','B'),('shift131_block',131,'B','D')]:
    family={'B':m.B,'D':D};before=family[source](v);after=family[target](v);side='R' if q==73 else 'L'
    if side=='R':
        begin=m.Conf(q,'R',[l],before+[r]);end=m.Conf(q,'R',m.reverse(after)+[l],[r]);drift=v+2
    else:
        begin=m.Conf(q,'L',m.reverse(before)+[l],[r]);end=m.Conf(q,'L',[l],after+[r]);drift=-1*(v+2)
    proof=m.prove(name,begin,end,v+2,drift);blocks.append(proof);m.BLOCK_PROOFS[name]=proof;m.DERIVED[(q,side,source,side=='L')]=(name,target)
a,b=m.Blocks('B','pre'),m.Blocks('B','suf');z=m.Blank()
proof=m.prove('left_increment_with_two_zero_clearance',
    m.Conf(73,'R',[m.bit(1),m.bit(0),m.bit(0),l],[a,m.bit(0),m.bit(0),m.ones(x),b,z]),
    m.Conf(48,'R',[m.bit(0),l],[m.bit(1),a]+m.B(x+1)+[b,z]),
    2*p+6,m.E(-2),allow_lists=True)
# Derive the unchanged carry and rollback finite-list rules needed for decrement.
for name,q,source,target,side in [('carry95_block',95,'B','C','R'),('rollback112_block',112,'C','B','L')]:
    before={'B':m.B,'C':m.C}[source](v);after={'B':m.B,'C':m.C}[target](v)
    if side=='R':begin=m.Conf(q,'R',[l],before+[r]);end=m.Conf(q,'R',m.reverse(after)+[l],[r]);drift=v+2
    else:begin=m.Conf(q,'L',m.reverse(before)+[l],[r]);end=m.Conf(q,'L',[l],after+[r]);drift=-1*(v+2)
    pr=m.prove(name,begin,end,v+2,drift);blocks.append(pr);m.BLOCK_PROOFS[name]=pr;m.DERIVED[(q,side,source,side=='L')]=(name,target)
y=m.E.var('y');suffix=m.B(y)+[b,z]
zero=m.prove('short_zero_decrement',m.Conf(95,'R',[l],[a,m.bit(0),m.bit(0)]+suffix),m.Conf(112,'L',[l],[a]+m.B(m.E())+suffix),2*p+5,m.E(-1),allow_lists=True)
out=dict(status='PASS_LOCAL_BOX_CONTRACTS_ONLY',new_working_rows=488,edits={'75/0':'0 L 112','83/0':'1 L 112','131/0':'0 R 48'},removed=255,word_identity=identity,block_theorems=blocks,increment=proof,zero_decrement=zero,global_status='REJECTED: complete instruction fixture 5 fails. The real increment phase fills the pointer gap with ones, so the local two-zero clearance premise is unavailable; rollback crosses into the PC. No blank-start or consistency theorem.',gap_change_per_increment=-1,spare_count_change_per_increment=0,table_sha256=hashlib.sha256(Path(__file__).with_name('left_increment_local244_old.tm').read_bytes()).hexdigest())
Path(__file__).with_name('left_increment_local_proofs.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['block_theorems','increment','zero_decrement']},indent=2))
