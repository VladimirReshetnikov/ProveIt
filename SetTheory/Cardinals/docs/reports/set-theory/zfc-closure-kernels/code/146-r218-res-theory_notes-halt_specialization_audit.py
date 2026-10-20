#!/usr/bin/env python3
"""Independently check the exact source replacement used by specialized_halt.
The infinite argument is the three-case calculation in halt_specialization.md.
Finite testing below is an extra implementation check, not the proof.
"""
from pathlib import Path
import sys,json,hashlib
from audit_abstract_certificate import check
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'k220_replay/baseline/K221_Construction_2026-10-20/portable'))
import source_language as s
OLD=ROOT/'baseline220/K220_Construction_2026-10-20/machine/sites220.json'
NEW=ROOT/'root_work/specialized_halt.sites.json'
CERT=ROOT/'root_work/abstract_seed.json'
rows=json.loads(OLD.read_bytes());newrows=json.loads(NEW.read_bytes());domains=json.loads(CERT.read_bytes())['domains']
check(rows,domains,[3,0,0,0,3,0,0,0,0])
a=s.tree(rows);z=s.tree(newrows);path='1110100101';old=s.subtree(a,path);new=s.subtree(z,path)
cd5=('CD',5);cd6=('CD',6);ci5=('CI',5);ci6=('CI',6);cc1=('CC',1);cc2=('CC',2);cb1=('CB',1);halt=('CH',None)
clear=(cd5,cc1)
compare=((cd6,((cd5,cc2),(ci5,(cd6,cc2)))),(cd5,(clear,cb1)))
need=lambda v,m:None if v else (_ for _ in ()).throw(ValueError(m))
need(old[0]==ci6 and old[1][0]==(compare,halt),'old literal test differs')
newtest=(cd5,((cd5,(clear,cb1)),halt))
need(new==(newtest,old[1][1]),'new literal test/rest differs')
need(s.boundary(old[1][1])==(0,0,False),'tail has an escaping control effect')
need(s.replace(a,path,new)==z,'source changed outside claimed subtree')
entry=next(i for i,r in enumerate(rows)if r[0].startswith(path))
need(entry==4598 and domains[entry][6]==1,'scratch is not proved zero')
# An independent small-step execution of a syntax subtree, with explicit
# primitive exception propagation. No source graph resolver is used here.
def run(tree,reg,budget):
    budget[0]-=1
    if budget[0]<0:raise ValueError('test budget')
    if isinstance(tree[0],str):
        op,r=tree
        if op=='CI':reg[r]+=1;return('N',0)
        if op=='CD':
            if reg[r]==0:return('B',1)
            reg[r]-=1;return('N',0)
        return({'CB':'B','CC':'C','CH':'H'}[op],r or 0)
    while True:
        k,v=run(tree[0],reg,budget)
        if k=='B':return('N',0)if v==1 else('B',v-1)
        if k!='N':return(k,v)
        k,v=run(tree[1],reg,budget)
        if k=='C':
            if v==1:continue
            return('C',v-1)
        return(k,v)
for x in range(257):
    r1=[11,13,17,19,23,x,0,29,31];r2=r1.copy()
    e1=run((ci6,(compare,halt)),r1,[100000]);e2=run(newtest,r2,[100000])
    need((e1,r1)==(e2,r2),('finite mismatch',x,e1,e2,r1,r2))
    need(e1==(('H',0)if x==1 else('N',0)),('wrong exit',x,e1))
    need(r1[5]==r1[6]==0,('not clear',x))
receipt={'status':'EXACT_RESTRICTED_HALT_SPECIALIZATION_AUDIT_PASS','source_sha256':hashlib.sha256(OLD.read_bytes()).hexdigest(),'specialized_source_sha256':hashlib.sha256(NEW.read_bytes()).hexdigest(),'entry_ordinal':entry,'entry_path':path,'proved_precondition':'r6=0; all other registers arbitrary naturals','mathematical_cases':['x=0','x=1','x>=2'],'termination':'Both blocks terminate for all natural x; their only loops monotonically decrease r5 or r6.','postcondition':'Halt iff initial r5=1. Otherwise normal exit. In both cases r5=r6=0; every other register unchanged.','closed_common_tail':True,'outside_source_unchanged':True,'supplementary_finite_tests':257,'scope':'The finite tests supplement the explicit all-natural mathematical proof; this does not verify the compiled binary transition table.'}
(ROOT/'theory_notes/halt_specialization_audit.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
