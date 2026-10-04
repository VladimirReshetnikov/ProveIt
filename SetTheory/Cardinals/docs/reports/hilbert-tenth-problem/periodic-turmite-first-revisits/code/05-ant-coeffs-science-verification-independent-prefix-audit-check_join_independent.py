#!/usr/bin/env python3
"""Separate, new full-splice validator for inspected owned arithmetic sources.

No upstream program/recipe/saved schedule executes. Prefix generation was
independently audited before this check; its canonical hash must match here.
The only reused Report44 module is the pinned, inspected OWN arithmetic source.
"""
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
RELEASE=Path('/workspace/shared/ant-coefficient-compression/release')
def check(ok,why):
    if not ok:raise ValueError(why)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def imported(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

class Splice:
    def __init__(self,prefix,bindings,arity):
        self.offset=prefix.n;self.h=prefix.digest.copy();self.bindings=bindings
        self.names=set();self.witnesses=[];self.raw=None;self.counter=0
        self.M=prefix.M;self.A=prefix.A;self.equations=[];self.residuals=0;self.used=set();self.arity=arity
    def operand(self,v):
        if type(v) is int:
            check(0<=v<self.counter,('Forward old operand',v,self.counter));return v+self.offset
        check(type(v) is str,('Wrong operand type',v))
        if v.startswith('C:'):
            name=v[2:];check(name in self.bindings,('Unbound coefficient',name));self.used.add(name)
            ref=self.bindings[name]
            check(ref in ('one','three') if type(ref) is str else type(ref) is int and 0<=ref<self.offset,('Bad fixed binding',ref))
            return ref
        check(v in self.names,('Undeclared coordinate',v));return v
    def write(self,line):
        row=json.loads(line)
        if type(row[0]) is int:
            check(len(row)==4 and row[0]==self.counter,('Bad old gate ID',row))
            number,op,left,right=row
            check(op in ('+','-','*'),('Bad opcode',op))
            a=self.operand(left);b=self.operand(right)
            output=f'{self.offset+number}\t{op}\t{a}\t{b}\n'
            self.counter+=1
            if op=='*':self.M+=1
            else:self.A+=1
        else:
            typ=row[0]
            if typ=='raw_positive':
                check(self.raw is None and not self.names,'Raw declaration order')
                wanted=['RawLeft','RawRight'] if self.arity==2 else ['RawInput']
                check(row[1]==wanted,'Wrong raw coordinates')
                self.raw=wanted;self.names.update(wanted);new=row
            elif typ=='positive':
                check(type(row[1]) is str and row[1] not in self.names and row[1] not in ('one','three') and not row[1].startswith('C:'),'Duplicate/reserved positive coordinate')
                self.names.add(row[1]);self.witnesses.append(row[1]);new=row
            elif typ=='residual_pair':
                check(len(row)==5 and row[1]==self.residuals,'Residual index')
                new=[typ,row[1],self.operand(row[2]),self.operand(row[3]),row[4]];self.residuals+=1
            elif typ=='eq':
                check(len(row)==3 and not self.equations,'Extra final equation')
                new=[typ,self.operand(row[1]),self.operand(row[2])];self.equations.append(new[1:])
            else:raise ValueError(('Record kind',typ))
            output=json.dumps(new,separators=(',',':'))+'\n'
        self.h.update(output.encode());return len(line)

def main():
    sys.path.insert(0,str(RELEASE))
    prefix=imported(RELEASE/'full_prefix.py','independently_checked_prefix')
    source=imported(RELEASE/'occurrence_compiler.py','prefix_source_class')
    p=source.Source(digest=True)
    bindings,receipt=prefix.build(p,json.loads((RELEASE/'data/recipe_assets/ca/physical_program.json').read_text()),json.loads((RELEASE/'data/anchor_patch.json').read_text()))
    check(p.receipt()==dict(M=13182377,A=15898997,total=29081374,sha256='6a01d7c1d8ee6b268d49c921b3263b578c152e49c62810d5aa877a4103cb9759'),'Prefix identity')
    owned=RELEASE/'main_source/merged_source.py'
    check(sha(owned)=='eafe92d6e57782347f430a4f1d6ea5693bd6a48300d2db0294b3ab7026b96395','Owned-source pin')
    original=imported(owned,'independently_checked_owned_main')
    expected={2:'c16901162e09b07d1e0c27b28e29dcc12a9b6137391fce85e3f150a3fed37eac',1:'85a161972769207e4f5d4212214630535208f69d6736bca2b46a8aff8276a22a'}
    joins={}
    for arity in (2,1):
        target=Splice(p,bindings,arity)
        old=original.build(stream=target,arity=arity)
        check(old['source_sha256']==expected[arity],'Old canonical stream identity')
        check(target.used==set(bindings) and len(target.used)==1152598,'Incomplete label use')
        check(target.counter==old['single_polynomial']['total'],'Main gate count')
        check(target.witnesses==old['positive_witnesses'],'Positive names changed')
        check(target.residuals==285+(arity==1),'Residual metadata count')
        check(target.equations==[[target.offset+target.counter-1,0]],'Final equation binding')
        joins[str(arity)]=dict(M=target.M,A=target.A,total=target.offset+target.counter,source_sha256=target.h.hexdigest(),
                             main_stream_sha256=old['source_sha256'],raw=target.raw,positive_witnesses=len(target.witnesses),
                             fixed_labels_used=len(target.used),residual_metadata=target.residuals,final_equations=target.equations)
    reported=json.loads((RELEASE/'verification/joined-strict-receipt.json').read_text())
    for arity,r in joins.items():
        other=reported['joins'][arity]
        for key in ('M','A','total','source_sha256','positive_witnesses'):
            check(r[key]==other[key],('Independent join differs',arity,key,r[key],other[key]))
    result=dict(status='PASS_INDEPENDENT_ACTUAL_STRICT_JOINS',joins=joins,only_literal_leaves=[1,3],
                adapter_sha256=sha(Path(__file__)),candidate_adapter_sha256=sha(RELEASE/'join_strict.py'),
                owned_arithmetic_source_sha256=sha(owned),
                scope='Both complete joined streams were regenerated and hashed, with a separately authored binding adapter. No complete stream file was retained; generation and hashing are actual, not hypothetical.')
    (HERE/'joined-independent-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
