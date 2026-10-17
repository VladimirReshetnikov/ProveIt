#!/usr/bin/env python3
"""Align primitive-operation occurrences between recovered DAG and literal tree."""
from collections import deque
from pathlib import Path
import json,re,sys
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'source/Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(BASE))
from full_grammar_experiment import load_file
import recover_wade_dag as recover
helper=load_file('align_helper',HERE/'08-schema-machine-rebracket_axioms.py')
nodes,names=recover.parse_dag(recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
raw=(recover.SNAPSHOT/'ZF/m254/coq/tm/Prog254.v').read_text()
body=raw.split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
ops={'CN':'ENode','CI':'EInc','CD':'EDecnz','CB':'EBreak','CC':'EContinue','CH':'EHalt'}
def convert(e):
    op,*arg=e.split();return ops[op]+(' '+arg[0] if arg else '')
rawnodes={i:tuple(map(convert,pair)) for i,pair in enumerate(re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body))}
a,b=helper.PathMachine(nodes),helper.PathMachine(rawnodes)
todo=deque([(a.normalize(()),b.normalize(()))]);mapping={};reverse={}
while todo:
    x,y=todo.popleft()
    if x in mapping:
        assert mapping[x]==y,(x,mapping[x],y);continue
    if x[1].startswith('EInc ') and y[1].startswith('EInc '):
        aa=[];bb=[]
        while x[1].startswith('EInc '):
            aa.append(x);ss=a.successors(*x);assert len(ss)==1;x=ss[0]
        while y[1].startswith('EInc '):
            bb.append(y);ss=b.successors(*y);assert len(ss)==1;y=ss[0]
        assert sorted(z[1] for z in aa)==sorted(z[1] for z in bb),(aa,bb)
        remain=bb[:]
        for xx in aa:
            yy=next(z for z in remain if z[1]==xx[1]);remain.remove(yy)
            assert xx not in mapping or mapping[xx]==yy
            mapping[xx]=yy;reverse[yy]=xx
        todo.append((x,y));continue
    assert x[1]==y[1],(x,y)
    mapping[x]=y
    assert y not in reverse or reverse[y]==x
    reverse[y]=x
    todo.extend(zip(a.successors(*x),b.successors(*y)))
print('ALIGNED',len(mapping))
def bstr(p):return ''.join(map(str,p))
def locate(root,path=()):
    if root in (1,130,149,171,166,167,121,95,113):
        if bstr(path).startswith('111') or root in (130,149):
            entries=[(bstr(x[0]),x[1],bstr(y[0])) for x,y in mapping.items() if x[0][:len(path)]==path]
            prefix=entries[0][2] if entries else ''
            for _,_,p in entries:
                while not p.startswith(prefix):prefix=prefix[:-1]
            print('ROOT',root,names[root],'PATH',bstr(path),'ALIGNED_PREFIX',prefix,'COUNT',len(entries))
            if root==171 and bstr(path).startswith('111000000'):
                print(json.dumps(entries))
    for bit,e in enumerate(nodes[root]):
        if e.startswith('ENode '):locate(int(e.split()[1]),path+(bit,))
locate(0)
report=[dict(source=bstr(x[0]),operation=x[1],target=bstr(y[0])) for x,y in mapping.items()]
(HERE/'protocol_alignment.json').write_text(json.dumps(report,indent=2)+'\n')
