#!/usr/bin/env python3
"""Independent exact 17-step obstruction for the rejected U208 rotation pair.

Requires the literal parent and rejected-candidate tables; no inherited
runtime or source-language checker is imported. Exterior cells are opaque.
"""
from pathlib import Path
import argparse,hashlib,json

def require(ok,message):
    if not ok:raise ValueError(message)

def read(path):
    result={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require((q,b)not in result and b in(0,1)and w in(0,1)and d in('L','R'),'Invalid row')
        result[q,b]=(w,1 if d=='R'else-1,z)
    return result

def replay(table,word):
    initial={-1:1,**dict(enumerate(map(int,word)))}
    tape=initial.copy();q,head=84,0;trace=[]
    for i in range(100):
        if head==len(word):break
        require(head in tape,'Reads arbitrary exterior')
        bit=tape[head];write,direction,target=table[q,bit]
        trace.append([i,q,head,bit,write,direction,target])
        tape[head]=write;q,head=target,head+direction
    else:raise ValueError('Prefix replay exceeds bound')
    return {'prefix':word,'initial_state':84,'initial_head':0,'initial_known':initial,
        'trace':trace,'final_state':q,'final_head':head,
        'modified_cells':{p:b for p,b in tape.items()if initial[p]!=b}}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('parent',type=Path);parser.add_argument('candidate',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();word='0011001000001'
    old=replay(read(args.parent),word);new=replay(read(args.candidate),word)
    require(len(old['trace'])==len(new['trace'])==17,'Expected 17 transitions')
    require((old['final_state'],old['final_head'],old['modified_cells'])==(42,13,{}),'Parent differs')
    require((new['final_state'],new['final_head'],new['modified_cells'])==(25,13,{12:0}),'Candidate differs')
    require(old['trace'][:12]==new['trace'][:12],'Common prefix differs')
    require(new['trace'][-1]==[16,41,12,1,0,1,25],'Wrong destructive row')
    result={'status':'EXACT_COUNTEREXAMPLE_VERIFIED','arbitrary_exterior':True,
        'scope':'Refutes the declared nonwriting prefix-decoder contract; no global state lower bound',
        'parent_sha256':hashlib.sha256(args.parent.read_bytes()).hexdigest(),
        'candidate_sha256':hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
        'parent':old,'candidate':new}
    raw=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(raw)
    print(raw,end='')

if __name__=='__main__':main()
