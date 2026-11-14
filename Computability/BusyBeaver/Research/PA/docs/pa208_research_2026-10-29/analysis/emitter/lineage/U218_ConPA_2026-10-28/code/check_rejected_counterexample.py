#!/usr/bin/env python3
"""Concrete valid-frame counterexample to the rejected provisional compiler table.

The failure is a literal one-instruction simulation error, not a claim about
its blank-tape halting behavior. No inherited runtime code is imported.
"""
from pathlib import Path
import argparse,hashlib,json
from table_io import parse,require
PHY=(6,2,0,4,3,7,8,5,1)

def frame(pc,registers,spares,gap=0):
    physical=[0]*9
    for i,j in enumerate(PHY):physical[j]=registers[i]
    ones={-1,64+gap}|{i for i,b in enumerate(pc)if b=='1'};p=65+gap
    for value in physical+spares:
        p+=1;ones.update(range(p,p+value+1));p+=value+1
    return ones

def root_frame(q,h,ones):
    if q!=84 or not ones or min(ones)!=h-1:return False
    right=sorted(x for x in ones if x>=h+52)
    if not right or right[0]<h+64:return False
    p=right[0]+1;last=max(ones);values=[]
    while p<=last:
        if p in ones or p+1 not in ones:return False
        p+=1;n=0
        while p in ones:n+=1;p+=1
        values.append(n-1)
    return p==last+1 and len(values)>=10

def check(table,source):
    T=parse(table.read_bytes());sites=json.loads(source.read_text());i=3004;pc,op,arg=sites[i]
    require((op,arg)==('CI',1),'Wrong witness instruction')
    original=frame(pc,[0]*9,[0]);ones=set(original);q=84;h=0;trace=[]
    for steps in range(10000):
        if steps and root_frame(q,h,ones):break
        require((q,int(h in ones))in T,'Premature undefined transition')
        b=int(h in ones);w,d,z=T[q,b];trace.append([q,h,b,w,d,z])
        if w:ones.add(h)
        else:ones.discard(h)
        q,h=z,h+d
    else:raise ValueError('Witness construction limit exhausted')
    next_pc=format(int(pc,2)+1,'0'+str(len(pc))+'b');registers=[0]*9;registers[1]=1
    wanted=frame(next_pc,registers,[0,1])
    require((q,h,ones)!=(84,0,wanted),'Rejected table unexpectedly satisfies the witness')
    return {'status':'CONCRETE_VALID_RUNTIME_FRAME_COUNTEREXAMPLE','table_sha256':hashlib.sha256(table.read_bytes()).hexdigest(),
            'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'site_index':i,'site':sites[i],
            'initial':{'state':84,'head':0,'logical_registers':[0]*9,'spares':[0],'gap':0,'one_cells':sorted(original)},
            'steps_to_dispatch':steps,'actual':{'state':q,'head':h,'one_cells':sorted(ones)},
            'expected':{'state':84,'head':0,'one_cells':sorted(wanted)},
            'missing_expected_one_cells':sorted(wanted-ones),'unexpected_one_cells':sorted(ones-wanted),
            'literal_trace':trace,
            'scope':'A valid CI1 primitive-frame counterexample to the provisional table. This does not assert a counterexample to its blank-run behavior or a consistency statement.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('source',type=Path);p.add_argument('--output',type=Path);a=p.parse_args();r=check(a.table,a.source)
    s=json.dumps(r,indent=2)+'\n'
    if a.output:a.output.write_text(s)
    print(json.dumps({k:v for k,v in r.items()if k not in('literal_trace','initial','actual','expected')},indent=2))
if __name__=='__main__':main()
