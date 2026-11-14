#!/usr/bin/env python3
"""Independent complete blank-tape prefix check for the new candidate."""
from pathlib import Path
import argparse, hashlib, json
from audit_rotation_source import read_table, require

def execute(table,steps):
    state=0;head=0;ones=set();visited=set();digest=hashlib.sha256()
    for i in range(steps):
        require(state!=254,('premature halt',i))
        scanned=int(head in ones);visited.add((state,scanned))
        write,move,target=table[state,scanned]
        digest.update(f'{state} {head} {scanned} {write} {move} {target}\n'.encode())
        if write:ones.add(head)
        else:ones.discard(head)
        state=target;head+=move
    return state,head,ones,visited,digest.hexdigest()

def audit(parent,candidate,source):
    a=read_table(parent);b=read_table(candidate);steps=48140
    old=execute(a,steps);new=execute(b,steps)
    require(old[:3]==new[:3],'complete startup endpoint differs')
    require(old[4]==new[4],'literal startup traces differ')
    state,head,ones,visited,trace_sha=new
    edits={row for row in set(a)|set(b)if a.get(row)!=b.get(row)}
    require(not edits.intersection(visited),'a changed row occurs during startup')
    require((state,head)==(84,-2),'unexpected dispatcher/head')
    rows=json.loads(Path(source).read_text());pc=rows[136][0]
    require(pc=='001100110101010','interior-start source address changed')
    logical=[1,0,13,0,0,1,0,0,1];physical=[0]*9
    for value,position in zip(logical,[6,2,0,4,3,7,8,5,1]):physical[position]=value
    expected={head-1,head+56}
    expected.update(head+i for i,bit in enumerate(pc)if bit=='1')
    position=head+57
    for value in physical+[1]*43:
        position+=1
        expected.update(range(position,position+value+1));position+=value+1
    require(ones==expected,'exact canonical whole-tape frame differs')
    return {'status':'INDEPENDENT_BLANK_STARTUP_PASS','steps':steps,
            'state':state,'head':head,'source_ordinal':136,'source_address':pc,
            'header_distance':56,'additional_gap':0,'logical_registers':logical,
            'spare_registers':[1]*43,'one_cells':sorted(ones),'zero_exterior':True,
            'parent_and_candidate_traces_identical':True,
            'trace_sha256':trace_sha,'changed_rows_visited':0,
            'all_changes':[[*row,a.get(row),b.get(row)]for row in sorted(edits)],
            'scope':'An exact finite blank prefix and calibrated frame. '
                    'This does not assert actual nonhalting.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('parent');p.add_argument('candidate')
    p.add_argument('source');p.add_argument('--output',required=True);a=p.parse_args()
    r=audit(a.parent,a.candidate,a.source)
    r['input_sha256']={k:hashlib.sha256(Path(getattr(a,k)).read_bytes()).hexdigest()
                       for k in('parent','candidate','source')}
    Path(a.output).write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items()if k not in('one_cells','spare_registers','all_changes')},indent=2))

if __name__=='__main__':main()
