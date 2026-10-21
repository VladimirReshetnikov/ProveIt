#!/usr/bin/env python3
"""Independent dense replay and complete seed-frame check for combined215."""
from pathlib import Path
import argparse,hashlib,json

def req(p,m):
    if not p:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--table',required=True);ap.add_argument('--trace',required=True);ap.add_argument('--out',required=True);a=ap.parse_args()
    actions={}
    for line in Path(a.table).read_text().splitlines():
        if not line.strip()or line.startswith('#'):continue
        fs=line.split();req(len(fs)==5,'malformed row')
        q,b,w,d,z=fs;q,b,w,z=map(int,(q,b,w,z));req(b in(0,1)and w in(0,1)and d in('L','R'),'bad action')
        req((q,b)not in actions,'duplicate row');actions[q,b]=(w,{'L':-1,'R':1}[d],z)
    states={q for q,b in actions};req(len(states)==215 and len(actions)==430,'state/row count')
    req(all((q,b)in actions for q in states for b in(0,1)),'missing row')
    req({z for w,d,z in actions.values()}-states=={254},'wrong external halt')
    record=json.loads(Path(a.trace).read_bytes());req(record['steps']==95714,'unexpected prefix count')
    req(len(record['trace'])==95714,'trace length')
    middle=10000;tape=bytearray(2*middle+1);q=0;h=middle;lo=hi=h
    for tick,expected in enumerate(record['trace']):
        req(0<=h<len(tape),'finite buffer exceeded')
        b=tape[h];req((q,b)in actions,'early halt');w,d,z=actions[q,b]
        req(expected==[q,h-middle,b,w,d,z],f'trace mismatch at {tick}')
        tape[h]=w;h+=d;q=z;lo=min(lo,h);hi=max(hi,h)
    support=[i-middle for i,x in enumerate(tape)if x]
    logical=[4,0,0,0,0,0,0,0,0];physical=[0]*9
    for j,k in enumerate((6,2,0,4,3,7,8,5,1)):physical[k]=logical[j]
    expected={-9,57};p=58
    for value in physical+[1]*40:
        expected.update(range(p+1,p+value+2));p+=value+2
    req(q==84 and h-middle==-8,'incorrect final control')
    req(support==sorted(expected),'incorrect complete frame')
    req(record['one_cells']==support and record['registers']==logical and record['spares']==[1]*40,'receipt frame mismatch')
    req(record['gap']==1 and record['head']==-8 and record['state']==84,'receipt control mismatch')
    result={'status':'PASS','table_sha256':sha(a.table),'trace_sha256':sha(a.trace),'checker_sha256':sha(__file__),'working_states':215,'rows':430,'blank_steps':95714,'dispatcher':84,'head':-8,'gap':1,'header_position':57,'logical_registers':logical,'spare_count':40,'spare_value':1,'one_cells':support,'one_count':len(support),'visited_interval':[lo-middle,hi-middle],'complete_trace_rows_compared':95714,'scope':'Finite exact blank prefix and whole-tape endpoint. Independent replay uses a checked dense buffer and a direct seed-frame construction; no runtime/compiler helper imported.'}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='one_cells'},indent=2))
if __name__=='__main__':main()
