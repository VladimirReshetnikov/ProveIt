#!/usr/bin/env python3
"""Independent source/prefix analysis and exact complete blank initialization."""
import argparse,hashlib,json
from pathlib import Path
from common import ROOT,need,read,write_json
from independent_source import source_info,prefix_binding
import source_language as second

def execute(table,n):
    q=head=0;ones=set();visited=set();digest=hashlib.sha256()
    for step in range(n):
        need(q!=254,'Premature halt');b=int(head in ones);w,d,z=table[q,b]
        digest.update(f'{step} {q} {head} {b} {w} {d} {z}\n'.encode());visited.add((q,b))
        ones.add(head)if w else ones.discard(head);q=z;head+=d
    return(q,head,ones),digest.hexdigest(),visited

def check(machine,output):
    machine=Path(machine);base=read(ROOT/'baseline/u212.native.tm');pre=read(machine/'prefold212.native.tm');final=read(machine/'u209.native.tm')
    old=json.loads((ROOT/'baseline/sites.json').read_text());new=json.loads((machine/'sites.json').read_text())
    p0,b0,g0,m0=source_info(old);p1,b1,g1,m1=source_info(new)
    need(g0==g1,'Full effect/control graph changed')
    ga=second.graph_arithmetic(new)[0];gi=second.graph_intervals(new)
    need(ga==gi==second.graph_arithmetic(old)[0],'Binary and interval source resolvers differ')
    maximum={}
    for name,table,prefixes in[('parent',base,p0),('prefold',pre,p1),('final',final,p1)]:
        bindings,steps=prefix_binding(table,prefixes);need(len(bindings)==3908,'Prefix count');maximum[name]=steps
    changed={q for(q,b),a in pre.items()if a!=base[q,b]}
    backward=[[q,b,*a]for(q,b),a in sorted(base.items())if a[2]in changed and a[1]==-1]
    need(backward==[[171,0,0,-1,7]],'Unexpected backward entrance')
    a,ta,va=execute(base,48140);b,tb,vb=execute(final,48140)
    need(a==b and ta==tb,'Blank tape or transition trace differs')
    need(a[:2]==(84,-2),'Wrong dispatcher/head')
    need(new[136][0]=='001100110101010','Startup address changed')
    registers=[1,0,13,0,0,1,0,0,1];physical=[0]*9
    for i,j in enumerate((6,2,0,4,3,7,8,5,1)):physical[j]=registers[i]
    expected={-3,54}|{-2+i for i,bit in enumerate(new[136][0])if bit=='1'};position=55
    for value in physical+[1]*43:
        expected.update(range(position+1,position+value+2));position+=value+2
    need(a[2]==expected and len(expected)==120,'Whole canonical startup frame')
    row_delta={k for k in set(base)|set(final)if base.get(k)!=final.get(k)}
    need(not va&row_delta,'Startup traverses edited row')
    regs=[1,0,4,0,0,1,0,0,1];ordinal=106;source_trace=[]
    for _ in range(141):
        before=[ordinal,regs.copy()];op,arg,targets=g1[ordinal]
        if op=='CI':regs[arg]+=1;ordinal=targets[0]
        elif op=='CD':positive=regs[arg]>0;regs[arg]-=int(positive);ordinal=targets[int(positive)]
        elif op in('CB','CC'):ordinal=targets[0]
        else:raise ValueError('Source prefix halted')
        source_trace.append([*before,ordinal,regs.copy()])
    need((ordinal,regs)==(136,registers),'Source startup bridge')
    report={'status':'SOURCE_INTERFACE_STARTUP_PASS','primitives':3909,'control_edges':sum(len(z)for op,arg,z in g1),
      'guarded_cases':3909+sum(op=='CD'for p,op,arg in new),'internal_prefixes':3908,
      'maximum_prefix_steps':maximum,'source_metrics':m1,'backward_entries':backward,
      'changed_addresses':sum(a[0]!=b[0]for a,b in zip(old,new)),
      'startup':{'steps':48140,'state':84,'head':-2,'header':54,'header_distance':56,'source_ordinal':136,
        'source_address':new[136][0],'logical_registers':registers,'spares':[1]*43,'one_cells':sorted(expected),
        'zero_exterior':True,'entire_trace_equal':True,'trace_sha256':ta,'changed_row_visits':0,
        'source_seed_ordinal':106,'source_seed':[1,0,4,0,0,1,0,0,1],'source_prefix_steps':141,'source_prefix_trace':source_trace},
      'scope':'Exact source graph, literal decoder prefixes, blank startup and finite source bridge. Unbounded runtime is checked separately.'}
    write_json(output,report);return report
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--machine',type=Path,default=ROOT/'machine');p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    r=check(a.machine,a.output);print(json.dumps({k:v for k,v in r.items()if k!='startup'},indent=2))
