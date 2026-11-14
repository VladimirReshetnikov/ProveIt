#!/usr/bin/env python3
"""Discovery screen and exact bounded local alias certificates.

For each noninitial state q, the disjunction of incoming-edge tags is exhaustive.
An accepted alias replaces q by r and simulates each old q step by a positive
number of new steps, without reading any unspecified bits except by branching.
No finite simulation is represented as a consistency proof.
"""
from pathlib import Path
import argparse, json, random, time

def read(path):
    table={}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();table[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
    return table

def tags(table,q):
    return sorted({(-d,w) for (p,b),(w,d,z) in table.items() if z==q})

def small_check(table,q,r,entry,oldbit,rng,limit):
    cells={i:rng.randrange(2) for i in range(-limit-2,limit+3)}
    cells[entry[0]]=entry[1];cells[0]=oldbit
    ow,od,oz=table[q,oldbit];target= r if oz==q else oz
    expected=dict(cells);expected[0]=ow
    actual=dict(cells);p=0;s=r
    for k in range(1,limit+1):
        if s==254:return False
        w,d,z=table[s,actual[p]]
        actual[p]=w;p+=d;s=r if z==q else z
        if (s,p)==(target,od) and actual==expected:return True
    return False

def exact_case(table,q,r,entry,oldbit,limit):
    initial={entry[0]:entry[1],0:oldbit}
    ow,od,oz=table[q,oldbit];target=r if oz==q else oz
    stack=[(r,0,{},initial,[])];cert=[]
    while stack:
        s,p,writes,values,trace=stack.pop()
        if trace and (s,p)==(target,od):
            positions=set(writes)|{0}
            if all(writes.get(x,values.get(x,('v',x))) == (ow if x==0 else values.get(x,('v',x))) for x in positions):
                cert.append({'initial':values,'trace':trace,'target':[target,od]});continue
        if len(trace)>=limit or s==254:return None
        bit=writes.get(p,values.get(p))
        if bit is None:
            for b in (0,1):
                v=dict(values);v[p]=b
                stack.append((s,p,dict(writes),v,list(trace)))
            continue
        w,d,z=table[s,bit];z=r if z==q else z
        wn=dict(writes);wn[p]=w
        stack.append((z,p+d,wn,values,trace+[[s,p,bit,w,d,z]]))
        if len(stack)+len(cert)>16384:return None
    return cert

def main():
    a=argparse.ArgumentParser();a.add_argument('table');a.add_argument('--output',required=True);a.add_argument('--limit',type=int,default=13);a=a.parse_args()
    table=read(a.table);states=sorted({q for q,b in table});rng=random.Random(292110)
    results=[];screened=0;began=time.monotonic()
    for q in states:
        if q==0:continue
        ins=tags(table,q)
        if not ins:continue
        for r in states:
            if r==q:continue
            screened+=1
            if not all(small_check(table,q,r,e,b,rng,a.limit) for e in ins for b in (0,1) for _ in range(6)):continue
            cases=[]
            for e in ins:
                for b in (0,1):
                    c=exact_case(table,q,r,e,b,a.limit)
                    if c is None:break
                    cases.append({'entry_tag':e,'scanned':b,'branches':c})
                else:continue
                break
            else:
                item={'remove':q,'representative':r,'cases':cases}
                results.append(item);print('FOUND',q,'->',r,flush=True)
    report={'input':a.table,'max_macro_steps':a.limit,'ordered_aliases_screened':screened,'seconds':time.monotonic()-began,'results':results,'scope':'Bounded discovery is incomplete; accepted cases are exhaustive symbolic local identities over arbitrary tape exterior.'}
    Path(a.output).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2));print('certificates',len(results))

if __name__=='__main__':main()
