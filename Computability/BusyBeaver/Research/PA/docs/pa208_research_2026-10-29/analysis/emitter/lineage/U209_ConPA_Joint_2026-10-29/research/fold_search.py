#!/usr/bin/env python3
"""Search one-row contextual folds, with exhaustive local branch checking."""
from pathlib import Path
import argparse,json,random,time
from alias_search import read,tags

def exact(old,new,q,r,entry,oldbit,limit):
    initial={entry[0]:entry[1],0:oldbit}
    ow,od,oz=old[q,oldbit];target=oz
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
                v=dict(values);v[p]=b;stack.append((s,p,dict(writes),v,list(trace)))
            continue
        w,d,z=new[s,bit];wn=dict(writes);wn[p]=w
        stack.append((z,p+d,wn,values,trace+[[s,p,bit,w,d,z]]))
        if len(stack)+len(cert)>4096:return None
    return cert

def finite(old,new,q,r,entry,oldbit,rng,limit):
    cells={i:rng.randrange(2) for i in range(-limit-2,limit+3)}
    cells[entry[0]]=entry[1];cells[0]=oldbit
    ow,od,oz=old[q,oldbit];expected=dict(cells);expected[0]=ow
    actual=dict(cells);p=0;s=r
    for k in range(1,limit+1):
        if s==254:return False
        w,d,z=new[s,actual[p]];actual[p]=w;p+=d;s=z
        if (s,p)==(oz,od) and actual==expected:return True
    return False

def main():
    a=argparse.ArgumentParser();a.add_argument('table');a.add_argument('--output',required=True);a.add_argument('--limit',type=int,default=15);a=a.parse_args()
    old=read(a.table);states=sorted({q for q,b in old});rng=random.Random(20261029);results=[];screened=0;pairs=0;start=time.monotonic()
    for i,q in enumerate(states):
        for r in states[:i]:
            if q==0 or r==0:continue
            tq,tr=tags(old,q),tags(old,r)
            if not(len(tq)==len(tr)==1 and tq[0][0]==tr[0][0]==-1 and tq!=tr):continue
            for changed_bit in (0,1):
                if old[q,1-changed_bit]!=old[r,1-changed_bit]:continue
                if any(z in (q,r) for w,d,z in [old[q,0],old[q,1],old[r,0],old[r,1]]):continue
                pairs+=1
                for helper in states:
                    if helper in (q,r):continue
                    for write in (changed_bit,1-changed_bit):
                        screened+=1
                        new={(s,b):(w,d,r if z==q else z) for (s,b),(w,d,z) in old.items() if s!=q}
                        new[r,changed_bit]=(write,-1,helper)
                        if not all(finite(old,new,s,r,e,b,rng,a.limit) for s,tag in [(q,tq),(r,tr)] for e in tag for b in (0,1) for _ in range(4)):continue
                        cases=[]
                        for s,e in [(q,tq[0]),(r,tr[0])]:
                            for b in (0,1):
                                c=exact(old,new,s,r,e,b,a.limit)
                                if c is None:break
                                cases.append({'state':s,'tag':e,'read':b,'branches':c})
                            else:continue
                            break
                        else:
                            result={'remove':q,'keep':r,'changed_row':[r,changed_bit,write,-1,helper],'cases':cases};results.append(result)
                            print('FOUND',q,'->',r,'via',helper,flush=True)
    report={'input':a.table,'pairs':pairs,'screened':screened,'limit':a.limit,'seconds':time.monotonic()-start,'results':results}
    Path(a.output).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2));print('certificates',len(results))
if __name__=='__main__':main()
