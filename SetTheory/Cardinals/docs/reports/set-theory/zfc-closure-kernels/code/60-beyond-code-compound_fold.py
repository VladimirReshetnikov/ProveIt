#!/usr/bin/env python3
"""Uniform folds with composable register boxes and a disposable spare suffix.

Research diagnostic, not a kernel proof or a state lower bound.  The four
unchanged box contracts are reused on arbitrarily many successive excursions.
The enclosing affine tape executor is the attributed source-27 checker.
"""
from __future__ import annotations
import argparse
from collections import Counter,defaultdict
import hashlib,importlib.util,json,sys,time
from pathlib import Path
from types import SimpleNamespace

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

INF=10**6
def close(z):
    z=[row[:] for row in z]
    for k in range(10):
        for i in range(10):
            if z[i][k]==INF:continue
            for j in range(10):
                if z[k][j]!=INF:z[i][j]=min(z[i][j],z[i][k]+z[k][j])
    return None if any(z[i][i]<0 for i in range(10)) else z

class Tracking(dict):
    def __init__(self,table):super().__init__(table);self.used=set()
    def __getitem__(self,key):self.used.add(key);return super().__getitem__(key)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    ap.add_argument('--zones',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--fuel',type=int,default=1000)
    ap.add_argument('--seconds',type=float,default=240)
    args=ap.parse_args();began=time.monotonic()
    root=args.root.resolve();data=root/'data'
    sys.dont_write_bytecode=True
    import frozen_support as audit
    phase=SimpleNamespace(PROG_SHA='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746',
                          EXCLUDED=[8202,8203,8204,8358,8359,8360])
    strictpath=root/'vendor/strict_affine.py'
    sys.modules['cost_search']=SimpleNamespace()
    strict=load('compound_strict',strictpath)
    raw=(data/'zfc_permutation252_old.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==audit.EXPECTED_SHA
    nums=audit.read_table(raw)
    table={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in nums.items()}
    prog=(data/'Prog254.v').read_bytes()
    assert hashlib.sha256(prog).hexdigest()==phase.PROG_SHA
    graph=json.loads((data/'program_cases.json').read_text())
    assert graph['source_sha256']==phase.PROG_SHA
    sites,cases,targets,first=(graph[k]for k in ('sites','cases','targets','first'))
    lines=args.zones.read_text().splitlines();n,cap,pops,updates=map(int,lines[0].split())
    assert n==len(sites) and len(lines)==n+1
    zones=[]
    for line in lines[1:]:
        row=list(map(int,line.split()))
        if not row[0]:zones.append(None);continue
        assert len(row)==101
        flat=[INF if x==999999 else x for x in row[1:]]
        zones.append([flat[i:i+10]for i in range(0,100,10)])
    invphys={p:l for l,p in enumerate(audit.NEWPHYS)}
    specs=[];excluded=[]
    for ci,(site,path,op,r,zero)in enumerate(cases):
        z=zones[site]
        if z is not None:
            z=close(z)
            if op=='CD':
                if zero:z[r+1][0]=min(z[r+1][0],0)
                else:z[0][r+1]=min(z[0][r+1],-1)
                z=close(z)
        if z is None:excluded.append(ci);specs.append(None);continue
        lo=tuple(-z[0][invphys[p]+1]for p in range(9))
        hi=tuple(z[invphys[p]+1][0]for p in range(9))
        p=audit.NEWPHYS[r]if op in('CI','CD')else r
        delta=[0]*9
        if op=='CI':delta[p]=1
        elif op=='CD'and not zero:delta[p]=-1
        state=('plain',tuple(delta)if any(delta)else None)
        nxt=audit.successor(path,op,r,zero)
        right=([('b',int(c))for c in nxt]if nxt is not None else[])
        right+=[('r',0,1,(41 if nxt is None else 40)-len(nxt or'')),('b',1),('box',state)]
        specs.append((path,op,lo,hi,strict.canon([('b',1)],right)))
    assert excluded==phase.EXCLUDED
    active=None;compound_calls=0
    def oracle(q,branch,state):
        nonlocal compound_calls
        _,_,lo,hi,_=active
        if state[0]=='plain':
            delta=(0,)*9 if state[1]is None else state[1]
            if q in strict.SKIP:
                r=strict.SKIP[q]
                if any(delta):compound_calls+=1
                return ('2'if r==0 else'6'),('mark',r,delta)
            return None
        if state[0]!='mark':return None
        _,r,d=state;delta=list(d)
        if q=='73':
            delta[r]+=1
            return '48',('plain',tuple(delta)if any(delta)else None)
        if q!='43':return None
        if hi[r]!=INF and hi[r]+delta[r]<=0:return '3',('plain',tuple(delta)if any(delta)else None)
        if lo[r]+delta[r]>=1:
            delta[r]-=1
            return ('63'if r==0 else'48'),('plain',tuple(delta)if any(delta)else None)
        return None
    strict.oracle=oracle
    def check(rows,index):
        nonlocal active
        active=specs[index]
        path,op,_,_,target=active
        try:
            rules,literal=strict.run(rows,path,None,target,halt=op=='CH',fuel=args.fuel)
            assert literal>0
            return True,sum(rules.values()),None
        except AssertionError as e:
            msg=str(e)
            return False,0,'fuel'if msg=='symbolic fuel exhausted'else msg
        except KeyError as e:return False,0,'missing '+str(e)
    allowed=[i for i,s in enumerate(specs)if s is not None]
    usage=defaultdict(list)
    for i in allowed:
        traced=Tracking(table);ok,cost,err=check(traced,i)
        assert ok,(i,err)
        for q in{q for q,b in traced.used}:usage[q].append((cost,i))
    for group in usage.values():group.sort()
    states=sorted({q for q,b in table},key=int)
    protected={(str(q),b)for q,b in audit.BOX_PAIRS}
    pt={table[k][2]for k in protected}
    eligible=[q for q in states if q!='96'and q not in pt and all((q,b)not in protected for b in(0,1))]
    assert len(eligible)==221
    print('BASELINE PASS: 8385 cases with composable boxes; search starts',flush=True)
    result=dict(scope='conditional composable-box affine contracts, phase-restricted source; disposable spare suffix',
                table_sha256=audit.EXPECTED_SHA,program_sha256=phase.PROG_SHA,
                strict_sha256=hashlib.sha256(strictpath.read_bytes()).hexdigest(),
                zone_sha256=hashlib.sha256(args.zones.read_bytes()).hexdigest(),
                driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                baseline_cases=len(allowed),excluded_cases=excluded,cap=cap,fuel=args.fuel,
                planned=55471,completed=0,checks=0,survivors=[],recipes=[])
    reasons=Counter();stop=False
    for dead in eligible:
        for target in states:
            if target==dead:continue
            if time.monotonic()-began>args.seconds:stop=True;break
            candidate={(q,b):(w,d,target if t==dead else t)for(q,b),(w,d,t)in table.items()if q!=dead}
            assert len(candidate)==502 and all(candidate[k]==table[k]for k in protected)
            fail=None
            for _,i in usage[dead]:
                ok,cost,err=check(candidate,i);result['checks']+=1
                if not ok:fail=i;break
            if fail is None:
                for i in allowed:
                    ok,cost,err=check(candidate,i);result['checks']+=1
                    if not ok:fail=i;break
            result['completed']+=1
            result['recipes'].append([int(dead),int(target),fail,err])
            if fail is None:
                result['survivors'].append([int(dead),int(target)])
                print('SURVIVOR',dead,target,flush=True)
            else:reasons[err.split(',')[0]]+=1
        if stop:break
    result.update(status='partial'if stop else'completed',seconds=time.monotonic()-began,
                  nonzero_delta_remark_calls=compound_calls,reasons=dict(reasons))
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('recipes','reasons')}),flush=True)

if __name__=='__main__':main()
