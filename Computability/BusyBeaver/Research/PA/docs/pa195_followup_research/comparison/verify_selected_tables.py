#!/usr/bin/env python3
"""Independent structural audit of the selected comparison tables.

This verifies exact finite table properties, not PA consistency calibration.
Python's -O does not disable any required check.
"""
import hashlib,json
from collections import defaultdict
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def require(condition,message):
    if not condition:raise ValueError(message)

def fingerprint(data):
    rows={}
    for line in data.decode('ascii').splitlines():
        if not line.strip() or line.lstrip().startswith('#'):continue
        x=line.split()
        require(len(x)==5,'Malformed transition row')
        q,r,w,d,n=x;q,r,w,n=map(int,(q,r,w,n))
        require(q>=0 and n>=0 and r in (0,1) and w in (0,1) and d in ('L','R'),'Invalid row value')
        require((q,r) not in rows,'Duplicate row')
        rows[q,r]=(w,d,n)
    states={q for q,r in rows};nstate=len(states)
    require(states==set(range(nstate)),'Working state set is not dense')
    require(set(rows)=={(q,r) for q in states for r in (0,1)},'Non-total table')
    halts={n for w,d,n in rows.values()}-states
    require(halts=={nstate},'Halt convention mismatch')
    ids={0:0};order=[0]
    for q in order:
        for r in (0,1):
            n=rows[q,r][2]
            if n!=nstate and n not in ids:
                ids[n]=len(ids);order.append(n)
    require(len(order)==nstate,'Graph-unreachable working state')
    normalized=[]
    for q in order:
        for r in (0,1):
            w,d,n=rows[q,r]
            normalized.append([ids[q],r,w,d,nstate if n==nstate else ids[n]])
    digest=hashlib.sha256(json.dumps(normalized,separators=(',',':')).encode()).hexdigest()
    return nstate,digest

def main():
    meta=json.loads((ROOT/'current_comparison.json').read_text())
    by_size=defaultdict(set);names=[]
    for record in meta['table_records']:
        name=record['name'];data=(ROOT/'tables'/(name+'.tm')).read_bytes()
        require(hashlib.sha256(data).hexdigest()==record['literal_sha256'],'Literal hash mismatch: '+name)
        n,digest=fingerprint(data)
        require(n==record['states'],'State count mismatch: '+name)
        require(digest==record['canonical_sha256_this_checker'],'Canonical hash mismatch: '+name)
        require(digest not in by_size[n],'Duplicate selected rooted graph: '+name)
        by_size[n].add(digest);names.append(name)
    result={'ok':True,'tables':len(names),'distinct_rooted_graphs':{str(n):len(v) for n,v in sorted(by_size.items())},'checks':['all literal hashes','total binary transition domain','dense start0 and haltN convention','all working states graph-reachable','rooted read/action-preserving canonicalization','pairwise graph nonisomorphism'],'scope':'Structural table verification only; ordinary consistency proofs and symbolic runtime evidence retain their separately recorded statuses.'}
    require(result['distinct_rooted_graphs']=={'195':1,'196':32,'197':3},'Expected corpus count changed')
    print(json.dumps(result,indent=2))
    return result
if __name__=='__main__':main()
