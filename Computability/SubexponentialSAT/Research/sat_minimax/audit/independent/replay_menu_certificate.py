#!/usr/bin/env python3
"""Independent exact replay of a four-plan cached-contraction menu.

Plans are input; supports and KKT certificates are rebuilt independently.
All enumeration/pruning uses integer arithmetic, all hull checks Fraction.
numpy is used only to batch exact int64 sums; values are bounded below 2^63.
"""
from fractions import Fraction as F
from itertools import permutations,combinations,product
from pathlib import Path
import json,argparse
import numpy as np
from minimax_exact import closest,serial


def make_supports(r,plan,weights=(56,47,30)):
    if sorted(v for block in plan for v in block)!=list(range(r)):raise ValueError('not a partition')
    ops=[]
    def build(block):
        if len(block)<2:return
        left=block[:len(block)//2];right=block[len(block)//2:]
        build(left);build(right)
        ops.append((left,right,[v for v in range(r) if v not in block]))
    for block in plan:build(block)
    ops.append(plan)
    den,aa,bb=weights
    forms=sorted(set(permutations((den,den,0)))|set(permutations((den,aa,bb))))
    pairs=list(combinations(range(r),2));res=[]
    for op in ops:
        labels={v:j for j,part in enumerate(op) for v in part}
        for form in forms:
            row=[]
            for a,b in pairs:
                x,y=sorted((labels[a],labels[b]))
                row.append(0 if x==y else form[{(0,1):0,(0,2):1,(1,2):2}[(x,y)]])
            res.append(row)
    return np.array(res,dtype=np.int64)


def replay(r,plans,claimed,weights=(56,47,30),require_sharp=True):
    if len(plans)!=4:raise ValueError('exact batched enumerator uses four plans')
    A=[make_supports(r,p,weights) for p in plans]
    # Q is squared norm of sum of selected vectors, not their average.
    limit=(16*claimed).numerator//(16*claimed).denominator
    ns=[np.sum(a*a,axis=1,dtype=np.int64) for a in A]
    G={(i,j):A[i]@A[j].T for i in range(4) for j in range(i+1,4)}
    core=ns[2][:,None]+ns[3][None,:]+2*G[2,3]
    maxQ=-1;uniform_witness=None;checksum=0;count=0;remaining=[];maxfound=F(0);maxcert=None
    for i in range(len(A[0])):
        for j in range(len(A[1])):
            base=ns[0][i]+ns[1][j]+2*G[0,1][i,j]
            vals=base+core+2*(G[0,2][i]+G[1,2][j])[:,None]+2*(G[0,3][i]+G[1,3][j])[None,:]
            if int(vals.max())>maxQ:
                maxQ=int(vals.max());k,l=np.unravel_index(int(vals.argmax()),vals.shape);uniform_witness=(i,j,int(k),int(l))
            checksum+=int(vals.sum());count+=vals.size
            for k,l in zip(*np.nonzero(vals>limit)):
                ids=(i,j,int(k),int(l))
                points=[tuple(map(int,a[z])) for a,z in zip(A,ids)]
                cert=closest(points)
                if cert['norm_squared']>claimed:raise ValueError(('bound false',ids,cert))
                cert['indices']=ids
                cert['gram']=[[sum(x*y for x,y in zip(v,w)) for w in points] for v in points]
                remaining.append(cert)
                if cert['norm_squared']>maxfound:maxfound=cert['norm_squared'];maxcert=cert
    total=1
    for a in A:total*=len(a)
    if count!=total:raise ValueError('tuple coverage mismatch')
    if maxfound!=claimed:
        points=[tuple(map(int,a[z])) for a,z in zip(A,uniform_witness)]
        cert=closest(points);cert['indices']=uniform_witness
        cert['gram']=[[sum(x*y for x,y in zip(v,w)) for w in points] for v in points]
        if cert['norm_squared']==claimed:maxfound=claimed;maxcert=cert
        elif require_sharp:raise ValueError(('no sharp witness found',maxfound,claimed,cert))
        else:maxfound=cert['norm_squared'];maxcert=cert
    beta=2*claimed/F(weights[0]**2*r*r)
    return {'r':r,'support_counts':list(map(len,A)),'tuples_checked':count,
            'uniform_prune_threshold_Q':limit,'uniform_max_Q':maxQ,'sum_Q_checksum':checksum,
            'exact_hull_checks':len(remaining),'certified_squared_norm_bound':claimed,'beta_squared':beta,
            'witness_certificate':maxcert,'sharp':maxfound==claimed,'nonpruned_certificates':remaining,
            'scope':'Exact finite entropy relaxation certificate; not a SAT runtime measurement.'}


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input',required=True,help='menu specification JSON')
    ap.add_argument('--output',required=True)
    args=ap.parse_args();spec=json.load(open(args.input))
    out=replay(spec['r'],spec['plans'],F(spec['claimed_norm_squared']),
               tuple(spec['weights']),spec['require_sharp'])
    out['plans']=spec['plans'];out['weights']=spec['weights']
    Path(args.output).write_text(json.dumps(serial(out),indent=2)+'\n')
    print(json.dumps({k:serial(v) for k,v in out.items() if k not in ['witness_certificate','nonpruned_certificates','plans']},indent=2))
