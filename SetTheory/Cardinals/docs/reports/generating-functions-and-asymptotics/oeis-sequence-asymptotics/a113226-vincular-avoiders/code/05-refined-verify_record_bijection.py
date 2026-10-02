#!/usr/bin/env python3
"""Exhaustive literal word test of the record/cycle bijection, through n=8."""
import argparse,itertools,json,math
from pathlib import Path

def valid_words(n):
    if not n:
        yield (),();return
    for tail in itertools.product((0,1),repeat=n-1):
        b=(0,)+tail
        for p in itertools.permutations(range(1,n+1)):
            zmax=0
            for i in range(n):
                if b[i]==0:
                    zmax=max(zmax,p[i])
                    if i and not b[i-1] and p[i]>p[i-1]:break
                elif p[i]<=zmax or (i and b[i-1] and p[i]<p[i-1]):break
            else:yield b,p

def split(b,p):
    runs=[]
    for bit,group in itertools.groupby(zip(b,p),key=lambda x:x[0]):runs.append((bit,tuple(x[1] for x in group)))
    isolated=()
    if runs and runs[-1][0]==0:isolated=runs.pop()[1]
    pairs=tuple((runs[2*i][1],runs[2*i+1][1]) for i in range(len(runs)//2))
    return pairs,isolated

def forward(pairs,isolated):
    cycles=[];mx=0
    for pair in pairs:
        e=max(pair[0])
        if e>mx:cycles.append([]);mx=e
        cycles[-1].append(pair)
    for cyc in cycles:
        assert max(x for E,M in cyc for x in E)<min(x for E,M in cyc for x in M)
        assert max(cyc[0][0])==max(x for E,M in cyc for x in E)
    return tuple(tuple(x) for x in cycles),tuple(sorted(isolated))

def inverse(cycles,isolated):
    canon=[]
    for cyc in cycles:
        i=max(range(len(cyc)),key=lambda i:max(cyc[i][0]));cyc=cyc[i:]+cyc[:i];canon.append(cyc)
    canon.sort(key=lambda cyc:max(cyc[0][0]))
    b=[];p=[]
    for cyc in canon:
        for E,M in cyc:b.extend([0]*len(E)+[1]*len(M));p.extend(sorted(E,reverse=True));p.extend(sorted(M))
    b.extend([0]*len(isolated));p.extend(sorted(isolated,reverse=True))
    return tuple(b),tuple(p)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=8);N=ap.parse_args().n
    S=[[0]*(N+1) for _ in range(N+1)];S[0][0]=1
    for n in range(1,N+1):
        for k in range(1,n+1):S[n][k]=k*S[n-1][k]+S[n-1][k-1]
    report=[]
    for n in range(N+1):
        total=0;one=[0]*(n//2+1)
        for b,p in valid_words(n):
            pairs,iso=split(b,p);cycles,singles=forward(pairs,iso)
            # Perturb representations by reversing set order and rotating cycles.
            distorted=tuple(cyc[1:]+cyc[:1] for cyc in cycles[::-1])
            assert inverse(distorted,singles)==(b,p)
            total+=1
            if len(cycles)==1 and not iso:one[len(pairs)]+=1
        expected=[0]+[math.factorial(k)*math.factorial(k-1)*sum(S[a][k]*S[n-a][k] for a in range(k,n-k+1)) for k in range(1,n//2+1)]
        assert one==expected
        report.append({'n':n,'roundtrips':total,'one_cycle_counts_by_pairs':one})
    out={'max_n':N,'all_roundtrips_and_component_counts_pass':True,'rows':report}
    Path(__file__).with_name('record_bijection_validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
