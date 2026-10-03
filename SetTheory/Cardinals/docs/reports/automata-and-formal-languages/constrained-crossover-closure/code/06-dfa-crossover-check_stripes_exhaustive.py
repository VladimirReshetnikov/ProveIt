"""Independent small exhaustive safe-core/stripe audit using exact pair cycles."""
import itertools, math, json

def audit(delta,final):
    n=len(delta); full=(1<<n)-1
    def fw(x):
        ans=0
        for q in range(n):
            if x>>q&1:
                for v in delta[q]:ans|=1<<v
        return ans
    def bw(x):
        return sum(1<<q for q in range(n) if any(x>>v&1 for v in delta[q]))
    seen={}; seq=[]; pair=(1,final)
    while pair not in seen:
        seen[pair]=len(seq);seq.append(pair);pair=(fw(pair[0]),bw(pair[1]))
    t=seen[pair]; per=len(seq)-t
    # Use a common period divisible by every SCC period, including irrelevant SCCs.
    p=math.lcm(per,*range(1,n+1))
    def stable(a,which):return seq[t+(a-t)%per][which]
    reaches=[]
    for q in range(n):
        x=1<<q
        while True:
            y=x|fw(x)
            if x==y:break
            x=y
        reaches.append(x)
    scc=[];assigned=0
    for q in range(n):
        if assigned>>q&1:continue
        members=[v for v in range(n) if reaches[q]>>v&1 and reaches[v]>>q&1]
        mask=sum(1<<v for v in members);assigned|=mask
        if len(members)==1 and q not in delta[q]:continue
        ds={q:0};queue=[q]
        for u in queue:
            for v in delta[u]:
                if mask>>v&1 and v not in ds:ds[v]=ds[u]+1;queue.append(v)
        d=0
        for u in members:
            for v in delta[u]:
                if mask>>v&1:d=math.gcd(d,ds[u]+1-ds[v])
        scc.append((members,mask,ds,d))
    checked=0
    for r in range(p):
        if not stable(r,0)&final:continue
        S=[stable(a,0)&stable(r-a,1) for a in range(p)]
        C=[tuple(c for c in (0,1) if any((S[a]>>q&1) and (S[(a+1)%p]>>delta[q][c]&1) for q in range(n))) for a in range(p)]
        U=S[:]
        while True:
            V=[sum(1<<q for q in range(n) if U[a]>>q&1 and all(U[(a+1)%p]>>delta[q][c]&1 for c in C[a])) for a in range(p)]
            if V==U:break
            U=V
        good=False
        for members,mask,ds,d in scc:
            for h in range(d):
                stripe=[(a,q) for a in range(p) for q in members if (a-ds[q])%d==h]
                viability=[bool(S[a]>>q&1) for a,q in stripe]
                assert all(viability) or not any(viability),('nonuniform',delta,final,r,h)
                if all(viability) and all(mask>>delta[q][c]&1 for a,q in stripe for c in C[a]):good=True
        assert good==any(U),('counterexample',delta,final,r)
        checked+=1
    return checked

counts={};residues=0
for n in range(1,4):
    cases=0
    for mapping in itertools.product(range(n),repeat=2*n):
        delta=[mapping[2*q:2*q+2] for q in range(n)]
        for final in range(1<<n):
            residues+=audit(delta,final);cases+=1
    counts[n]=cases
print(json.dumps({'status':'PASS','complete_binary_dfas_by_states':counts,'live_residue_checks':residues},indent=2))
