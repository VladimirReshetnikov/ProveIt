#!/usr/bin/env python3
"""Experimental conservative deoptimization of context-dependent decoder entries.

Every accepted output must pass the unchanged Box-conditional affine suite and
literal bootstrap. This is not a source-equivalence or kernel proof.
"""
from __future__ import annotations
import argparse,inspect,json,sys,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent/'compiler_reduction'))
import search_structural as s

# Exact partition of the old gap n+40: one case n=0 and one n=m+1.
# Only the two coefficients of the initial zero run change; every transition
# and every oracle rule is the pinned strict checker rule.
_run_text=inspect.getsource(s.strict.run).replace('fuel=20000):','fuel=20000,gap_a=1,gap_c=40):').replace("('r',0,1,40-len(pc))","('r',0,gap_a,gap_c-len(pc))")
_run_globals=dict(s.strict.__dict__);exec(compile(_run_text,'<gap-substitution>','exec'),_run_globals)
gap_run=_run_globals['run']

def check(table,nodes,root):
    traced=s.Tracking({(str(q),b):(w,d,str(t)) for(q,b),(w,d,t) in table.items()})
    count=0;cs=list(s.cases(nodes,root));tail=max(41,max(len(x[0]) for x in cs)+6)
    partitions=[(0,c) for c in range(40,tail)]+[(1,tail)]
    for p,e,zero,physical,target in cs:
        for a,c in partitions:
            sides=[]
            for side in target:
                sides.append(tuple(seg if seg[0]=='box' else (seg[0],seg[1]*a,seg[2]+seg[1]*(c-40)) for seg in side if seg[0]=='box' or seg[1]*a or seg[2]+seg[1]*(c-40)))
            try:gap_run(traced,p,(physical,zero) if e[0]=='D' else None,tuple(sides),halt=e[0]=='H',fuel=2000,gap_a=a,gap_c=c)
            except (AssertionError,KeyError) as ex:
                return {'passed':False,'cases_passed':count,'failure':{'path':p,'operation':e,'zero':zero,'gap_a':a,'gap_c':c,'reason':str(ex)}},traced.used
        count+=1
    return {'passed':True,'cases_passed':count,'gap_partitions_per_case':len(partitions),'gap_partitions':partitions},traced.used

def emit(nodes,root,forced):
    fp=s.fingerprints(nodes)
    old={n:s.OLD_FP.get(fp[n]) for n in nodes}
    # A deoptimized child needs an explicit parent edge. Expand ancestors only
    # where the old row is opaque, and preserve purely forwarding decoder rows.
    changed=set(forced)|{n for n in nodes if old[n] is None}
    while True:
        new={n for n,pair in nodes.items() if any(e[0]=='N' and e[1] in changed for e in pair)}
        if new<=changed:break
        changed|=new
    entries={n:96 if n==root else 1000+n if n in changed else s.NODE_LABELS[old[n]] for n in nodes}
    table=s.BASE.copy()
    # Generic arithmetic entry. Unlike coalesced original entries, these do
    # not inspect the prefix preceding the instruction leaf.
    def arithmetic(e):
        k,r=e;q=2000+2*r+(k=='D')
        table[q,0]=0,'R',57 if k=='I' else 30
        table[q,1]=0,'R',s.audit.SKIP[s.audit.NEWPHYS[r]]
        return q
    def breaker(k):
        if k==0:return 7
        q=2100+k
        if (q,0) not in table:
            table[q,0]=0,'L',breaker(k-1)
            table[q,1]=0,'L',q
        return q
    def continuer(k):
        assert k>=1
        q=2200+k
        if (q,0) not in table:
            table[q,0]=0,'L',q
            table[q,1]=(0,'R',10) if k==1 else (0,'L',continuer(k-1))
        return q
    def trans(e,b):
        k=e[0]
        if k=='N':return b,'R',entries[e[1]]
        if k in 'ID':return b,'R',arithmetic(e)
        if k=='H':return b,'R',254
        n=e[1]
        if k=='B':
            if n==0:return (1,'R',10) if b==0 else (0,'L',7)
            return 0,'L',breaker(n-(b==0))
        if k=='C':
            if n==0:return b,'R',10
            if b==1 and n==1:return 0,'R',10
            return 0,'L',continuer(n-(b==1))
        raise ValueError(e)
    for n in changed|{root}:
        for b,e in enumerate(nodes[n]):table[entries[n],b]=trans(e,b)
    assert all(table[k]==s.BASE[k] for k in s.audit.BOX_PAIRS)
    return table,entries,changed,old

def pathnodes(nodes,root,p):
    n=root;out=[]
    for b in p:
        out.append(n);e=nodes[n][int(b)]
        if e[0]!='N':return out
        n=e[1]
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('--output',type=Path,default=Path('work/context-repair'));ap.add_argument('--shorten',action='store_true');a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    d=json.loads(a.input.read_text());nodes={int(k):tuple(map(tuple,v)) for k,v in d['nodes'].items()};root=d['root'];forced=set();history=[];begun=time.monotonic()
    for it in range(len(nodes)+1):
        table,entries,changed,old=emit(nodes,root,forced)
        if a.shorten:
            table={(q,b):(w,m,84 if t==74 else t) for (q,b),(w,m,t) in table.items() if q!=74}
        runtime,used=check(table,nodes,root)
        rr=dict(iteration=it,forced=sorted(forced),changed=len(changed),runtime=runtime,runtime_states=len({q for q,b in used|s.audit.BOX_PAIRS}))
        print(it,len(changed),runtime,flush=True)
        history.append(rr)
        if runtime['passed']:
            boot,bu=s.boot(table,1000000);rr['boot']=boot
            rr['symbolic_retained_states']=len(s.prune(table,used))//2
            if boot['outcome']=='zero_root':
                table=s.prune(table,used|bu);rr['working_states']=len(table)//2
                (a.output/'candidate.tm').write_bytes(s.audit.encode(table))
            break
        p=runtime['failure']['path'];path=pathnodes(nodes,root,p)
        choices=[n for n in path if n not in changed and s.NODE_LABELS[old[n]] not in s.PURE]
        if not choices:choices=[n for n in path if n not in changed]
        if not choices:
            rr['unrepaired_failure']=True;break
        forced.add(choices[0])
    out=dict(input=str(a.input),shortened=a.shorten,history=history,elapsed_seconds=time.monotonic()-begun)
    (a.output/'results.json').write_text(json.dumps(out,indent=2)+'\n')
    print('END',json.dumps({k:v for k,v in rr.items() if k!='boot'}),flush=True)
if __name__=='__main__':main()
