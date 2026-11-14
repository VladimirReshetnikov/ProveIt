#!/usr/bin/env python3
"""Optional bounded source-parenthesization search; no physical TM is built.

The delivered recipe can be reconstructed without running this heuristic.
Use --parent for an extracted u222_consistency_machine directory and
--output-dir for newly generated source candidates and the search summary.
"""
from pathlib import Path
import argparse, importlib.util, sys, json, functools, heapq
sys.dont_write_bytecode=True
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--parent',type=Path,required=True)
parser.add_argument('--output-dir',type=Path,required=True)
parser.add_argument('--beam',type=int,default=12)
args=parser.parse_args()
if args.beam<1:raise ValueError('beam must be positive')
BASE=args.parent.resolve()
ROOT=args.output_dir.resolve()
ROOT.mkdir(parents=True,exist_ok=True)
spec=importlib.util.spec_from_file_location('pinned_source_builder',BASE/'code/build_source.py')
B=importlib.util.module_from_spec(spec)
spec.loader.exec_module(B)

@functools.cache
def nodes(t):
    return frozenset([t]) if B.leaf(t) else nodes(t[0])|nodes(t[1])|{t}

@functools.cache
def depth(t):
    if B.leaf(t):return (0,0,0)
    a,b=depth(t[0]),depth(t[1]); lead=a[1]+1
    return max(a[0],b[0])+1,lead,max(a[2],b[2],lead)

old=B.parse(json.loads((BASE/'inputs/k215_sites.json').read_text()))
rec=json.loads((BASE/'inputs/source_recipe.json').read_text())
mac={'m'+k:B.serial(B.closed_forest(old,*v)) for k,v in rec['macro_intervals'].items()}
known=nodes(old)
alias={'c':'m168','0':'m171','1':'m177','R':'m181','I':'m119','Q':'m180','N':'m218'}

def postfix(t):
    if not isinstance(t,tuple):return [str(t)]
    if t[0]=='N':return postfix(t[1])+['N']
    return postfix(t[1])+postfix(t[2])+[t[0]]

def shell(order,commute):
    c='c'; e=('R',1,c); g=('Q',c,('I',('R',c,1),('R',c,0)))
    u=('Q',1,('I',e,c)); l=('Q',1,('I',c,('I',g,e)) if commute else ('I',g,('I',c,e)))
    x,y=(u,l) if order else (l,u)
    return ('Q',c,('I',x,('N',y)))

def optimize(tokens,beam):
    atoms=[mac[alias[x]] for x in tokens]
    n=len(atoms);dp={}
    for i,a in enumerate(atoms):dp[i,i+1]=[(a,nodes(a)-known)]
    for width in range(2,n+1):
        for i in range(n-width+1):
            j=i+width; opts={}
            for k in range(i+1,j):
                for a,sa in dp[i,k]:
                    for b,sb in dp[k,j]:
                        t=(a,b)
                        if depth(t)[2]>6:continue
                        s=sa|sb
                        if t not in known:s=s|{t}
                        if t not in opts:opts[t]=s
            dp[i,j]=heapq.nsmallest(beam,opts.items(),key=lambda x:(len(x[1]),depth(x[0])[2],depth(x[0])[0],repr(x[0])))
    winners=[]
    for t,s in dp[0,n]:
        full=B.splice(old,2885,4482,t); m=B.metrics(full)
        if m['maximum_zero_run']<=6:winners.append((m,full,t))
    return sorted(winners,key=lambda x:(x[0]['dag_nodes'],x[0]['maximum_depth']))

if __name__=='__main__':
    beam=args.beam
    reports=[]
    for order in (0,1):
        for commute in (0,1):
            tokens=postfix(shell(order,commute))
            name=f'order{order}-commute{commute}-beam{beam}'
            winners=optimize(tokens,beam)
            print(name,tokens, len(winners),flush=True)
            for rank,(m,t,repl) in enumerate(winners[:3]):
                filename=name+f'-rank{rank}.sites.json'
                (ROOT/filename).write_text(json.dumps(B.sites(t),separators=(',',':'))+'\n')
                reports.append({'name':name,'rank':rank,'filename':filename,'metrics':m,'tokens':tokens})
            if winners:print(winners[0][0],flush=True)
    (ROOT/f'dp-results-beam{beam}.json').write_text(json.dumps(reports,indent=2)+'\n')
