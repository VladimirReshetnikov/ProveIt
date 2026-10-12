"""Search-free graph-proof checker. No calls to flow search or the kernel producer.

This checks a finite graph certificate. Source-to-kernel provenance is separately
bound by source reconstruction in the CLI; that reconstruction shares normalization
code with the producer and is not advertised as an independent compression verifier.
"""
from .model import Graph

def verify_graph(g:Graph,proof:dict,k:int=3)->bool:
    try:
        if type(k)is not int or k<0 or type(proof['threshold'])is not int or proof['threshold']!=k:return False
        if proof['verdict']=='LOW_MARKED_CUT':
            colors=proof['colors']
            if len(colors)!=g.n or any(type(x)is not int or x not in (0,1) for x in colors):return False
            cut=[];marks=set()
            for e,(a,b) in enumerate(g.edges):
                if colors[a]!=colors[b]:cut.append(e)
                else:marks.add(colors[a])
            return len(cut)<=k and marks=={0,1} and proof['cut_edges']==cut
        if proof['verdict']!='NO_LOW_MARKED_CUT':return False
        records=proof['exclusions'];index=0;limit=k+1
        for i in range(len(g.edges)):
            for j in range(i+1,len(g.edges)):
                if any(a==b for a in g.edges[i] for b in g.edges[j]):continue
                if index>=len(records):return False
                record=records[index];index+=1
                if record['anchors']!=[i,j]:return False
                # Independent residual dictionary, with graph edge multiplicities.
                residual={};source=g.n;sink=g.n+1
                def add(a,b,c):residual[a,b]=residual.get((a,b),0)+c
                for a,b in g.edges:
                    if a!=b:add(a,b,1);add(b,a,1)
                for a in set(g.edges[i]):add(source,a,limit)
                for b in set(g.edges[j]):add(b,sink,limit)
                amount_total=0
                for step in record['paths']:
                    p=step['vertices'];amount=step['amount']
                    if type(amount)is not int or amount<=0 or not p or p[0]!=source or p[-1]!=sink:return False
                    if len(set(p))!=len(p) or any(type(v)is not int or not 0<=v<g.n+2 for v in p):return False
                    for a,b in zip(p,p[1:]):
                        if residual.get((a,b),0)<amount:return False
                        add(a,b,-amount);add(b,a,amount)
                    amount_total+=amount
                if amount_total!=limit:return False
        return index==len(records)
    except (KeyError,TypeError,ValueError,IndexError):return False
