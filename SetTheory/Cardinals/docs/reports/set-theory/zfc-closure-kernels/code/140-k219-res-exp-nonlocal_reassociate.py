#!/usr/bin/env python3
"""Enumerate nonlocal reassociations of closed blocks in interned DAG space.

This permits intermediate source DAGs to grow: only the final replacement
is scored. It therefore goes beyond sequences of node-neutral rotations.
"""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
import argparse,json,time,hashlib,sys
from search_general import s,b,BASE,WORK,PARENT


class Dag:
    def __init__(self):
        self.nodes=[];self.index={};self.count=[];self.boundary=[];self.leading=[];self.zero=[];self.depth=[]
    def add(self,n):
        if n in self.index:return self.index[n]
        q=len(self.nodes);self.nodes.append(n);self.index[n]=q
        if isinstance(n[0],str):
            op,arg=n;self.count.append(1);self.leading.append(0);self.zero.append(0);self.depth.append(0)
            self.boundary.append((1,0,False) if op=='CD' else (arg,0,False) if op=='CB' else (0,arg,False) if op=='CC' else (0,0,op=='CH'))
        else:
            a,b=n;self.count.append(self.count[a]+self.count[b]);self.leading.append(1+self.leading[a]);self.zero.append(max(1+self.leading[a],self.zero[a],self.zero[b]));self.depth.append(1+max(self.depth[a],self.depth[b]))
            x,y=self.boundary[a],self.boundary[b];self.boundary.append((max(x[0]-1,y[0],0),max(x[1],y[1]-1,0),x[2] or y[2]))
        return q
    def intern(self,n):return self.add(n if s.leaf(n) else (self.intern(n[0]),self.intern(n[1])))
    def leaf(self,q):return isinstance(self.nodes[q][0],str)
    def reach(self,q):
        seen=set();todo=[q]
        while todo:
            i=todo.pop()
            if i in seen:continue
            seen.add(i)
            if not self.leaf(i):todo.extend(self.nodes[i])
        return seen
    def tree(self,q):
        @lru_cache(None)
        def rec(i):
            n=self.nodes[i]
            return n if self.leaf(i) else (rec(n[0]),rec(n[1]))
        return rec(q)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--sites',type=Path,default=BASE/'machine/sites220.json');ap.add_argument('--max-atoms',type=int,default=8)
    ap.add_argument('--out',type=Path,default=WORK/'research_root/nonlocal');ap.add_argument('--retain',type=int,default=300)
    ap.add_argument('--threshold',type=int,default=208);args=ap.parse_args();args.out.mkdir(exist_ok=True,parents=True)
    oldtree=s.tree(json.loads(args.sites.read_text()));d=Dag();root=d.intern(oldtree);oldn=len(d.nodes)
    oldparents=defaultdict(set)
    for q,n in enumerate(d.nodes):
        if not d.leaf(q):
            for ch in n:oldparents[ch].add(q)
    started=time.monotonic();examined=0;best=oldn;retained=0;hits=[];seenroots=set();frontiercount=0
    for x in range(oldn):
        d=Dag();root=d.intern(oldtree);seenroots=set()
        if d.leaf(x) or d.boundary[x]!=(0,0,False):continue
        def can_split(q):return not d.leaf(q) and all(d.boundary[ch]==(0,0,False) for ch in d.nodes[q])
        frontiers=set()
        for strategy in ('largest','smallest','left','right','depth'):
            f=[x]
            while len(f)<args.max_atoms:
                options=[i for i,q in enumerate(f) if can_split(q)]
                if not options:break
                if strategy=='largest':i=max(options,key=lambda i:d.count[f[i]])
                elif strategy=='smallest':i=min(options,key=lambda i:d.count[f[i]])
                elif strategy=='left':i=options[0]
                elif strategy=='right':i=options[-1]
                else:i=max(options,key=lambda i:d.depth[f[i]])
                f[i:i+1]=d.nodes[f[i]]
                if len(f)>=3:frontiers.add(tuple(f))
        affected={x};todo=[x]
        for q in todo:
            for p in oldparents[q]:
                if p not in affected:affected.add(p);todo.append(p)
        ordered=sorted(affected)
        for f in sorted(frontiers,key=lambda v:(len(v),v)):
            frontiercount+=1
            @lru_cache(None)
            def shapes(i,j):
                if j-i==1:return (f[i],)
                result=[]
                for k in range(i+1,j):
                    for a in shapes(i,k):
                        for bb in shapes(k,j):result.append(d.add((a,bb)))
                return tuple(result)
            for newx in shapes(0,len(f)):
                if newx==x:continue
                mapping={x:newx}
                for q in ordered:
                    if q==x:continue
                    a,bb=d.nodes[q];mapping[q]=d.add((mapping.get(a,a),mapping.get(bb,bb)))
                newroot=mapping.get(root,root)
                if newroot in seenroots:continue
                seenroots.add(newroot);examined+=1
                if d.zero[newroot]>6:continue
                reachable=d.reach(newroot);score=len(reachable)
                if score<best:
                    best=score;print('BEST',best,'node',x,'atoms',len(f),'trials',examined,'sec',round(time.monotonic()-started,1),flush=True)
                if score>args.threshold:continue
                if retained>=args.retain and score>=208:continue
                newtree=d.tree(newroot);rows=s.sites(newtree)
                # Strictly closed factors guarantee CFG, recheck separately on each retained candidate.
                cfg,_=s.graph_arithmetic(rows)
                if cfg!=s.graph_intervals(rows):raise AssertionError('Resolvers disagree')
                if cfg!=s.graph_intervals(s.sites(oldtree)):raise AssertionError('Closed reassociation changes CFG')
                retained+=1;name=f'candidate{retained:05d}'
                (args.out/(name+'.sites.json')).write_bytes(s.compact(rows))
                rec=dict(candidate=name,dag_nodes=score,old_node=x,old_node_leaf_count=d.count[x],frontier=f,frontier_lengths=[d.count[q] for q in f],
                    source_sha256=hashlib.sha256(s.compact(rows)).hexdigest(),new_nodes=len(reachable-set(range(oldn))),removed_nodes=len(set(range(oldn))-reachable),
                    metrics=s.metrics(newtree),status='SOURCE_EQUIVALENCE_ONLY_REQUIRES_COMPILATION_AND_RUNTIME')
                (args.out/(name+'.json')).write_text(json.dumps(rec,indent=2)+'\n');hits.append(rec)
            shapes.cache_clear()
        if len(frontiers):print('NODE',x,'frontiers',len(frontiers),'trials',examined,'kept',retained,'best',best,'sec',round(time.monotonic()-started,1),flush=True)
    summary=dict(examined=examined,best_dag_nodes=best,retained=retained,frontiers=frontiercount,seconds=time.monotonic()-started,scope='Five greedy closed frontiers per node; all Catalan reparenthesizations up to max_atoms',max_atoms=args.max_atoms,hits=hits)
    (args.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print({k:v for k,v in summary.items() if k!='hits'},flush=True)


if __name__=='__main__':main()
