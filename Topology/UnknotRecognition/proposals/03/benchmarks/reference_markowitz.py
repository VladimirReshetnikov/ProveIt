"""Validation only: original explicit cobordism algebra, changed pivot scheduler.

NOT the unchanged baseline used in speedup denominators. This independent
representation checks the packed engine on instances too large for the cube.
"""
from collections import defaultdict
from heapq import heappop, heappush
from time import monotonic
from fastunknot import scan as old


class ReferenceMarkowitz(old.ScanComplex):
    def eliminate(self):
        queue = []
        def cost(a, b):
            return (len(self.out[a])-1)*(len(self.inc[b])-1)
        def push(a, b):
            heappush(queue, (cost(a,b), a, b))
        for a in list(self.out):
            for b in self.out[a]:
                if self._invertible(a,b):
                    push(a,b)
        while queue:
            self._check()
            priority,b,c=heappop(queue)
            if b not in self.objects or c not in self.objects or not self._invertible(b,c):
                continue
            if priority != cost(b,c):
                push(b,c)
                continue
            m=self.objects[b].matching
            inv=old.inverse(self.out[b][c],m)
            ins=[(a,self.out[a][c]) for a in sorted(self.inc[c]) if a!=b]
            outs=[(f,self.out[b][f]) for f in self.out[b] if f!=c]
            for a,delta in ins:
                self._check()
                ma=self.objects[a].matching
                half=old.compose(delta,inv,ma,m,m)
                for f,gamma in outs:
                    term=old.compose(half,gamma,ma,m,self.objects[f].matching)
                    self.stats['compositions']+=2
                    if term:
                        current=self.out[a].get(f,set()) ^ term
                        self._set(a,f,current)
                        if current and self._invertible(a,f):
                            push(a,f)
            for x in (b,c):
                for y in list(self.out[x]):self._set(x,y,set())
                for y in list(self.inc[x]):self._set(y,x,set())
                del self.objects[x]
                self.out.pop(x,None);self.inc.pop(x,None)
            self.stats['eliminations']+=1


def reference_rank(pd, seconds=None):
    order=old.best_scan_order(pd,tries=min(12,len(pd)))
    c=ReferenceMarkowitz(deadline=None if seconds is None else monotonic()+seconds)
    for i in order:c.add_crossing(pd[i])
    return {'rank':c.total_rank(),'reduced_rank':c.total_rank()//2,
            'by_degree':c.ranks_by_degree(),'stats':c.stats,'order':order}
