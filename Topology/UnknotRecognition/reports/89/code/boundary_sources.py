"""Actual degree-two boundary sources: binary polygon circles and marked edges.

These are interface models, not triangulated knot exteriors.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Sequence
from moment_kernel import Pairing, Kernel, compile_kernel, assemble_kernel, Oracle

@dataclass(frozen=True)
class CircleSource:
    lengths: tuple[int,...]
    marks: tuple[tuple[int,int],...]
    silent_points: int=0
    def validate(self):
        if any(type(n) is not int or n<1 for n in self.lengths):raise ValueError('nonempty circles required')
        if type(self.silent_points) is not int or self.silent_points<0:raise ValueError('invalid silent count')
        if len(set(self.marks))!=len(self.marks):raise ValueError('duplicate marked source edge')
        for c,e in self.marks:
            if type(c) is not int or type(e) is not int or not 0<=c<len(self.lengths) or not 0<=e<self.lengths[c]:
                raise ValueError('invalid source mark')
    def packet(self):
        self.validate();starts=[];at=0
        for n in self.lengths:starts.append(at);at+=n
        terminals=[];owners=[]
        for c,e in self.marks:
            start=starts[c];terminals.extend((start+e,start+(e+1)%self.lengths[c]));owners.append(c)
        pairs=[];mass=[]
        for c,n in enumerate(self.lengths):
            base=starts[c];marks=sorted(e for cc,e in self.marks if cc==c)
            # Unmarked edge runs [a,b); last edge is handled as a singleton bridge.
            at=0
            for stop in marks+[n]:
                if at<stop:
                    mass.append((base+at,base+stop,1))
                    end=min(stop,n-1)
                    if at<end:pairs.append(Pairing(base+at,base+end-1,base+at+1,base+end))
                    if stop==n and at<=n-1:pairs.append(Pairing(base+n-1,base+n-1,base,base))
                at=stop+1
        return (sum(self.lengths)+self.silent_points,pairs,terminals,mass,owners,[1]*len(self.lengths))
    def compile(self,oracle: Oracle)->Kernel:
        return compile_kernel(*self.packet(),oracle)
    def direct_pairs(self):
        """Source-order oracle, independent of interval connectivity and moments."""
        result=[]
        for c,n in enumerate(self.lengths):
            marks=sorted((e,j) for j,(cc,e) in enumerate(self.marks) if cc==c)
            for k,(e,j) in enumerate(marks):
                f,nextj=marks[(k+1)%len(marks)]
                length=(f-e-1)%n
                a,b=2*j+2,2*nextj+1
                result.append((min(a,b),max(a,b),length))
        return tuple(sorted(result))


def forget_ports(kernel: Kernel, keep: Sequence[int]) -> Kernel:
    """Coarsen by unmarking whole unit source edges. IDs in keep are zero-based.

    No source query; paths are spliced and their integer lengths are added.
    Remaining port IDs are renumbered in the order of keep.
    """
    p=len(kernel.port_owners)
    if len(set(keep))!=len(keep) or any(type(j) is not int or not 0<=j<p for j in keep):
        raise ValueError('invalid kept ports')
    kept=set(keep);gap={}
    for a,b,l in kernel.pairs:gap[a]=(b,l);gap[b]=(a,l)
    relabel={2*j+e+1:2*k+e+1 for k,j in enumerate(keep) for e in (0,1)}
    result=[];seen=set()
    for start in relabel:
        if start in seen:continue
        x=start;length=0;steps=0
        while True:
            y,l=gap[x];length+=l
            if (y-1)//2 in kept:break
            # Reinsert the old marked unit edge into the residual path.
            length+=1;x=y+1 if y%2 else y-1;steps+=1
            if steps>p:raise ValueError('malformed continuation graph')
        seen.update((start,y));a,b=sorted((relabel[start],relabel[y]));result.append((a,b,length))
    bcounts=tuple(a+b for a,b in zip(kernel.active_counts,kernel.passive_counts))
    return assemble_kernel(tuple(sorted(result)),[kernel.port_owners[j] for j in keep],bcounts,0)
