#!/usr/bin/env python3
"""Exact row-reduced affine spaces over prime fields; standard library only."""
class Domain:
    def __init__(self,p):self.p=p
    def canonical(self,rows):
        p=self.p;basis={}
        for raw in rows:
            r=list(raw)
            for j,b in sorted(basis.items()):
                if r[j]:
                    f=r[j];r=[(a-f*c)%p for a,c in zip(r,b)]
            try:j=next(i for i,x in enumerate(r) if x%p)
            except StopIteration:continue
            inv=pow(r[j],-1,p);r=[(a*inv)%p for a in r]
            for k,b in list(basis.items()):
                if b[j]:basis[k]=tuple((a-b[j]*c)%p for a,c in zip(b,r))
            basis[j]=tuple(r)
        return tuple(b for _,b in sorted(basis.items()))
    def normalize_affine(self,rows):
        ans=self.canonical(rows)
        return ans if ans and ans[0][0]==1 else ()
    def meet(self,B,k,value):
        if not B:return ()
        co=[(row[k+1]-value*row[0])%self.p for row in B]
        if not any(co):return B
        pivot=next(i for i,x in enumerate(co) if x)
        inv=pow(co[pivot],-1,self.p);b=B[pivot]
        return self.normalize_affine(tuple((x-co[i]*inv*y)%self.p for x,y in zip(r,b))
                                     for i,r in enumerate(B) if i!=pivot)
    def reduce(self,B,mask):
        if not B or mask is None:return ()
        for k,category in enumerate(mask):
            if category in (1,2):B=self.meet(B,k,category-1)
            if not B:break
        return B
    def step(self,B,op,k,zero,mask):
        if not B:return ()
        if op=='CD':
            if zero:
                if not mask[k]&1:return ()
                B=self.meet(B,k,0)
            elif not mask[k]&6:return ()
        if op=='CI' or (op=='CD' and not zero):
            d=1 if op=='CI' else -1
            rows=[]
            for row in B:
                r=list(row);r[k+1]=(r[k+1]+d*r[0])%self.p;rows.append(r)
            B=self.normalize_affine(rows)
        return B
    def join(self,A,B):return self.normalize_affine(A+B)
    def included(self,A,B):return self.join(A,B)==B

