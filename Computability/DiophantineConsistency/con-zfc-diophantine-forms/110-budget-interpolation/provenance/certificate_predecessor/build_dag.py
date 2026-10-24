#!/usr/bin/env python3
"""Build ordinary-polynomial expression DAGs for the four-corner fixture.
Only fixed nonnegative integer powers occur in this DAG. Variable powers
are exposed separately as graph interfaces and are never DAG operations.
"""
import json
from pathlib import Path
from core import CORNERS,constants,data,pack_masks,board_masks
class Ring:
    def __init__(self): self.nodes=[];self.ids={};self.degrees=[]
    def put(self,node,degree):
        key=json.dumps(node,sort_keys=True,separators=(',',':'))
        if key in self.ids:return self.ids[key]
        i=len(self.nodes);self.ids[key]=i;self.nodes.append(node);self.degrees.append(degree);return i
    def c(self,n):return self.put({'op':'const','value':n},0)
    def v(self,n):return self.put({'op':'var','name':n},1)
    def add(self,*xs):return self.put({'op':'add','args':list(xs)},max([self.degrees[x] for x in xs] or [0]))
    def mul(self,*xs):return self.put({'op':'mul','args':list(xs)},sum(self.degrees[x] for x in xs))
    def neg(self,x):return self.mul(self.c(-1),x)
    def sub(self,x,y):return self.add(x,self.neg(y))
    def pow(self,x,n):
        if type(n) is not int or n<0:raise ValueError('Only literal polynomial exponents allowed')
        return self.put({'op':'pow_fixed','base':x,'exponent':n},n*self.degrees[x])
    def evaluate(self,env):
        vals=[]
        for a in self.nodes:
            op=a['op']
            if op=='const':v=a['value']
            elif op=='var':v=env[a['name']]
            elif op=='add':v=sum(vals[i] for i in a['args'])
            elif op=='mul':
                v=1
                for i in a['args']:v*=vals[i]
            elif op=='pow_fixed':v=vals[a['base']]**a['exponent']
            else:raise ValueError(op)
            vals.append(v)
        return vals

def make(tiles):
    ring=Ring();c=ring.c;add=ring.add;mul=ring.mul;sub=ring.sub;pw=ring.pow
    k=len(tiles);C,A0,D=constants(tiles)
    Q,G,Z=[ring.v(x) for x in ['Q','G','Z']]
    P=add(c(1),mul(c(C-1),G));H=mul(c(A0),P);R=mul(c(D),pw(P,3));B=mul(c(D//2),pw(P,3));L=pw(R,2*k)
    aa=[[] for _ in range(7)]
    for t in tiles:
        vals=[c(1),mul(sub(Q,c(1)),c(int(t.west==0))),
              sub(c(C*int(t.east==0)),mul(Q,c(int(t.west==0)))),
              c(C*t.east-t.west),sub(mul(Q,c(t.south)),c(t.north)),
              c((C-1)*int(t.north==0)),sub(mul(Q,c(int(t.south==0))),mul(P,c(int(t.north==0))))]
        for row,v in zip(aa,vals):row.append(v)
    cc=[ring.neg(G),sub(c(1),P),c(0),c(0),c(0),sub(c(1),Q),c(0)]
    K=[add(*(mul(add(H,a),pw(R,k-1-t)) for t,a in enumerate(row))) for row in aa]
    F=[add(mul(K[j],Z),mul(add(B,ring.neg(mul(H,G)),cc[j]),pw(R,k-1))) for j in range(7)]
    M0=mul(G,add(*(pw(R,t) for t in range(k))))
    M1=sub(sub(pw(R,2*k-1),c(1)),mul(sub(sub(R,c(1)),B),pw(R,k-1)))
    A=add(M0,mul(M1,add(*(pw(L,j) for j in range(1,8)))))
    Y=add(Z,*(mul(F[j-1],pw(L,j)) for j in range(1,8)))
    out={'P':P,'H':H,'R':R,'B':B,'L':L,'M0':M0,'M1':M1,'A':A,'Y':Y}
    out.update({f'F{j+1}':v for j,v in enumerate(F)})
    return ring,out,{'k':k,'C':C,'A0':A0,'D':D}

def main():
    ring,out,con=make(CORNERS)
    for w,h in [(1,1),(1,2),(2,1),(2,2),(3,2)]:
        board=[i%4 for i in range(w*h)]
        Z=pack_masks(CORNERS,w,h,board_masks(CORNERS,w,h,board)); direct=data(CORNERS,w,h,Z)
        vals=ring.evaluate({name:direct[name] for name in ['Q','G','Z']})
        for name,i in out.items():
            expected=direct['F'][int(name[1:])-1] if name.startswith('F') else direct[name]
            if vals[i]!=expected:raise RuntimeError('DAG mismatch: '+name)
    result={'format':'integer-polynomial-dag-v1','tile_edges_order':'west,east,north,south',
            'tiles':[t.__dict__ for t in CORNERS],'constants':con,'inputs':['Q','G','Z'],
            'nodes':ring.nodes,'outputs':out,'degree_upper_bounds':{n:ring.degrees[i] for n,i in out.items()},
            'exposed_naturals':['a','b','Q','G','Z','r'],
            'uncompiled_graphs':['Q=C^(a+1)','1+(C-1)G=Q^(b+1)','binom(A,Y)=2r+1'],
            'node_count':len(ring.nodes),'verification':'Matched independent integer evaluator at five geometries.'}
    Path(__file__).with_name('FOUR_TILE_DAG.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ['node_count','degree_upper_bounds','verification']},indent=2))
if __name__=='__main__':main()
