"""LEGACY FACTORIZED: independent literal polynomial compiler.
All residuals are expanded sparse polynomials with exact integer coefficients.
Uses no producer modules. Tests the advertised counted gates, not an oracle wrapper.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import comb
import json, random
from independent_dynamics import conservative_permutation, dense_step, to_records

class E:
    def __init__(self, d): self.d={m:c for m,c in d.items() if c}
    @staticmethod
    def c(x): return x if isinstance(x,E) else E({():x})
    def __add__(self,o):
        o=E.c(o); d=defaultdict(int,self.d)
        for m,c in o.d.items(): d[m]+=c
        return E(d)
    __radd__=__add__
    def __neg__(self): return E({m:-c for m,c in self.d.items()})
    def __sub__(self,o): return self+-E.c(o)
    def __rsub__(self,o): return E.c(o)+-self
    def __mul__(self,o):
        o=E.c(o); d=defaultdict(int)
        for m,c in self.d.items():
            for n,b in o.d.items(): d[tuple(sorted(m+n))]+=c*b
        return E(d)
    __rmul__=__mul__
    def value(self,values):
        ans=0
        for mon,coeff in self.d.items():
            val=coeff
            for k in mon:val*=values[k]
            ans+=val
        return ans
    def degree(self): return max(map(len,self.d),default=0)

class Compiler:
    def __init__(self,K,g,records,T):
        self.K,self.q,self.g,self.M,self.T=K,K+1,g,len(records),T
        self.values=[];self.residuals=[];self.names=[];self.onehots=[]
        self.rows=[[(E.c(x+T),E.c(c)) for x,c in records]]
        for t in range(T):self.layer(self.rows[-1])
    def value(self,e):return E.c(e).value(self.values)
    def var(self,value,name):
        j=len(self.values);self.values.append(value);self.names.append(name)
        return E({(j,):1})
    def residual(self,e):
        e=E.c(e)
        assert e.degree()<=2
        assert e.value(self.values)==0,(len(self.residuals),e.d,e.value(self.values))
        self.residuals.append(e)
    def cmp(self,x,y):
        xv,yv=self.value(x),self.value(y)
        b=self.var(int(yv>=xv),'compare_bit')
        d=self.var(yv-xv if yv>=xv else xv-yv-1,'compare_gap')
        self.residual(b*(b-1));self.residual(y-x-(2*b-1)*d-b+1)
        return b
    def eq(self,x,y):return self.cmp(x,y)-self.cmp(x+1,y)
    def hot(self,number,size):
        s=[self.var(int(a==self.value(number)),'lookup_selector') for a in range(size)]
        self.onehots.append(s)
        self.residual(sum(s)-1);self.residual(number-sum(a*x for a,x in enumerate(s)))
        return s
    def layer(self,old):
        M=self.M;q=self.q
        channels=[]
        for x,z in old:
            h=[self.var(int(c==self.value(z)),'channel_selector') for c in range(3)]
            self.onehots.append(h)
            self.residual(sum(h)-1);self.residual(z-h[1]-2*h[2]);channels.append(h)
        ys=[]
        for (x,z),(L,C,R) in zip(old,channels):
            y=self.var(self.value(x-L+R),'stream_position');self.residual(y+L-x-R);ys.append(y)
        eqs=[[E.c(int(i==j)) for j in range(M)] for i in range(M)]
        for i in range(M):
            for j in range(i+1,M):eqs[i][j]=eqs[j][i]=self.eq(ys[i],ys[j])
        outs=[]
        for i in range(M):
            inputs=[]
            for c in (2,1,0):
                formula=sum(eqs[i][j]*channels[j][c] for j in range(M))
                n=self.var(self.value(formula),'input_mass');self.residual(n-formula);inputs.append(n)
            U,V,W=[self.hot(n,q) for n in inputs]
            A={}
            for a,b in product(range(q),repeat=2):
                A[a,b]=self.var(self.value(U[a]*V[b]),'pair_product')
                self.residual(A[a,b]-U[a]*V[b])
            B={}
            for a,b,c in product(range(q),repeat=3):
                B[a,b,c]=self.var(self.value(A[a,b]*W[c]),'triple_product')
                self.residual(B[a,b,c]-A[a,b]*W[c])
            out=[]
            for c in range(3):
                f=sum(self.g[abc][c]*sel for abc,sel in B.items())
                a=self.var(self.value(f),'output_mass');self.residual(a-f);out.append(a)
            outs.append(out)
        records=[]
        for i in range(M):
            rank=sum(eqs[i][:i+1]);a,b,c=outs[i]
            h=self.cmp(rank,a);k=self.cmp(rank,a+b)
            records.append((ys[i],2-h-k))
        sort_count=0
        for end in range(M-1,0,-1):
            for j in range(end):
                x,z=records[j];y,w=records[j+1]
                bit=self.cmp(3*x+z,3*y+w)
                xm=self.var(self.value(y+bit*(x-y)),'sort_position')
                zm=self.var(self.value(w+bit*(z-w)),'sort_channel')
                xM=self.var(self.value(x+y-xm),'sort_position')
                zM=self.var(self.value(z+w-zm),'sort_channel')
                self.residual(xm-y-bit*(x-y));self.residual(zm-w-bit*(z-w))
                self.residual(xM-x-y+xm);self.residual(zM-z-w+zm)
                records[j],records[j+1]=(xm,zm),(xM,zM);sort_count+=1
        assert sort_count==comb(M,2)
        self.rows.append(records)
    def verify(self,records):
        M,T,q=self.M,self.T,self.q
        wantv=T*(M*(q**3+q*q+3*q+14)+5*M*(M-1))
        wantr=T*(M*(q**3+q*q+19)+5*M*(M-1))
        assert len(self.values)==wantv,(len(self.values),wantv)
        assert len(self.residuals)==wantr,(len(self.residuals),wantr)
        D=max((x for x,c in records),default=0)
        H=3*(D+2*T)+M+3*self.K+3
        assert all(type(v)==int and 0<=v<=H for v in self.values)
        # Independently compare complete physical trajectories.
        dense=defaultdict(lambda:[0,0,0])
        for x,c in records:dense[x][c]+=1
        dense={x:tuple(a) for x,a in dense.items()}
        table_lcr={abc:self.g[abc[::-1]] for abc in self.g}
        for t,row in enumerate(self.rows):
            actual=[(self.value(x)-T,self.value(z)) for x,z in row]
            assert actual==to_records(dense),(t,actual,to_records(dense))
            if t<T:dense=dense_step(dense,table_lcr)
        return {'variables':wantv,'residuals':wantr,'max_residual_degree':max((r.degree() for r in self.residuals),default=0),'max_witness':max(self.values,default=0),'bound':H}


def elementary_tests():
    comparisons=0
    for x,y in product(range(8),repeat=2):
        solutions=[]
        for b,d in product(range(4),range(10)):
            if b*(b-1)==0 and y-x-(2*b-1)*d-b+1==0:solutions.append((b,d))
        assert solutions==[(int(y>=x),y-x if y>=x else x-y-1)]
        comparisons+=1
    onehots=0
    for q in range(2,6):
        for n in range(q):
            sols=[s for s in product(range(2),repeat=q) if sum(s)==1 and sum(i*v for i,v in enumerate(s))==n]
            assert sols==[tuple(int(i==n) for i in range(q))];onehots+=1
    return {'cmp_input_pairs':comparisons,'lookup_onehot_values':onehots}


def real_counterexample():
    K=2;g={abc:abc for abc in product(range(3),repeat=3)}
    obj=Compiler(K,g,[(0,2)],1)
    canonical=list(obj.values)
    # First hot vector is the channel vector, second is incoming U.
    U=obj.onehots[1]
    ids=[next(iter(u.d))[0] for u in U]
    for j,val in zip(ids,[Fraction(1,2),0,Fraction(1,2)]):obj.values[j]=val
    # Recompute product outputs from defining quadratic residuals, which place
    # each fresh result as the sole linear term of coefficient +1.
    for r in obj.residuals:
        linear=[m[0] for m,c in r.d.items() if len(m)==1 and c==1]
        for j in linear:
            if obj.names[j] in ('pair_product','triple_product'):
                other=E({m:c for m,c in r.d.items() if m!=(j,)})
                obj.values[j]=-other.value(obj.values)
    assert all(r.value(obj.values)==0 for r in obj.residuals)
    assert canonical!=obj.values
    assert all(x>=0 for x in obj.values)
    simplex_squares=sum(u*u for u in U)-1
    assert simplex_squares.value(obj.values)==Fraction(-1,2)
    return {'K':K,'M':1,'T':1,'g':'identity on incoming (R,C,L) and outgoing (L,C,R) coordinates','initial_record':[0,2], 'alternative_U':['1/2','0','1/2'],'all_existing_residuals_zero':True,'optional_square_simplex_residual':'-1/2'}


def strengthen_and_verify(obj):
    core_count=len(obj.residuals)
    assert len(obj.onehots)==4*obj.M*obj.T
    for selectors in obj.onehots:
        obj.residual(sum(s*s for s in selectors)-1)
    assert len(obj.residuals)==core_count+4*obj.M*obj.T
    assert all(r.degree()<=2 for r in obj.residuals)
    assert all(r.value(obj.values)==0 for r in obj.residuals)
    return len(obj.residuals)


def main():
    rows=[];upgraded_total=0
    for K in (1,2,3):
        for seed in range(4):
            rng=random.Random(1000*K+seed)
            g=conservative_permutation(K,rng)
            vals=[rng.randrange(K+1) for _ in range(9)]
            # Bound the audit case mass while including repeated entries.
            while sum(vals)>7: vals[rng.choice([i for i,v in enumerate(vals) if v])]-=1
            records=sorted((2*x,c) for x in range(3) for c in range(3) for _ in range(vals[3*x+c]))
            if not records:records=[(0,1)]
            shift=min(x for x,c in records);records=[(x-shift,c) for x,c in records]
            for T in (0,1,2):
                obj=Compiler(K,g,records,T);rows.append(obj.verify(records));upgraded_total+=strengthen_and_verify(obj)
    result={'backend':'factorized','elementary':elementary_tests(),'full_literal_compilers_checked':len(rows),'total_variables':sum(r['variables'] for r in rows),'total_residuals':sum(r['residuals'] for r in rows),'max_tested_residual_degree':max(r['max_residual_degree'] for r in rows),'exact_count_degree_bound_and_semantics_pass':True,'optional_strengthened_total_residuals':upgraded_total,'optional_plus_4MT_counts_verified':True,'nonnegative_real_counterexample':real_counterexample()}
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
