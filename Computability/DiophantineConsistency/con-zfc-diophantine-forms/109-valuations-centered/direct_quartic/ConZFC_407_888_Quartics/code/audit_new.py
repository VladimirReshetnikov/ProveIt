#!/usr/bin/env python3
"""Independent arithmetic audit of saved rows; imports no construction code."""
from pathlib import Path
import argparse,json,math

def require(ok,msg):
    if not ok:raise ValueError(msg)

def add(p,q):
    out=dict(p)
    for m,c in q.items():out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}

def scale(p,c):return {m:c*x for m,x in p.items() if c*x}
def mul(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():
            key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}

def atom(a):return tuple(a)
def var(i):return {(i,):1}
def constant(n):return {():n} if n else {}

class Audit:
    def __init__(self,data):
        self.d=data;self.rows=data['rows']
        self.bylabel={r['label']:r for r in self.rows}
        self.gates={r['gate']:r for r in self.rows if r.get('gate') is not None}
        self.A=atom(data['scale'][1]);self.D=atom(data['discriminant'])
    def expand(self,a,leaves,disc=False,memo=None):
        a=atom(a)
        if a[0]=='c':return constant(a[1])
        i=a[1]
        if i in leaves:return leaves[i]
        if disc and a==self.D:
            ap=self.expand(self.A,leaves,False)
            return add(mul(ap,ap),constant(-1))
        if memo is None:memo={}
        if i in memo:return memo[i]
        if i not in self.gates:return var(i)
        row=self.gates[i]
        pivots=[(c,m) for c,m in row['terms'] if i in m]
        require(pivots==[(1,[i])],'nonmonic or recursive gate')
        result={}
        for c,m in row['terms']:
            if m==[i]:continue
            term=constant(-c)
            for j in m:term=mul(term,self.expand(('v',j),leaves,disc,memo))
            result=add(result,term)
        memo[i]=result;return result
    def row_poly(self,label,leaves,disc=False):
        result={}
        for c,m in self.bylabel[label]['terms']:
            term=constant(c)
            for i in m:term=mul(term,self.expand(('v',i),leaves,disc))
            result=add(result,term)
        return result
    def positive(self,a,memo=None):
        a=atom(a)
        if a[0]=='c':return a[1]>0
        i=a[1]
        if memo is None:memo={}
        if i in memo:return memo[i]
        if i not in self.gates:return False
        row=self.gates[i]
        # Only nonnegative constructor gates are eligible for this proof.
        if row['label'] not in ('addition','multiplication'):return False
        rhs=[(-c,m) for c,m in row['terms'] if m!=[i]]
        require(all(c>=0 for c,m in rhs),'signed positivity gate')
        value=any(c>0 and all(self.positive(('v',j),memo) for j in m) for c,m in rhs)
        memo[i]=value;return value
    def run(self):
        A=var(-1);D=var(-2)
        require(self.row_poly('index_addition.D_definition',{self.A[1]:A,self.D[1]:D})==add(add(mul(A,A),scale(D,-1)),constant(-1)),'discriminant identity')
        seeds={atom(r['exponent']):tuple(map(atom,r['pair'])) for r in self.d['seeds']}
        indices={atom(r['exponent']):tuple(map(atom,r['pair'])) for r in self.d['indices']}
        derivations={atom(r['target']):r for r in self.d['derivations']}
        requested={atom(r['exponent']) for r in self.d['powers']}
        require(not(set(seeds)&set(derivations)),'seed/derivation overlap')
        require(set(seeds)|set(derivations)==requested==set(indices),'exponent partition')
        for k,r in derivations.items():
            require(r['kind']=='shift','audit expects the three actual shift calls')
            src=atom(r['source']);shift=r['shift'];require(shift in(1,2),'shift range')
            require(src in requested and src[1]<k[1],'nonacyclic index dependency')
            K=var(-3)
            require(self.expand(k,{src[1]:K})==add(K,constant(shift)),'source exponent shift identity')
            X,Y=indices[src];Xp,Yp=tuple(map(atom,r['pair']))
            require(indices[k]==(Xp,Yp),'derived pair output mismatch')
            x,y=var(-4),var(-5)
            leaves={self.A[1]:A,X[1]:x,Y[1]:y}
            dd=add(mul(A,A),constant(-1))
            u,v=(A,constant(1)) if shift==1 else (add(scale(dd,2),constant(1)),scale(A,2))
            ex=add(mul(x,u),mul(dd,mul(y,v)))
            ey=add(mul(x,v),mul(y,u))
            require(self.expand(Xp,leaves,True)==ex,'X index addition law')
            require(self.expand(Yp,leaves,True)==ey,'Y index addition law')
        # The concrete requested exponents are all positive from literals and
        # nonnegative arithmetic alone; no assumed power output is used.
        require(all(self.positive(r['exponent']) for r in self.d['powers']),'nonpositive exponent atom')
        rd=self.d['radix'];B=atom(rd['radix_multiple']);V=atom(rd['factorial_radix']['numerator']);q=atom(rd['radix'])
        bp,vp=var(-6),var(-7)
        require(self.expand(q,{B[1]:bp,V[1]:vp})==mul(bp,add(vp,constant(1))),'recycled radix identity')
        g=atom(rd['aggregate_slack']);ranges=self.d['ranges'];r=len(ranges)
        require(r==rd['aggregate_range_count']==rd['range_binomials'],'range count')
        leaves={B[1]:bp,g[1]:var(-8)};expected=add(scale(bp,r),scale(var(-8),-1))
        for i,(n,k,bb,label) in enumerate(ranges):
            n=atom(n);require(atom(bb)==B,'range modulus differs')
            require(self.positive(n) and self.positive(k),'range inputs not positive')
            leaves[n[1]]=var(-20-i);expected=add(expected,scale(var(-20-i),-1))
        require(self.row_poly('crt.aggregate_representative_bound',leaves)==expected,'aggregate bound identity')
        # Bind V to the actual already-requested factorial numerator.
        H=atom(rd['factorial_radix']['H']);rho=atom(rd['factorial_radix']['rho'])
        powers={atom(p['output']):p for p in self.d['powers']}
        require(rho in powers and V in powers,'factorial radix outputs absent')
        rp,vpower=powers[rho],powers[V]
        hp=var(-40);rhop=var(-41)
        for a in (rp['base'],rp['exponent']):
            require(self.expand(a,{H[1]:hp})==add(hp,constant(2)),'rho graph binding')
        require(atom(vpower['exponent'])==H,'V exponent binding')
        require(self.expand(vpower['base'],{rho[1]:rhop})==add(rhop,constant(1)),'V base binding')
        facts=self.d['factorials'];require(len(facts)==2 and atom(facts[0]['input'])==H,'factorial source order')
        require(atom(facts[0]['output'])==atom(rd['factorial_radix']['factorial']),'T binding')
        require(len(self.d['binomials'])==rd['exact_binomials']==3,'exact binomial count')
        # Verify the auxiliary product contains only seed Y coordinates.
        U,Vaux,Baux=map(atom,self.d['auxiliary'])
        vm=[i for i,v in enumerate(self.d['variables']) if v['name']=='shared_index.Vquotient_minus1']
        require(len(vm)==1,'auxiliary quotient index')
        leaves={Vaux[1]:var(-50),vm[0]:var(-51)}
        product=constant(1)
        for i,(x,y) in enumerate(seeds.values()):
            leaves[y[1]]=var(-60-i);product=mul(product,mul(var(-60-i),var(-60-i)))
        expected=add(var(-50),scale(mul(product,add(var(-51),constant(1))),-1))
        require(self.row_poly('shared_index.V_positive_product',leaves)==expected,'auxiliary seed-only product')
        return {'distinct_exponents':len(requested),'power_graphs':len(self.d['powers']),
                'seed_indices':len(seeds),'derived_indices':len(derivations),
                'range_columns':r,'exact_binomials':3,
                'all_positive_exponent_atoms':True,
                'exact_new_row_identities':True,'acyclic_index_dependencies':True}

def fixtures():
    pell=0
    def pair(A,n):
        x,y=1,0
        for _ in range(n):x,y=A*x+(A*A-1)*y,x+A*y
        return x,y
    for A in range(2,12):
        for u in range(13):
            for v in range(13):
                x,y=pair(A,u);a,b=pair(A,v)
                require(pair(A,u+v)==(x*a+(A*A-1)*y*b,x*b+y*a),'Pell fixture')
                pell+=1
    digits=0
    for n in range(16):
        for k in range(1,19):
            bound=max(math.comb(n,j) if j<=n else 0 for j in range(k+1))
            for B in range(1,8):
                q=B*(bound+1);den=q**k;num=(q+1)**n;quot,rem=divmod(num,den)
                ck=math.comb(n,k) if k<=n else 0
                require(quot%q==ck,'low-digit fixture')
                require((quot%B==0)==(ck%B==0),'fused-divisibility fixture')
                digits+=1
    return {'pell_addition_cases':pell,'low_digit_and_fused_cases':digits}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--output',type=Path)
    a=p.parse_args();d=json.loads(a.input.read_text());result=Audit(d).run();result.update(fixtures())
    bad=json.loads(json.dumps(d));bad['radix']['radix']=['c',1]
    try:Audit(bad).run()
    except ValueError:result['deliberately_corrupted_radix_rejected']=True
    else:raise ValueError('corrupted radix accepted')
    result['status']='PASS';result['scope']='exact new gate identities, dependency partition, positive exponent atoms; unbounded arithmetic proof is in PROOF.md'
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(text)
    print(text)
