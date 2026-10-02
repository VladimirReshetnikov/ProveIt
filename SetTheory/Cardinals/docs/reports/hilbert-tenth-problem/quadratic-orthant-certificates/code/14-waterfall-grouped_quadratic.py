"""Standalone canonical quadratic compiler for a fixed 46-clock Waterfall frontend.

All domains are natural integers. External k is the number of completed TM
instructions, not a witness, so this is not a fixed-arity universal equation.
The underlying creator machine is prior art; see companion article.
"""
from pathlib import Path
import json,random
ROOT=Path(__file__).resolve().parent
TABLE='0RB1RA_1RC1RA_0LG0LE_0LF1LE_1RA1LD_1LD1LD_0LH1LG_1LI1LG_0RA1LJ_1LK---_0RL1RN_0RM1RL_0LB1RL_0LC0RO_0RN1RN'.split("_")
RULES=[]
for q,row in enumerate(TABLE):
    for s in range(2):
        t=row[3*s:3*s+3]
        if t!='---':RULES.append((q,s,ord(t[2])-65,int(t[1]=='R'),int(t[0])))
assert len(RULES)==29

class P:
    def __init__(self,terms=None):self.t={m:c for m,c in (terms or {}).items() if c}
    @staticmethod
    def cast(x):return x if isinstance(x,P) else P({():x})
    @staticmethod
    def var(x):return P({(x,):1})
    def __add__(self,b):
        b=self.cast(b);d=dict(self.t)
        for m,c in b.t.items():d[m]=d.get(m,0)+c
        return P(d)
    __radd__=__add__
    def __neg__(self):return P({m:-c for m,c in self.t.items()})
    def __sub__(self,b):return self+-self.cast(b)
    def __rsub__(self,b):return self.cast(b)+-self
    def __mul__(self,b):
        b=self.cast(b);d={}
        for m,c in self.t.items():
            for n,e in b.t.items():
                z=tuple(sorted(m+n));d[z]=d.get(z,0)+c*e
        return P(d)
    __rmul__=__mul__
    @property
    def degree(self):return max(map(len,self.t),default=0)
    def at(self,env):
        total=0
        for mon,c in self.t.items():
            for v in mon:c*=env[v]
            total+=c
        return total
    def dump(self):return [{'coefficient':c,'monomial':list(m)} for m,c in sorted(self.t.items())]

def tm_history(L,R,k):
    q=s=0;history=[]
    for j in range(k):
        key=(q,s);rule=next((t for t in RULES if t[:2]==key),None)
        if rule is None:return history,True,(q,s,L,R)
        _,_,qn,D,w=rule;X,Y=(R,L) if D else (L,R);Q,r=divmod(X,2)
        Ln,Rn=(2*Y+w,Q) if D else (Q,2*Y+w)
        history.append(dict(q=q,s=s,L=L,R=R,Q=Q,Y=Y,r=r,rule=RULES.index(rule),
                            Ln=Ln,Rn=Rn,C=6+3*Q+r+3*Y))
        q,s,L,R=qn,r,Ln,Rn
    return history,(q,s)==(9,1),(q,s,L,R)

class Base:
    def __init__(self,k):
        assert type(k) is int and k>=1
        self.k=k;self.parameters=['L0','R0','C','tau'];self.witnesses=[];self.squares=[];self.products=[]
    def v(self,n):self.witnesses.append(n);return P.var(n)
    def eq(self,n,p):assert p.degree<=1;self.squares.append((n,p))
    def energy(self,env):return sum(p.at(env)**2 for _,p in self.squares)+sum(a.at(env)*b.at(env) for _,a,b in self.products)
    def polynomial(self):return sum((p*p for _,p in self.squares),P())+sum((a*b for _,a,b in self.products),P())
    def finish(self,B,r,count):
        self.eq('halt_state',B-9);self.eq('halt_head',r-1)
        self.eq('count',count-P.var('C'));self.eq('time',P.var('tau')-1-2*P.var('C')-7*self.k)
    def dump(self):
        return dict(external_TM_steps=self.k,parameters=self.parameters,witnesses=self.witnesses,
                    domain='natural integers; exact fixed-k first halt; no unbounded fixed-arity claim',
                    degree=self.degree,squared_linear_residuals=[dict(name=n,polynomial=p.dump()) for n,p in self.squares],
                    nonnegative_products=[dict(name=n,left=a.dump(),right=b.dump()) for n,a,b in self.products],
                    witness_count=len(self.witnesses),squared_linear_count=len(self.squares),product_count=len(self.products))

class DirectionalQuadratic(Base):
    """Direction-group complementarity certificate with 35k witnesses."""
    degree=2
    def __init__(self,k):
        super().__init__(k);L,R=P.var('L0'),P.var('R0');B=rprev=P.cast(0);count=P.cast(6*k)
        for j in range(k):
            es=[self.v(f'e{j}_{i}') for i in range(29)]
            QL,rL,YL,QR,rR,YR=[self.v(f'{n}{j}') for n in ['QL','rL','YL','QR','rR','YR']]
            A,S,Bn,ER,W=[sum((rule[t]*e for rule,e in zip(RULES,es)),P()) for t in range(5)]
            EL=sum((e for rule,e in zip(RULES,es) if not rule[3]),P())
            WL=sum((rule[4]*e for rule,e in zip(RULES,es) if not rule[3]),P())
            WR=sum((rule[4]*e for rule,e in zip(RULES,es) if rule[3]),P())
            IL,IR=2*QL+rL+YR,YL+2*QR+rR
            OL,OR=QL+2*YR+WR,2*YL+WL+QR
            self.eq(f'onehot{j}',sum(es,P())-1)
            self.eq(f'state{j}',A-B);self.eq(f'head{j}',S-rprev)
            self.eq(f'inputL{j}',IL-L);self.eq(f'inputR{j}',IR-R)
            self.products.append((f'inactiveL{j}',ER,QL+rL+YL))
            self.products.append((f'inactiveR{j}',EL,QR+rR+YR))
            for name,a,b in self.products[-2:]:
                assert all(c>=0 for c in a.t.values()) and all(c>=0 for c in b.t.values())
            L,R,B,rprev=OL,OR,Bn,rL+rR
            count+=3*(QL+QR+YL+YR)+rL+rR
        self.finish(B,rprev,count)
        assert len(self.witnesses)==35*k and len(self.squares)==5*k+4 and len(self.products)==2*k
    def lift(self,L,R):
        history,halt,end=tm_history(L,R,self.k);assert len(history)==self.k
        C=sum(t['C'] for t in history);env=dict(L0=L,R0=R,C=C,tau=1+2*C+7*self.k)
        for j,t in enumerate(history):
            env.update({f'e{j}_{i}':int(i==t['rule']) for i in range(29)})
            D=RULES[t['rule']][3]
            for side in ['L','R']:
                active=(side=='R')==bool(D)
                for n in ['Q','r','Y']:env[f'{n}{side}{j}']=t[n] if active else 0
        return env,halt,end

def main():
    checks=0;mutations=0;sizes=[]
    for k in [1,2,7,8]:
        cert=DirectionalQuadratic(k)
        sizes.append(dict(k=k,witnesses=len(cert.witnesses),linear_squares=len(cert.squares),products=len(cert.products),degree=2))
        for L,R in [(0,0),(6,0),(6,4),(14,0),(3,5),(1,7)]:
            hist,halt,end=tm_history(L,R,k)
            if len(hist)<k:continue
            env,halt,end=cert.lift(L,R)
            assert (cert.energy(env)==0)==halt;checks+=1
            if halt:
                for v in cert.witnesses+['C','tau']:
                    bad=dict(env);bad[v]+=1;assert cert.energy(bad)>0;mutations+=1
    cert=DirectionalQuadratic(1);poly=cert.polynomial();assert poly.degree==2
    rng=random.Random(8841)
    for _ in range(1000):
        env={v:rng.randrange(3) for v in cert.parameters+cert.witnesses}
        assert poly.at(env)==cert.energy(env)>=0
    cert=DirectionalQuadratic(7);env,halt,end=cert.lift(6,0)
    assert halt and env['C']==189 and env['tau']==428 and cert.energy(env)==0
    (ROOT/'grouped-quadratic7-certificate.json').write_text(json.dumps(cert.dump(),indent=2)+'\n')
    (ROOT/'grouped-quadratic7-fixture.json').write_text(json.dumps(env,indent=2)+'\n')
    receipt=dict(status='PASS',sizes=sizes,simulation_cases=checks,witness_output_mutations=mutations,arbitrary_assignment_checks=1000,
                 first_halt_fixture=dict(L=6,R=0,k=7,C=189,tau=428),one_step_expanded_monomials=len(poly.t),
                 scope='External TM horizon k; canonical natural witnesses; quadratic not claimed convex; no unbounded fixed-arity equation.')
    (ROOT/'grouped-quadratic-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
