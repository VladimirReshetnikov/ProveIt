#!/usr/bin/env python3
"""Independent exact review of the two 17-integer norms and 18-integer companion.

No builder or author verifier is imported. Standard library only. The literal
comparison uses a separately transcribed formula and associative-commutative
normalization; universal norm identities use a separate sparse polynomial
engine; total degree uses highest homogeneous components.
"""
import ast
import gzip
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent


def require(ok,why):
    if not ok:raise ValueError(why)


def parse(s):return ast.parse(s,mode='eval').body


def scalar(n):return ('n',n)


def product(*xs):
    c=1;rest=[]
    for x in xs:
        ys=x[2] if x[0]=='m' else (x,)
        if x[0]=='m':c*=x[1]
        for y in ys:
            if y[0]=='n':c*=y[1]
            else:rest.append(y)
    if not c:return scalar(0)
    if not rest:return scalar(c)
    rest=tuple(sorted(rest,key=repr))
    if c==1 and len(rest)==1:return rest[0]
    return ('m',c,rest)


def summation(*xs):
    const=0;terms={}
    for x in xs:
        ys=x[1] if x[0]=='a' else ((1,x),)
        for coeff,y in ys:
            if y[0]=='n':const+=coeff*y[1];continue
            if y[0]=='m':coeff*=y[1];y=product(*(y[2]))
            terms[y]=terms.get(y,0)+coeff
    out=[(c,y) for y,c in terms.items() if c]
    if const:out.append((1,scalar(const)))
    if not out:return scalar(0)
    if len(out)==1:return product(scalar(out[0][0]),out[0][1])
    return ('a',tuple(sorted(out,key=repr)))


def normal(t,env):
    if isinstance(t,ast.Constant):
        require(type(t.value)==int,'noninteger literal');return scalar(t.value)
    if isinstance(t,ast.Name):return env.get(t.id,('v',t.id))
    if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return product(scalar(-1),normal(t.operand,env))
    require(isinstance(t,ast.BinOp),'unsupported node')
    a=normal(t.left,env)
    if isinstance(t.op,ast.Pow):
        require(isinstance(t.right,ast.Constant) and type(t.right.value)==int and 0<=t.right.value<=8,'bad exponent')
        return product(*([a]*t.right.value))
    b=normal(t.right,env)
    if isinstance(t.op,ast.Add):return summation(a,b)
    if isinstance(t.op,ast.Sub):return summation(a,product(scalar(-1),b))
    if isinstance(t.op,ast.Mult):return product(a,b)
    raise ValueError('bad operation')


# Independently transcribed mathematical definitions, without reading the
# generator's definition dictionary to construct the expected expressions.
MANUAL=[
('J','3*J3+1'),('q','beta*J+1'),('W','4*(3*w3+1)'),('X','q*W'),
('Y','(2*v_scale+1)*q**3'),('E','X*Y'),('a','(X+1)*Y'),
('H','4*a+3'),('Delta','a**2+4*a+3'),('V','f*o-c'),
('k','1-V+j*c+h*E'),('eta','c-Y*k'),('u','E*Y*k'),
('A','u*(u+k)+1'),('F','(K0+W)*C-z*(q-1)'),
('I','(2*r+1)*c**2'),('Q','I**2'),('delta','Q-1'),
('R','(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*J'),
('det','(cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)**2'),
('Tpair','eta*(k-eta)'),
('guard','det*Tpair-(pair_root**2-det-Tpair+1)**2-(1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1))'),
('Bnum','Q*V**2-1'),
('norm','(delta*(root_sum**2+2*I*(2*u+k)*root_sum+Q*(k**2-4))-4*Bnum)**2-64*delta*Q*A*Bnum')]
ROWS=['(X+a*c+gamma*H)**2-Delta*c**2-1','c*j-V-R','Q-Delta*(f**2-1)','guard','norm']


class Ring:
    def __init__(self,names):self.names=tuple(names);self.pos={n:i for i,n in enumerate(names)};self.zero=(0,)*len(names)
    def const(self,n):return {self.zero:n} if n else {}
    def var(self,n):
        a=list(self.zero);a[self.pos[n]]=1;return {tuple(a):1}
    def add(self,a,b,scale=1):
        z=dict(a)
        for m,c in b.items():
            v=z.get(m,0)+scale*c
            if v:z[m]=v
            elif m in z:del z[m]
        return z
    def mul(self,a,b):
        z={}
        for m,c in a.items():
            for n,d in b.items():
                k=tuple(x+y for x,y in zip(m,n));z[k]=z.get(k,0)+c*d
        return {k:v for k,v in z.items() if v}
    def power(self,a,e):
        z=self.const(1)
        for _ in range(e):z=self.mul(z,a)
        return z
    def eval(self,t,env=None):
        env=env or {}
        if isinstance(t,ast.Constant):return self.const(t.value)
        if isinstance(t,ast.Name):return env[t.id] if t.id in env else self.var(t.id)
        if isinstance(t,ast.UnaryOp):return self.mul(self.const(-1),self.eval(t.operand,env))
        a=self.eval(t.left,env)
        if isinstance(t.op,ast.Pow):return self.power(a,t.right.value)
        b=self.eval(t.right,env)
        if isinstance(t.op,ast.Add):return self.add(a,b)
        if isinstance(t.op,ast.Sub):return self.add(a,b,-1)
        if isinstance(t.op,ast.Mult):return self.mul(a,b)
        raise ValueError('bad operation')


def top(t,ring,weights,env):
    if isinstance(t,ast.Constant):return 0,ring.const(t.value)
    if isinstance(t,ast.Name):return env[t.id] if t.id in env else (weights.get(t.id,0),ring.var(t.id))
    if isinstance(t,ast.UnaryOp):
        d,p=top(t.operand,ring,weights,env);return d,ring.mul(ring.const(-1),p)
    da,a=top(t.left,ring,weights,env)
    if isinstance(t.op,ast.Pow):return da*t.right.value,ring.power(a,t.right.value)
    db,b=top(t.right,ring,weights,env)
    if isinstance(t.op,ast.Mult):return da+db,ring.mul(a,b)
    sign=-1 if isinstance(t.op,ast.Sub) else 1
    if da>db:return da,a
    if db>da:return db,ring.mul(ring.const(sign),b)
    return da,ring.add(a,b,sign)


def main():
    packet=json.loads((ROOT/'forms/norm17_degree112.json').read_text())
    variables=['J3','C','z','f','h','r','v_scale','w3','gamma','o','j','c','pair_root','pair_pos1','pair_pos2','pair_pos3','root_sum']
    ports=['beta','K0','MC','MF','cone_A','cone_B']
    require(packet['variables']==variables and packet['fixed_numerals']==ports,'literal domain declaration')
    env={}
    for name,expression in MANUAL:env[name]=normal(parse(expression),env)
    expected=[normal(parse(s),env) for s in ROWS]
    actual=[normal(parse(s),{}) for s in packet['residuals']]
    require(actual==expected,'independently transcribed literal residuals')
    used={n.id for s in packet['residuals'] for n in ast.walk(parse(s)) if isinstance(n,ast.Name)}
    require(used==set(variables+ports),'exact free-symbol closure and liveness')

    # Exact free-polynomial completeness certificate after the root_sum map.
    ring=Ring(['I','u','k','V','tau','y']);e={}
    formulas=[('Q','I**2'),('delta','Q-1'),('A','u*(u+k)+1'),('Bnum','Q*V**2-1'),
              ('root_sum','2*(I*tau+y)-I*(2*u+k)'),('S','tau**2-A'),('T','delta*y**2-Bnum'),
              ('N','(delta*(root_sum**2+2*I*(2*u+k)*root_sum+Q*(k**2-4))-4*Bnum)**2-64*delta*Q*A*Bnum'),
              ('cert','16*((delta*Q*S+T)**2+4*delta*I*tau*y*(delta*Q*S+T)+4*delta*Q*(delta*S*y**2+A*T))')]
    for name,s in formulas:e[name]=ring.eval(parse(s),e)
    require(e['N']==e['cert'],'universal source-residual ideal certificate')

    # Independent exact leading homogeneous component of the authored packet.
    ring2=Ring(variables+ports);weights={v:1 for v in variables};tops={}
    for name,s in MANUAL:tops[name]=top(parse(s),ring2,weights,tops)
    rowtops=[top(parse(s),ring2,weights,tops) for s in ROWS]
    require([d for d,p in rowtops]==[14,5,14,44,56],'unconditional residual-degree upper bounds')
    high=ring2.power(rowtops[-1][1],2)
    coeff=2**52*3**52
    monomial={'r':12,'c':24,'h':4,'f':4,'o':4,'J3':44,'w3':8,'v_scale':12,'beta':44}
    m=tuple(monomial.get(n,0) for n in ring2.names)
    require(high=={m:coeff},'exact top-degree coefficient after specialization')
    require(sum(monomial.get(v,0) for v in variables)==112,'total witness degree')

    # The degree-110 companion is a polynomial translation of the verified
    # degree-112 norm, with its leading cancellation performed exactly.
    d110=json.loads((ROOT/'forms/norm17_degree110.json').read_text())
    require(d110['variables']==variables and d110['fixed_numerals']==ports,'degree110 domain declaration')
    manual110=MANUAL[:-1]+[
        ('center110','root_sum**2+2*I*(2*u+k)*root_sum+Q*(k**2-4)'),
        ('Jtail110','delta*(center110+4*V*root_sum)-4*(V**2-1)'),
        ('Htail110','4*delta*I*(2*u+k)*V'),
        ('norm110','Jtail110**2+2*Jtail110*Htail110+64*delta*Q*A*(1-V**2)+16*delta**2*Q*(k**2-4)*V**2')]
    env110={};top110={}
    for name,s in manual110:
        env110[name]=normal(parse(s),env110)
        top110[name]=top(parse(s),ring2,weights,top110)
    rows110=ROWS[:-1]+['norm110']
    require([normal(parse(s),{}) for s in d110['residuals']]==[normal(parse(s),env110) for s in rows110],
            'degree110 independent literal formulas')
    t110=[top(parse(s),ring2,weights,top110) for s in rows110]
    require([d for d,p in t110]==[14,5,14,44,55],'degree110 upper bounds')
    witness110=dict(monomial);witness110['f']=2;witness110['o']=2;witness110['root_sum']=2
    require(ring2.power(t110[-1][1],2)=={tuple(witness110.get(n,0) for n in ring2.names):coeff},
            'degree110 exact homogeneous certificate')
    ring110=Ring(['I','u','k','V','xi']);envsmall={}
    small110=[('Q','I**2'),('delta','Q-1'),('A','u*(u+k)+1'),('Bnum','Q*V**2-1'),
              ('oldxi','xi+2*V'),
              ('old','(delta*(oldxi**2+2*I*(2*u+k)*oldxi+Q*(k**2-4))-4*Bnum)**2-64*delta*Q*A*Bnum'),
              ('L0','xi**2+2*I*(2*u+k)*xi+Q*(k**2-4)'),
              ('Jtail','delta*(L0+4*V*xi)-4*(V**2-1)'),('Htail','4*delta*I*(2*u+k)*V'),
              ('new','Jtail**2+2*Jtail*Htail+64*delta*Q*A*(1-V**2)+16*delta**2*Q*(k**2-4)*V**2')]
    for n,s in small110:envsmall[n]=ring110.eval(parse(s),envsmall)
    require(envsmall['old']==envsmall['new'],'universal translated norm identity')

    # A different 18-variable companion centers the first root and avoids
    # squaring the signed guard by using a nonnegative SOS unit factor.
    d80=json.loads((ROOT/'forms/center18_degree80.json').read_text())
    vars80=['J3','C','z','f','h','r','v_scale','w3','tau_center','y','gamma','o','j','c','pair_root','pair_pos1','pair_pos2','pair_pos3']
    require(d80['variables']==vars80,'center18 domain declaration')
    common=MANUAL[:next(i for i,(n,s) in enumerate(MANUAL) if n=='Bnum')]
    rows80=['tau_center**2+2*(2*u+k)*tau_center+k**2-4']+ROWS[:3]+['Q*(V**2-y**2)+y**2-1','guard']
    env80={}
    for n,s in common:env80[n]=normal(parse(s),env80)
    require([normal(parse(s),{}) for s in d80['residuals']]==[normal(parse(s),env80) for s in rows80],
            'center18 independent literal rows')
    ring80=Ring(vars80+ports);top80={};weights80={v:1 for v in vars80}
    for n,s in common:top80[n]=top(parse(s),ring80,weights80,top80)
    rows_top80=[top(parse(s),ring80,weights80,top80) for s in rows80]
    require([d for d,p in rows_top80]==[18,14,5,14,10,44],'center18 degree bounds')
    # The unique top contribution is G times the square of the midpoint row.
    high80=ring80.mul(rows_top80[-1][1],ring80.power(rows_top80[0][1],2))
    mon80={'h':6,'w3':8,'v_scale':14,'J3':50,'tau_center':2,'beta':50}
    require(high80=={tuple(mon80.get(n,0) for n in ring80.names):-2**34*3**58},'center18 exact degree80')
    small=Ring(['tau','u','k']);mp={}
    for n,s in [('t','2*tau-2*u-k'),('M','t**2+2*(2*u+k)*t+k**2-4'),('old','4*(tau**2-u*(u+k)-1)')]:
        mp[n]=small.eval(parse(s),mp)
    require(mp['M']==mp['old'],'midpoint source identity')
    parity=Ring(['t','u','k'])
    require(not parity.eval(parse('t**2+2*(2*u+k)*t+k**2-4-(t+k)**2-4*(u*t-1)')),
            'midpoint parity identity')
    companion_reviews=[
        {'packet':'norm17_degree110','status':'PASS','variables':17,'degree':110,
         'literal_binding':True,'translated_norm_identity':True,'unique_leading_component':True},
        {'packet':'center18_degree80','status':'PASS','variables':18,'degree':80,
         'literal_binding':True,'midpoint_identity':True,'parity_identity':True,'unique_leading_component':True,
         'finalizer_proof':'S>=0 and (1+G)(1+S)=1 imply 1+S=1, hence S=G=0'}]

    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text());rawbytes=0;gzipbytes=0
    for name in ports:
        rec=binding['payloads'][name];p=ROOT/'coefficients'/rec['path'];raw=gzip.decompress(p.read_bytes())
        require(hashlib.sha256(raw).hexdigest()==rec['raw_sha256'],'fixed numeral '+name)
        require(int.from_bytes(raw,'little').bit_length()==rec['bits'],'fixed numeral bits '+name)
        rawbytes+=len(raw);gzipbytes+=p.stat().st_size
    require(rawbytes==615883 and gzipbytes==10607,'coherent six-numeral payload')

    result={'status':'PASS','packet':'norm17_degree112','variables':17,'residuals':5,'exact_total_degree':112,
            'literal_formulas_match_independent_transcription':True,'free_symbol_closure':True,
            'universal_completeness_ideal_identity':True,
            'ideal_certificate':'N(root_sum=2(I tau+y)-I(2u+k))=16[(delta Q S+T)^2+4 delta I tau y(delta Q S+T)+4 delta Q(delta S y^2+A T)], S=tau^2-A,T=delta y^2-Bnum',
            'residual_degree_upper_bounds':[d for d,p in rowtops],
            'degree_witness':packet['degree_witness'],'fixed_raw_bytes':rawbytes,'fixed_gzip_bytes':gzipbytes,
            'proof_scope':'Exact finite identities, literal binding and degree. Reverse existence uses rational-root extraction and the unbounded adjacent-coefficient Pell descent reviewed separately.',
            'companion_reviews':companion_reviews}
    out=ROOT/'certificates/INDEPENDENT_REVIEW.json';out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
