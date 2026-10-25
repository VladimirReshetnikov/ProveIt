#!/usr/bin/env python3
"""Independent review of the new odd-sum 14-variable DAGs; no producer import."""
import argparse, hashlib, gzip, json
from pathlib import Path
from collections import Counter
import sympy as S

def require(ok,msg):
    if not ok: raise ValueError(msg)
COMMON={
'J':'6*j+1','qm':'beta*J','q':'qm+1','W':'12*w+4','X':'q*W','Y':'v',
'F':'(K0+W)*C-z*qm','R':'(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*J',
'E':'X*Y','a':'E+Y','H':'4*a+3','Delta':'a**2+H','k':'R+1+h*E',
'eta':'c-Y*k','L':'E*(Y*k)','I':'(2*r+1)*c**2','q3':'q*q**2','M':'2*q3',
'U':'M*H','Klo':'X*(2*X-3*c)-2','Z':'U*n+M*Klo+H*(Y-q3)',
'Derr':'(cone_A*F-q)**2+(cone_B*C-q)**2',
'budget':'(Y*k)**2*(q**2-Derr)-q**2*(4*(Y*eta)**2+(k*q3)**2)',
'carrier':'(Z+U*k)**2+4*U*(L*Z-U)','Bg':'budget-p1**2-p2**2','G':'4*Bg-3'}
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
VARS86=['j','C','z','h','r','v','w','T','c','n','f','p2','p1','s']
VARS94=['j','C','z','h','r','v','w','T','c','n','y','p1','p2','s']
EXTRA86={'Q':'Delta*(f**2-1)','V':'f**2*(c*T-R)-c','strong':'f**2-Delta*I**2',
'delta':'Q-1','Cy':'Q*V**2-1','inner':'delta*(s*(s+1)-Bg+1)-Cy',
'N':'inner**2-G*delta*Cy','P':'(carrier+1)*strong*(N+1)-1'}
EXTRA94={'Ds':'Delta*I**2','Fs':'1+Ds','Q':'Delta*Ds','V':'Fs*(c*T-R)-c',
'auxiliary':'V**2-(Q-1)*y*(2*V+y)','inner':'s*(s+1)-Bg-Ds',
'N':'inner**2-G*Fs','P':'(carrier+1)*(N+1)*auxiliary-1'}

def check_dag(path,degree,ops):
    p=json.loads(path.read_text()); spec=json.loads(path.with_name(path.stem+'_spec.json').read_text())
    variables=VARS86 if degree==86 else VARS94
    expected=COMMON|(EXTRA86 if degree==86 else EXTRA94)
    require(p['variables']==variables and p['variable_count']==14,'variable list')
    require(p['domain']=='unrestricted integers','domain')
    require(set(p['named_registers'])==set(expected),'register set')
    require(set(n for n,f in spec['registers'])==set(expected),'spec register coverage')
    nodes=p['nodes']; count=Counter(); seenvars=set(); seenports=set(); syntactic=[]
    for i,node in enumerate(nodes):
        tag=node[0]
        if tag in ('add','sub','mul'):
            require(len(node)==3 and all(type(j)==int and 0<=j<i for j in node[1:]),'topology')
            count[tag]+=1
            syntactic.append(sum(syntactic[j] for j in node[1:]) if tag=='mul' else max(syntactic[j] for j in node[1:]))
        elif tag=='integer':require(type(node[1])==int,'integer leaf');syntactic.append(0)
        elif tag=='variable':require(node[1] in variables,'variable leaf');seenvars.add(node[1]);syntactic.append(1)
        elif tag=='coefficient':require(node[1] in PORTS,'coefficient leaf');seenports.add(node[1]);syntactic.append(0)
        else:raise ValueError('unknown primitive')
    live=set()
    def visit(i):
        if i in live:return
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):
            for j in nodes[i][1:]:visit(j)
    visit(p['output']);require(live==set(range(len(nodes))),'dead nodes')
    require(seenvars==set(variables) and seenports==set(PORTS),'dead inputs')
    require(dict(count)==p['operation_counts'] and sum(count.values())==p['operations']==ops,'counts')
    require(p['exact_degree']==syntactic[p['output']]==degree,'upper degree')
    env={n:S.Symbol(n) for n in variables+PORTS};cuts={};covered=set()
    for name,_ in spec['registers']:
        target=p['named_registers'][name]
        cache={}
        def expand(i):
            if i in cuts:return cuts[i]
            if i in cache:return cache[i]
            n=nodes[i];tag=n[0]
            if tag=='integer':q=S.Integer(n[1])
            elif tag in ('coefficient','variable'):q=env[n[1]]
            else:
                covered.add(i);a,b=expand(n[1]),expand(n[2]);q=a+b if tag=='add' else a-b if tag=='sub' else a*b
            cache[i]=q;return q
        want=S.sympify(expected[name],locals=env)
        require(S.expand(expand(target)-want)==0,'formula '+name)
        env[name]=S.Symbol(name);cuts[target]=env[name]
    require(covered=={i for i,n in enumerate(nodes) if n[0] in ('add','sub','mul')},'unverified live operations')
    require(p['named_registers']['P']==p['output'],'output')
    # Exact homogeneous component at the certified degree upper bound,
    # specializing C,h,T,p1,p2,s to zero but retaining n for two witnesses.
    retained={'j','w','v','z','r','c','f','y','n'};top=[]
    for i,node in enumerate(nodes):
        tag=node[0]
        if tag=='integer':q=S.Integer(node[1])
        elif tag=='coefficient':q=S.Symbol(node[1])
        elif tag=='variable':q=S.Symbol(node[1]) if node[1] in retained else S.Integer(0)
        else:
            ia,ib=node[1:];a,b=top[ia],top[ib]
            if tag=='mul':q=a*b
            elif syntactic[ia]>syntactic[ib]:q=a
            elif syntactic[ib]>syntactic[ia]:q=b if tag=='add' else -b
            else:q=a+b if tag=='add' else a-b
        top.append(S.expand(q))
    gens=[S.Symbol(n) for n in variables if n in retained]
    poly=S.Poly(top[p['output']],*gens)
    beta=S.Symbol('beta');out=[]
    witnesses=([({'j':54,'w':8,'v':8,'z':6,'r':2,'c':4,'f':4},-2**78*3**62*beta**54),
                 ({'j':51,'w':9,'v':10,'z':5,'r':2,'c':4,'f':4,'n':1},-2**79*3**60*beta**51)] if degree==86 else
                [({'j':58,'w':8,'v':8,'z':7,'r':4,'c':8,'y':1},2**85*3**66*beta**58),
                 ({'j':55,'w':9,'v':10,'z':6,'r':4,'c':8,'y':1,'n':1},2**86*3**64*beta**55)])
    for powers,coefficient in witnesses:
        mon=S.prod(g**powers.get(str(g),0) for g in gens)
        require(sum(powers.values())==degree,'witness degree')
        got=poly.coeff_monomial(mon)
        require(S.expand(got-coefficient)==0,'attained fixed-port coefficient')
        out.append(dict(powers=powers,coefficient=str(coefficient)))
    return dict(file=path.name,sha256=hashlib.sha256(path.read_bytes()).hexdigest(),variables=14,degree=degree,operations=ops,operation_counts=dict(count),all_registers_verified=True,all_gates_covered=True,degree_witnesses=out)

def identity_checks():
    b,d,e,s,x,g,u,p=S.symbols('b d e s x g u p')
    G=4*b+1;K=d*(s*(s+1)-b)-e;N=K*K-G*d*e;xx=2*s+1
    require(S.expand(16*N-((d*(xx*xx+G)-4*e)**2-4*d*d*xx*xx*G))==0,'merger identity')
    require(S.expand(N.subs({b:p*(p+1),s:p+u,e:d*u*u},simultaneous=True))==0,'universal reverse lift')
    A=d*(x*x+G)-4*e
    require(S.expand(d*(x-g)**2-4*e-(A-2*d*x*g+d*(g*g-G)))==0,'forward reconstruction identity')
    for a in range(4):
        D=(a+2)**2-1
        for I in range(4):
            F=1+D*I*I;require(F%4 in (0,1),'Fs parity')
            for f in range(4):require((f*f-D*I*I)%4!=3,'strong unit -1 exclusion')
            for k in range(4):require((k*k-F)%4!=2,'94 norm -2 exclusion')
    return dict(merger=True,forward_reconstruction=True,universal_reverse_lift=True,strong_unit_mod4=True,norm94_mod4=True)

def coefficients(base):
    bind=json.loads((base/'baseline/coefficients/BINDING.json').read_text());out=[]
    for name,m in bind['payloads'].items():
        b=gzip.decompress((base/'baseline/coefficients'/m['file']).read_bytes())
        require(hashlib.sha256(b).hexdigest()==m['raw_sha256'],'coefficient hash '+name)
        require(len(b)==m['raw_bytes'] and int.from_bytes(b,'little').bit_length()==m['bits'],'coefficient dimensions')
        if name=='beta':require(int.from_bytes(b,'little')==(1<<1064921)-1,'actual beta')
        out.append(name)
    return out

def main():
    a=argparse.ArgumentParser();a.add_argument('directory',type=Path);a.add_argument('--output',type=Path);args=a.parse_args()
    r=dict(status='PASS',scope='Exact finite transcription and identities, not an unbounded refutation theorem',identities=identity_checks(),coefficient_payloads=coefficients(args.directory),equations=[check_dag(args.directory/'integer14_degree86_ops112.json',86,112),check_dag(args.directory/'integer14_degree94_ops110.json',94,110)])
    text=json.dumps(r,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
