#!/usr/bin/env python3
"""Independent exact audit. Standard library only; never imports build.py.

Checks the literal DAG against the polynomial specification by exact symbolic
term identities, reconstructs the full six-symbol norm polynomial, checks
weighted cancellation/degree certificates, and authenticates every fixed
coefficient. Unbounded arithmetic semantics are proved in PROOF.md.
"""
import ast
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from polynomial import Poly, parse

ROOT=Path(__file__).resolve().parent
sys.setrecursionlimit(30000)


def need(ok,message):
    if not ok:
        raise ValueError(message)


class Terms:
    """Exact shared terms; commutativity is the only identification used."""
    def __init__(self):
        self.ids={}
    def intern(self,key):
        if key not in self.ids:
            self.ids[key]=len(self.ids)
        return self.ids[key]
    def leaf(self,kind,value):
        return self.intern((kind,value))
    def op(self,kind,a,b):
        if kind in ('add','mul'):
            a,b=sorted((a,b))
        return self.intern((kind,a,b))
    def power(self,x,n):
        need(type(n) is int and n>=0,'fixed nonnegative exponent')
        if n==0:return self.leaf('constant',1)
        if n==1:return x
        half=self.power(x,n//2)
        square=self.op('mul',half,half)
        return self.op('mul',square,x) if n%2 else square
    def parse(self,text,env):
        def visit(node):
            if isinstance(node,ast.Constant) and type(node.value) is int:
                return self.leaf('constant',node.value)
            if isinstance(node,ast.Name):
                need(node.id in env,'declared symbol '+node.id)
                return env[node.id]
            if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):
                return self.op('sub',self.leaf('constant',0),visit(node.operand))
            if isinstance(node,ast.BinOp):
                if isinstance(node.op,ast.Pow):
                    need(isinstance(node.right,ast.Constant),'literal exponent')
                    return self.power(visit(node.left),node.right.value)
                op={ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul'}.get(type(node.op))
                need(op is not None,'ordinary polynomial operation')
                return self.op(op,visit(node.left),visit(node.right))
            raise ValueError('unsupported expression')
        return visit(ast.parse(text,mode='eval').body)


def audit_literal(name,expected_variables,expected_operations):
    packet=json.loads((ROOT/'equations'/f'{name}.json').read_text())
    circuit=json.loads((ROOT/'circuits'/f'{name}.json').read_text())
    parent=json.loads((ROOT/'upstream17.json').read_text())
    need(packet['variables']==circuit['variables'],'variable order')
    need(len(packet['variables'])==expected_variables,'variable count')
    need(packet['fixed_ports']==circuit['fixed_ports'],'fixed ports')
    for key,value in parent['registers'].items():
        if key not in ('I','strong'):
            need(packet['registers'].get(key)==value,'unchanged source register '+key)
    terms=Terms()
    env={x:terms.leaf('variable',x) for x in packet['variables']}
    env.update({x:terms.leaf('fixed',x) for x in packet['fixed_ports']})
    leaves=dict(env)
    for key,expression in packet['registers'].items():
        need(key not in env,'fresh register '+key)
        env[key]=terms.parse(expression,env)
    for expression,inlined in zip(packet['residuals'],packet['fully_inlined_residuals']):
        need(terms.parse(expression,env)==terms.parse(inlined,leaves),'fully inlined residual binding')
    wanted=terms.parse(packet['polynomial_expression'],env)
    actual=[]
    for i,node in enumerate(circuit['nodes']):
        kind=node['type']
        if kind in ('add','sub','mul'):
            need(0<=node['left']<i and 0<=node['right']<i,'topological order')
            actual.append(terms.op(kind,actual[node['left']],actual[node['right']]))
        else:
            need(kind in ('variable','fixed','constant'),'recognized leaf')
            if kind!='constant':
                need(node['value'] in leaves,'declared circuit leaf')
            actual.append(terms.leaf(kind,node['value']))
    need(actual[circuit['output']]==wanted,'exact full circuit polynomial identity')
    live=set()
    def walk(i):
        if i in live:return
        live.add(i)
        node=circuit['nodes'][i]
        if node['type'] in ('add','sub','mul'):
            walk(node['left']);walk(node['right'])
    walk(circuit['output'])
    need(len(live)==len(circuit['nodes']),'all gates and leaves live')
    counts=Counter(node['type'] for node in circuit['nodes'])
    operations=sum(counts[x] for x in ('add','sub','mul'))
    need(operations==expected_operations==circuit['live_binary_operations'],'operation count')
    need(counts['variable']==expected_variables,'all witness coordinates live')
    need(counts['fixed']==6,'all fixed ports live')
    return {'name':name,'variables':expected_variables,'operations':operations,
            'counts':{x:counts[x] for x in ('add','sub','mul')},
            'sha256':hashlib.sha256((ROOT/'circuits'/f'{name}.json').read_bytes()).hexdigest()}


def weighted(poly,weights):
    degree=max(sum(weights.get(v,0)*e for v,e in mon) for mon in poly.terms)
    return degree,Poly({mon:c for mon,c in poly.terms.items()
                       if sum(weights.get(v,0)*e for v,e in mon)==degree})


def source_leaders():
    """Exact leading-form propagation; every potential cancellation is checked."""
    parent=json.loads((ROOT/'upstream17.json').read_text())
    env={x:(1,Poly.symbol(x)) for x in parent['variables']}
    env.update({x:(0,Poly.symbol(x)) for x in parent['fixed_ports']})
    def evaluate(expression):
        def visit(node):
            if isinstance(node,ast.Name):return env[node.id]
            if isinstance(node,ast.Constant):return 0,Poly.integer(node.value)
            if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):
                degree,form=visit(node.operand);return degree,-form
            if isinstance(node,ast.BinOp):
                da,a=visit(node.left)
                if isinstance(node.op,ast.Pow):
                    return da*node.right.value,a**node.right.value
                db,b=visit(node.right)
                if isinstance(node.op,ast.Mult):return da+db,a*b
                sign=-1 if isinstance(node.op,ast.Sub) else 1
                degree=max(da,db)
                form=(a if da==degree else Poly())+(sign*b if db==degree else Poly())
                need(form!=0,'no unexamined cancellation in source expression '+expression)
                return degree,form
            raise ValueError('source polynomial syntax')
        return visit(ast.parse(expression,mode='eval').body)
    for key,expression in parent['registers'].items():
        env[key]=evaluate(expression)
    env['Q']=evaluate('Delta*(f**2-1)')
    aux_degree,aux_form=evaluate('(V+nu)**2-Q*nu*(2*V+nu)-1')
    need(aux_degree==22 and env['main'][0]==14 and env['guard'][0]==44,
         'exact remaining row degrees')
    return env


def algebra():
    # Two-root extraction and the parity-preserving center are ring identities.
    m,k,n,d,Q=[Poly.symbol(x) for x in ('m','k','n','d','Q')]
    A=1+m*(m+1)*k**2
    B0=m*k
    L=n+2*B0
    G=n**2+4*B0*(n-k)-4
    need(G==L**2-4*A,'centered two-root identity')
    U=d*G+Q
    N2=U**2-4*d*L**2*Q
    need((2*d*L**2-U)**2-16*d**2*L**2*A==N2,'rational first-root extraction identity')
    degree2,top2=weighted(N2,{'m':10,'k':7,'n':1,'d':4,'Q':14})
    need(degree2==56 and top2==parse('16*d**2*m**2*k**4'),'complete two-root leading form')
    u,t,Aa=[Poly.symbol(x) for x in ('u','tau','A')]
    L0=u+2*t
    N0=(d*(L0**2-4*Aa)+d*u**2)**2-4*d*L0**2*(d*u**2)
    need(N0==16*d**2*(t**2-Aa)*((t+u)**2-Aa),'two-root completeness factorization')

    # Norm identity, independently checked at the sum of three formal roots.
    a,b,c=[Poly.symbol(x) for x in ('root_a','root_b','root_c')]
    zz=a+b+c
    norm=((zz**2-a**2-b**2-c**2)**2-4*(a**2*b**2+a**2*c**2+b**2*c**2))**2-64*a**2*b**2*c**2*zz**2
    need(norm==0,'universal three-root sum identity')

    V=Poly.symbol('V')
    delta=Q-1;D=d*delta;S=k*(2*m+1)
    need(S**2-4*A==k**2-4,'guard-only separated-radical identity')
    LL=n+2*B0+2*S*V
    Ab=4*A*D;Bb=Q*delta;Cb=4*S**2*d*(Q*V**2-1)
    R=D*LL**2-Ab-Bb-Cb
    T=R**2-4*(Ab*Bb+Ab*Cb+Bb*Cb)
    N3=T**2-64*Ab*Bb*Cb*D*LL**2
    weights={'m':10,'k':7,'V':7,'Q':14,'d':4,'n':1}
    degree3,top3=weighted(N3,weights)
    need(len(N3.terms)==3120,'complete generic three-root norm term count')
    need(degree3==222,'exact weighted three-root norm degree')
    need(top3==parse('2**18*m**8*k**8*V**6*Q**2*d**4'),'complete three-root leading form')
    need(weighted(R,weights)[0]==59 and weighted(T,weights)[0]==111,'intermediate cancellations')

    # Actual source leaders; coefficients remain symbols, not sampled integers.
    tops={}
    for key,expression in (
        ('q','3*beta*J'),('W','12*w'),('X','q*W'),('Y','2*v*q**3'),
        ('E','X*Y'),('a','E'),('F','W*C-q*z'),('R','-F*q**3'),
        ('k','h*E'),('V','-R*f**2'),('m','X*Y**2'),
        ('Q','a**2*f**2'),('d','c**4'),('n','2*n0')):
        tops[key]=parse(expression,tops)
    expected_m=parse('2**4*3**8*beta**7*J**7*w*v**2')
    expected_k=parse('2**3*3**5*beta**4*J**4*h*w*v')
    expected_Q=parse('2**6*3**10*beta**8*J**8*w**2*v**2*f**2')
    expected_V=parse('f**2*(324*beta**3*J**3*w*C-81*beta**4*J**4*z)')
    need(tops['m']==expected_m and tops['k']==expected_k and tops['Q']==expected_Q and tops['V']==expected_V,'actual leading source forms')
    source=source_leaders()
    for key in ('m','k','Q','V'):
        need(source[key][1]==tops[key],'independent complete source leader '+key)
    need(source['guard'][1]**2==tops['Y']**8*tops['k']**8,'complete guard-square leader')
    leading16=top2.substitute(tops)**2
    witness16={'c':16,'J':60,'w':12,'v':16,'h':8}
    witness_variables=['J','C','z','f','h','n0','v','w','nu','gamma','T','c','t','p1','p2','p3']
    need(leading16.coefficient(witness16,witness_variables)==parse('2**48*3**72*beta**60'),'fixed-slice degree112 nonzero coefficient')
    Gtop=tops['Y']**8*tops['k']**8
    leading15=Gtop*top3.substitute(tops)
    witness15={'c':16,'J':184,'w':28,'v':44,'h':16,'z':6,'f':16}
    need(leading15.coefficient(witness15,witness_variables)==parse('2**118*3**212*beta**184'),'fixed-slice degree310 nonzero coefficient')
    return {'two_root_degree':degree2,'three_root_degree':degree3,
        'three_root_terms':len(N3.terms),'exact_degree16':112,'exact_degree15':310,
        'two_root_leading':top2.expression(),'three_root_leading':top3.expression(),
        'all_new_local_polynomial_identities':True}


def coefficients():
    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
    values={}
    for name,item in binding['ports'].items():
        compressed=(ROOT/item['path']).read_bytes()
        raw=gzip.decompress(compressed)
        need(hashlib.sha256(compressed).hexdigest()==item['gzip_sha256'],'compressed coefficient '+name)
        need(hashlib.sha256(raw).hexdigest()==item['raw_sha256'],'raw coefficient '+name)
        need(len(raw)==item['raw_bytes'],'coefficient size '+name)
        value=int.from_bytes(raw,'little')
        need(value.bit_length()==item['bits'],'coefficient bit length '+name)
        values[name]=value
    need(values['beta']==2**1064921-1 and values['beta']>=17,'actual beta')
    need(values['cone_A']==2**1113 and values['cone_B']==2**666104,'unchanged determinant scales')
    return {'all_six_compressed_and_raw_hashes':True,'raw_bytes':sum(x['raw_bytes'] for x in binding['ports'].values())}


def algebra_mod4():
    m,k,V,Q,d,n=map(Poly.symbol,('m','k','V','Q','d','n'))
    A=1+m*(m+1)*k**2;B0=m*k;L=n+B0
    G=n**2+B0*(2*n-k)-1
    need(G==L**2-A,'mod4 first root center')
    U=d*G+Q;N2=U**2-4*d*L**2*Q
    need((2*d*L**2-U)**2-4*d**2*L**2*A==N2,'mod4 first root rational extraction')
    weights={'m':10,'k':7,'V':7,'Q':14,'d':4,'n':1}
    deg2,top2=weighted(N2,weights)
    need(deg2==56 and top2==parse('d**2*m**2*k**4'),'mod4 full two-root leading form')
    u,t,Aa=map(Poly.symbol,('u','tau','A'))
    L0=u+t
    N0=(d*(L0**2-Aa)+d*u**2)**2-4*d*L0**2*(d*u**2)
    need(N0==d**2*(t**2-Aa)*((t+2*u)**2-Aa),'mod4 completeness factorization')
    delta=Q-1;D=d*delta;S=k*(2*m+1);LL=n+B0+4*S*V
    Ab=A*D;Bb=Q*delta;Cb=16*S**2*d*(Q*V**2-1)
    R=D*LL**2-Ab-Bb-Cb
    T=R**2-4*(Ab*Bb+Ab*Cb+Bb*Cb)
    N3=T**2-64*Ab*Bb*Cb*D*LL**2
    deg3,top3=weighted(N3,weights)
    need(len(N3.terms)==3151 and deg3==222,'mod4 generic norm terms and degree')
    need(top3==parse('2**22*m**8*k**8*V**6*Q**2*d**4'),'mod4 complete three-root leader')
    source=source_leaders()
    repl={key:source[key][1] for key in ('m','k','V','Q')}
    repl['d']=parse('c**4')
    variables=['J','C','z','f','h','n0','v','w','nu','gamma','T','c','t','p1','p2','p3']
    coeff16=(top2.substitute(repl)**2).coefficient({'c':16,'J':60,'w':12,'v':16,'h':8},variables)
    need(coeff16==parse('2**40*3**72*beta**60'),'mod4 degree112 actual fixed-slice coefficient')
    final15=source['guard'][1]**2*top3.substitute(repl)
    coeff15=final15.coefficient({'c':16,'J':184,'w':28,'v':44,'h':16,'z':6,'f':16},variables)
    need(coeff15==parse('2**122*3**212*beta**184'),'mod4 degree310 actual fixed-slice coefficient')
    return {'two_root_degree':56,'two_root_leading':top2.expression(),
            'three_root_degree':222,'three_root_terms':len(N3.terms),
            'three_root_leading':top3.expression(),'exact_degree16':112,'exact_degree15':310}


def main():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for name,wanted in pins['inherited_files'].items():
        need(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==wanted,'inherited source pin '+name)
    report={'literal':[audit_literal('integer16_odd_degree112',16,120),
                       audit_literal('integer15_odd_degree310',15,137),
                       audit_literal('integer15_odd_degree306',15,140),
                       audit_literal('integer16_mod4_degree112',16,119),
                       audit_literal('integer15_mod4_degree310',15,136),
                       audit_literal('integer15_mod4_degree306',15,139)],
            'algebra':algebra(),'coefficients':coefficients(),
            'algebra_mod4':algebra_mod4(),
            'status':'PASS','mode':'optimized' if not __debug__ else 'normal',
            'scope':'Exact finite algebra, dimensions, circuit binding and fixed coefficients. Universal semantics are the ordinary proof in PROOF.md.'}
    base=json.loads((ROOT/'equations/integer15_odd_degree310.json').read_text())
    centered=json.loads((ROOT/'equations/integer15_odd_degree306.json').read_text())
    need(centered['registers']['n']=='2*(n0-h*Y*R)+1','exact parity-preserving shear')
    need({k:v for k,v in base['registers'].items() if k!='n'}==
         {k:v for k,v in centered['registers'].items() if k!='n'},'all other centered registers unchanged')
    need(base['residuals']==centered['residuals'] and
         base['polynomial_expression']==centered['polynomial_expression'],'same centered norm and finalizer')
    command=[sys.executable]+([] if __debug__ else ['-O'])+[str(ROOT/'independent_degree/audit.py')]
    child=subprocess.run(command,capture_output=True,text=True,check=True)
    report['centered_degree']=json.loads(child.stdout)
    need(report['centered_degree']['norm_exact_degree']==218 and
         report['centered_degree']['unit_product_exact_degree']==306,'independent centered degree audit')
    base4=json.loads((ROOT/'equations/integer15_mod4_degree310.json').read_text())
    centered4=json.loads((ROOT/'equations/integer15_mod4_degree306.json').read_text())
    need(base4['registers']['n']=='4*n0+2' and centered4['registers']['n']=='4*(n0-h*Y*R)+2','mod4 parity-preserving shear')
    need({k:v for k,v in base4['registers'].items() if k!='n'}==
         {k:v for k,v in centered4['registers'].items() if k!='n'},'mod4 centered registers unchanged')
    command4=[sys.executable]+([] if __debug__ else ['-O'])+[str(ROOT/'independent_degree/audit_mod4.py')]
    child4=subprocess.run(command4,capture_output=True,text=True,check=True)
    report['centered_degree_mod4']=json.loads(child4.stdout)
    need(report['centered_degree_mod4']['norm_exact_degree']==218 and
         report['centered_degree_mod4']['unit_product_exact_degree']==306,'independent mod4 centered degree audit')
    path=ROOT/('CHECKS_OPTIMIZED.json' if not __debug__ else 'CHECKS.json')
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
