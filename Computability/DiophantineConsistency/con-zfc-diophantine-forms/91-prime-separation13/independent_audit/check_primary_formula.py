#!/usr/bin/env python3
"""Exact gate-level binding of the primary P13 to its hand-written formula.

This implementation does not import either circuit builder.  It independently
constructs the native expressions, the cleared four-root norm, and the last
quadratic norm, then compares canonical expression DAGs over Z.  Only exact
ring identities for associativity, commutativity, integer scalar collection,
and neutral elements are used.  No sampling is involved in this comparison.
"""
from pathlib import Path
from collections import defaultdict
import ast,gzip,hashlib,json

ROOT=Path(__file__).resolve().parent.parent

def require(ok,msg):
    if not ok:raise ValueError(msg)

class Expressions:
    def __init__(self):self.nodes=[];self.cache={}
    def intern(self,key):
        if key not in self.cache:
            self.cache[key]=len(self.nodes);self.nodes.append(key)
        return self.cache[key]
    def lit(self,n):return self.intern(('constant',int(n)))
    def leaf(self,name):return self.intern(('leaf',name))
    def product(self,coefficient,factors):
        factors=tuple(sorted((k,v) for k,v in factors.items() if v))
        if not coefficient:return self.lit(0)
        if not factors:return self.lit(coefficient)
        if coefficient==1 and len(factors)==1 and factors[0][1]==1:return factors[0][0]
        return self.intern(('product',coefficient,factors))
    def mul(self,*args):
        coefficient=1;factors=defaultdict(int)
        for arg in args:
            node=self.nodes[arg]
            if node[0]=='constant':coefficient*=node[1]
            elif node[0]=='product':
                coefficient*=node[1]
                for key,exponent in node[2]:factors[key]+=exponent
            else:factors[arg]+=1
        return self.product(coefficient,factors)
    def add(self,*args):
        constant=0;terms=defaultdict(int)
        for arg in args:
            node=self.nodes[arg]
            if node[0]=='constant':constant+=node[1]
            elif node[0]=='sum':
                constant+=node[1]
                for key,coefficient in node[2]:terms[key]+=coefficient
            elif node[0]=='product':
                key=self.product(1,dict(node[2]));terms[key]+=node[1]
            else:terms[arg]+=1
        terms=tuple(sorted((key,value) for key,value in terms.items() if value))
        if not terms:return self.lit(constant)
        if not constant and len(terms)==1:return self.mul(self.lit(terms[0][1]),terms[0][0])
        return self.intern(('sum',constant,terms))
    def sub(self,a,b):return self.add(a,self.mul(self.lit(-1),b))
    def power(self,a,n):
        require(type(n) is int and n>=0,'fixed nonnegative integer exponent')
        node=self.nodes[a]
        if node[0]=='constant':return self.lit(node[1]**n)
        if node[0]=='product':return self.product(node[1]**n,{key:value*n for key,value in node[2]})
        return self.product(1,{a:n})
    def parse(self,expression,lookup):
        def walk(node):
            if isinstance(node,ast.Name):return lookup(node.id)
            if isinstance(node,ast.Constant):
                require(type(node.value) is int,'integer constant');return self.lit(node.value)
            if isinstance(node,ast.UnaryOp):
                require(isinstance(node.op,(ast.USub,ast.UAdd)),'allowed unary sign')
                value=walk(node.operand)
                return self.sub(self.lit(0),value) if isinstance(node.op,ast.USub) else value
            require(isinstance(node,ast.BinOp),'polynomial expression')
            if isinstance(node.op,ast.Pow):
                require(isinstance(node.right,ast.Constant),'fixed power')
                return self.power(walk(node.left),node.right.value)
            a,b=walk(node.left),walk(node.right)
            if isinstance(node.op,ast.Add):return self.add(a,b)
            if isinstance(node.op,ast.Sub):return self.sub(a,b)
            require(isinstance(node.op,ast.Mult),'no division or other operation')
            return self.mul(a,b)
        return walk(ast.parse(expression,mode='eval').body)

class Pairs:
    def __init__(self,algebra,radicand):self.a=algebra;self.rad=radicand
    def scalar(self,value):return value,self.a.lit(0)
    def lit(self,n):return self.scalar(self.a.lit(n))
    def add(self,x,y):return self.a.add(x[0],y[0]),self.a.add(x[1],y[1])
    def sub(self,x,y):return self.a.sub(x[0],y[0]),self.a.sub(x[1],y[1])
    def mul(self,x,y):
        a=self.a
        return (a.add(a.mul(x[0],y[0]),a.mul(self.rad,x[1],y[1])),
                a.add(a.mul(x[0],y[1]),a.mul(x[1],y[0])))
    def norm(self,x):return self.a.sub(self.a.mul(x[0],x[0]),self.a.mul(self.rad,x[1],x[1]))

def cleared_norm4(a,z,r1,r2,r3,num,den):
    """Independent transcription of the displayed closed norm formula."""
    square=lambda value:a.mul(value,value)
    scalar=lambda n,value:a.mul(a.lit(n),value)
    sigma=a.add(a.add(r1,r2),r3)
    products=a.add(a.mul(r1,r2),a.mul(a.add(r1,r2),r3))
    triple=a.mul(a.mul(r1,r2),r3)
    z2=square(z);d2=square(den)
    h=a.add(a.mul(den,a.sub(z2,sigma)),num)
    t=a.mul(a.mul(den,num),z2)
    k=a.add(square(h),scalar(4,a.sub(t,a.mul(d2,products))))
    r=scalar(16,a.mul(a.mul(d2,den),triple))
    b=a.sub(a.mul(h,k),r)
    e=a.sub(a.add(square(k),scalar(16,a.mul(t,square(h)))),
            scalar(4,a.mul(r,a.add(a.mul(den,z2),num))))
    return a.sub(square(e),scalar(64,a.mul(t,square(b))))

# These are the mathematical P13 abbreviations, independent of JSON metadata.
FORMULA={
 'J':'6*J6+1','q':'beta*J+1','W':'4*(3*w3+1)','X':'q*W',
 'Y':'(2*v_scale+1)*q**3','E':'X*Y','a':'(X+1)*Y',
 'H':'4*a+3','Delta':'a**2+H','c':'2*c1+1',
 'F':'(K0+W)*C-z*(q-1)',
 'R':'(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*J',
 'k':'R+1+h*E','eta':'c-Y*k','u':'E*Y*k','A':'u*(u+k)+1',
 'U':'(2*r+1)*c**2','F2':'1+Delta*U**2','Q':'Delta**2*U**2',
 'delta':'Q-1','V':'F2*(c*T-R)-c','D0':'X+a*c','Dm':'1+Delta*c**2',
 'det':'(cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)**2',
 'eta_zeta':'eta*(k-eta)',
 'Bguard':'det*eta_zeta-(pair_root**2-det-eta_zeta+1)**2-1-pair_pos2**2-pair_pos3*(pair_pos3+1)',
 't':'2*u+k','f_center':'(a+2)*U'
}

def source_binding():
    local=ROOT/'new_integer_compression/coefficients'
    upstream=ROOT/'inherited/source34_six_port_payloads'
    binding=json.loads((local/'BINDING.json').read_text())
    require(binding['backend']=='mixed-parity-unrounded-1064921','source-34 tuple')
    require(binding['MF_convention']=='already shifted by beta','MF shift convention')
    ports={};checks={}
    for name,record in binding['payloads'].items():
        raw=gzip.decompress((local/record['path']).read_bytes())
        original=gzip.decompress((upstream/(name+'.bin.gz')).read_bytes())
        require(raw==original,'same complete source-34 coefficient '+name)
        require(hashlib.sha256(raw).hexdigest()==record['raw_sha256'],'bound payload hash '+name)
        ports[name]=int.from_bytes(raw,'little');checks[name]=record['raw_sha256']
    require(ports['beta']==2**1064921-1,'literal beta')
    require(ports['cone_A']==2**1113 and ports['cone_B']==2**666104,'literal cone scales')
    return {'whole_source34_tuple_identical':True,'MF_shifted_exactly_as_in_source':True,
            'raw_sha256':checks}

def verify_all():
    path=ROOT/'new_integer_compact/five_root_integer13_compact.json'
    packet=json.loads(path.read_text());a=Expressions()
    variables=packet['variables'];ports=packet['fixed_ports']
    require(len(variables)==13 and len(set(variables))==13,'thirteen distinct variables')
    require(set(ports)=={'beta','K0','MC','MF','cone_A','cone_B'},'six fixed ports')
    named={name:a.leaf('v:'+name) for name in variables}
    named.update({name:a.leaf('c:'+name) for name in ports})
    active=set()
    def math_lookup(name):
        if name in named:return named[name]
        require(name in FORMULA,'unknown hand-written abbreviation '+name)
        require(name not in active,'cyclic hand-written formula')
        active.add(name);named[name]=a.parse(FORMULA[name],math_lookup);active.remove(name)
        return named[name]
    # Verify every explanatory definition against the independently stated formula.
    for name,expression in packet['polynomial_definitions'].items():
        require(name in FORMULA,'unreviewed retained abbreviation '+name)
        require(a.parse(expression,math_lookup)==math_lookup(name),'changed explanatory definition '+name)
    Z=a.parse('H*(xi+18*f_center+3*t+2*V)+2*D0',math_lookup)
    fifth=a.parse('2916*H**2*Bguard',math_lookup)
    qa=Pairs(a,fifth)
    normpair=cleared_norm4(qa,(Z,a.lit(-1)),
        qa.scalar(a.parse('324*H**2*F2',math_lookup)),
        qa.scalar(a.parse('36*H**2*A',math_lookup)),
        qa.scalar(a.parse('4*Dm',math_lookup)),
        qa.scalar(a.parse('4*H**2*(Q*V**2-1)',math_lookup)),
        qa.scalar(math_lookup('delta')))
    expected=qa.norm(normpair)
    values={'v:'+name:a.leaf('v:'+name) for name in variables}
    values.update({'c:'+name:a.leaf('c:'+name) for name in ports})
    dependencies={key:({key} if key.startswith('v:') else set()) for key in values}
    def read(token):
        if token.startswith('n:'):return a.lit(int(token[2:]))
        require(token in values,'unbound literal gate '+token);return values[token]
    def deps(token):return set() if token.startswith('n:') else dependencies[token]
    for fixed,nodes in [(True,packet['fixed_recipes']),(False,packet['nodes'])]:
        for node in nodes:
            require(node['id'] not in values,'duplicate gate identifier')
            left,right=read(node['left']),read(node['right'])
            dependencies[node['id']]=deps(node['left'])|deps(node['right'])
            if fixed:require(not dependencies[node['id']],'quantified input in free constant recipe')
            operation=node['op'];require(operation in ('add','sub','mul'),'allowed literal operation')
            values[node['id']]=getattr(a,operation)(left,right)
    require(values[packet['output']]==expected,'literal primary output differs from mathematical P13')
    require(values[packet['norm_output']]==expected,'literal raw norm differs from mathematical P13')
    require(dependencies[packet['output']]=={'v:'+name for name in variables},'every declared variable participates')
    for name in packet['polynomial_definitions']:
        require(math_lookup(name) in values.values(),'native abbreviation absent from actual literal gates '+name)
    result={'primary_formula_exactly_matches_literal_gates':True,
        'method':'Independent native formula and norm transcription; exact canonical expression DAG comparison using elementary integer ring identities only',
        'no_builder_imports':True,'no_sampling':True,
        'polynomial_definitions_checked':len(packet['polynomial_definitions']),
        'live_operation_count':len(packet['nodes']),
        'variables':variables,'fixed_ports':ports,
        'four_root_denominator_power':8,'final_denominator_power':16,
        'fifth_root_squared':'2916 H^2 Bguard = (54 H)^2 Bguard',
        'sum_coordinate_shift':'xi -> xi - 54 p1, therefore Z -> Z - 54 H p1',
        'four_root_radicands':['324 H^2 F2','36 H^2 A','4 Dm','4 H^2 (QV^2-1)/(Q-1)'],
        'literal_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'source_binding':source_binding()}
    return result

def main():
    result=verify_all()
    (ROOT/'independent_audit/PRIMARY_FORMULA_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
