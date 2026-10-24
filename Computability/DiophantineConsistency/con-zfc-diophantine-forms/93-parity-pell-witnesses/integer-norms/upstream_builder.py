#!/usr/bin/env python3
"""Literal ordinary polynomial packets. Python standard library only.

Every register is a finite polynomial abbreviation, never an additional unknown.
Power exponents are fixed nonnegative integers. There is no variable power,
division, oracle, proof search, or download in this file.
"""
import ast
import copy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']


def common17():
    return {
        'J0': '3*J+1',
        'q': 'beta*J0+1',
        'W': '4*(3*w+1)',
        'X': 'q*W',
        'Y': '(2*v+1)*q**3',
        'E': 'X*Y',
        'a': '(X+1)*Y',
        'H': '4*a+3',
        'Delta': 'a**2+H',
        'F': '(K0+W)*C-(q-1)*z',
        'alpha': 'q-F-C',
        'R': '(q-F)*(q**3-q)-C*(q**2-1)+(MC+q*MF)*J0',
        'k': 'R+1+h*E',
        'eta': 'c-Y*k',
        'zeta': 'k-eta',
        'I': '(2*r+1)*c**2',
        'V': 'c*(T*f-1)-R*f**2',
        'm': 'X*Y**2',
        'B0': 'm*k',
        'main_gap': 'X+gamma*H',
        'det': '(cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)**2',
        'Z': 'eta*zeta',
        'pos': '1+p1**2+p2**2+p3*(p3+1)',
        'guard': 'det*Z-(t**2-det-Z+1)**2-pos',
        'main': '2*a*c*main_gap+main_gap**2-H*c**2-1',
        'strong': 'I**2-Delta*(f**2-1)',
    }


def source23():
    regs = {
        'J0': '3*J+1', 'q': 'beta*J0+1', 'W': '4*(3*w+1)',
        'X': 'q*W', 'Y': 'a-E', 'k': 'eta+zeta',
        'c': 'Y*k+eta', 'V': 'f*o-c',
        'C': 'q-F-alpha', 'H': '4*a+3', 'Delta': 'a**2+H',
        'B0': 'E*(c-eta)', 'main_gap': 'X+gamma*H',
        'R': '((q-1)*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*J0',
        'det': '(cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)**2',
        'Z': 'eta*zeta', 'pos': '1+p1**2+p2**2+p3*(p3+1)',
        'guard': 'det*Z-(t**2-det-Z+1)**2-pos',
    }
    variables = ['J','F','alpha','z','f','h','r','v','w','tau','eta',
                 'zeta','nu','gamma','o','j','E','a','I','t','p1','p2','p3']
    rows = [
        'a-E-(2*v+1)*q**3',
        'E-X*Y',
        'tau**2+(2*tau-k)*B0-1',
        '2*a*c*main_gap+main_gap**2-H*c**2-1',
        'k-1-h*E-R',
        '(K0+W)*C-(q-1)*z-F',
        'V+k-1-c*j-h*E',
        'I-(2*r+1)*c**2',
        'I**2-Delta*(f**2-1)',
        '(V+nu)**2-I**2*nu*(2*V+nu)-1',
        'guard',
    ]
    return variables, regs, rows


def packets():
    v17 = ['J','C','z','f','h','r','v','w','tau','nu','gamma','T',
           'c','t','p1','p2','p3']
    r17 = common17()
    rows17 = ['tau**2+(2*tau-k)*B0-1', 'main', 'strong',
              '(V+nu)**2-I**2*nu*(2*V+nu)-1', 'guard']
    v16 = [v for v in v17 if v not in ('tau','nu')]
    v16.insert(8, 'n')
    r16 = common17()
    r16.update({
        'A0': '1+m*(m+1)*k**2',
        'S': 'k*(2*m+1)',
        'delta': 'I**2-1',
        'Lnorm': 'delta*(n**2+2*n*(B0+S*V)+2*B0*S*V-m*k**2-1)+S**2*(1-V**2)',
        'Nnorm': 'Lnorm**2-4*delta*A0*S**2*(I**2*V**2-1)',
        'Gsum': 'main**2+strong**2+guard**2',
    })
    v23, r23, rows23 = source23()
    return [
        ('integer23_degree10', v23, r23, rows23, 10,
         {'r':2,'a':4,'eta':4}, '4'),
        ('integer17_degree88', v17, r17, rows17, 88,
         {'h':8,'w':8,'v':16,'J':56}, '2**32*3**64*beta**56'),
        ('integer16_degree192', v16, r16, ['main','strong','guard','Nnorm'], 192,
         {'h':8,'w':16,'v':24,'J':120,'z':8,'f':16},
         '2**64*3**136*beta**120'),
        ('integer16_degree184', v16, r16, ['main','strong','guard','Nnorm'], 184,
         {'h':12,'w':16,'v':28,'J':116,'z':4,'f':8},
         '2**64*3**132*beta**116'),
    ]


def inline(expression, aliases):
    class Expand(ast.NodeTransformer):
        def visit_Name(self, node):
            return copy.deepcopy(aliases.get(node.id, node))
    return ast.fix_missing_locations(Expand().visit(ast.parse(expression, mode='eval').body))


class Circuit:
    """Deterministic literal binary DAG; scalar operations and squares count."""
    def __init__(self, variables, ports):
        self.nodes=[]; self.cache={}; self.symbols={}
        for v in variables: self.symbols[v]=self.leaf('variable',v)
        for p in ports: self.symbols[p]=self.leaf('fixed',p)
    def leaf(self, kind, value):
        key=(kind,value)
        if key not in self.cache:
            self.cache[key]=len(self.nodes)
            self.nodes.append({'type':kind,'value':value})
        return self.cache[key]
    def op(self, op, x, y):
        if op in ('add','mul') and x>y: x,y=y,x
        key=(op,x,y)
        if key not in self.cache:
            self.cache[key]=len(self.nodes)
            self.nodes.append({'type':op,'left':x,'right':y})
        return self.cache[key]
    def power(self, x, n):
        if n==0:return self.leaf('constant',1)
        if n==1:return x
        y=self.power(x,n//2); y=self.op('mul',y,y)
        return self.op('mul',y,x) if n%2 else y
    def parse(self, expression):
        def visit(n):
            if isinstance(n,ast.Name):return self.symbols[n.id]
            if isinstance(n,ast.Constant) and type(n.value) is int:return self.leaf('constant',n.value)
            if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return self.op('sub',self.leaf('constant',0),visit(n.operand))
            if isinstance(n,ast.BinOp):
                if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant):return self.power(visit(n.left),n.right.value)
                op={ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul'}.get(type(n.op))
                if op:return self.op(op,visit(n.left),visit(n.right))
            raise ValueError('unsupported arithmetic expression')
        return visit(ast.parse(expression,mode='eval').body)
    def finish(self, output):
        live=set()
        def walk(i):
            if i in live:return
            live.add(i); node=self.nodes[i]
            if node['type'] in ('add','sub','mul'):
                walk(node['left']);walk(node['right'])
        walk(output)
        remap={x:i for i,x in enumerate(sorted(live))}
        nodes=[]
        for old in sorted(live):
            n=dict(self.nodes[old])
            if n['type'] in ('add','sub','mul'):
                n['left']=remap[n['left']];n['right']=remap[n['right']]
            nodes.append(n)
        counts={op:sum(n['type']==op for n in nodes) for op in ('add','sub','mul')}
        return {'nodes':nodes,'output':remap[output],
                'live_binary_operations':sum(counts.values()),'counts':counts,
                'counting_convention':'All live binary +,-,* including scalar operations and squaring; fixed leaves and reuse free. No minimum claim.'}


def construct(name, variables, regs, rows, degree, witness, coefficient):
    aliases={}; available=set(variables+PORTS)
    for key,expr in regs.items():
        if key in available:raise ValueError('register shadows declared symbol: '+key)
        used={x.id for x in ast.walk(ast.parse(expr,mode='eval')) if isinstance(x,ast.Name)}
        if not used<=available:raise ValueError('undeclared register dependency: '+str(used-available))
        aliases[key]=inline(expr,aliases);available.add(key)
    expanded=[ast.unparse(inline(expr,aliases)) for expr in rows]
    used={n.id for e in expanded for n in ast.walk(ast.parse(e,mode='eval')) if isinstance(n,ast.Name)}
    if used-set(PORTS)!=set(variables):raise ValueError('unbound or unused variable')
    unit_product=name=='integer16_degree184'
    expression=('Gsum+Nnorm+Gsum*Nnorm' if unit_product
                else '+'.join('('+row+')**2' for row in rows))
    packet={'name':name,'domain':'all unrestricted integers','variables':variables,
            'variable_count':len(variables),'fixed_ports':PORTS,'registers':regs,
            'residuals':rows,'fully_inlined_residuals':expanded,'residual_count':len(rows),
            'single_equation':('positive sum-of-squares factor times norm factor minus one = 0'
                               if unit_product else 'sum of the squares of the listed residuals = 0'),
            'combination':('positive_unit_product' if unit_product else 'sum_of_squares'),
            'polynomial_expression':expression,
            'exact_degree':degree,'leading_certificate':{'powers':witness,'coefficient':coefficient},
            'coefficient_binding':'../coefficients/BINDING.json',
            'proof':'../PROOF.md',
            'semantic_scope':'New ordinary reductions; inherited named native/compiler/Pell and ZFC-refutation calibration. Not a new internal-ZFC proof certificate.'}
    c=Circuit(variables,PORTS)
    for key,expr in regs.items():c.symbols[key]=c.parse(expr)
    total=c.parse(expression)
    circuit=c.finish(total)
    circuit.update({'name':name,'variables':variables,'fixed_ports':PORTS,
                    'coefficient_binding':'../coefficients/BINDING.json'})
    return packet,circuit


def main():
    metrics=[]
    for values in packets():
        packet,circuit=construct(*values)
        name=packet['name']
        (ROOT/'equations'/f'{name}.json').write_text(json.dumps(packet,indent=2)+'\n')
        (ROOT/'circuits'/f'{name}.json').write_text(json.dumps(circuit,indent=2)+'\n')
        metrics.append({k:packet[k] for k in ['name','variable_count','residual_count','exact_degree']}|
                       {'live_binary_operations':circuit['live_binary_operations'],'gate_counts':circuit['counts']})
    (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps(metrics,indent=2))


if __name__=='__main__':main()
