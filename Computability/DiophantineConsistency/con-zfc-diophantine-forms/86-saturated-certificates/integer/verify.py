#!/usr/bin/env python3
"""Exact local identities, literal/DAG binding, degrees, and actual numerals.

This auditor does not import the generator. Universal Pell/compiler correctness
is a mathematical dependency, not inferred from any finite test below.
"""
import ast
from fractions import Fraction
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import random
from polynomial import Poly, parse, require

ROOT=Path(__file__).resolve().parent


def read(path):return json.loads((ROOT/path).read_text())


def local_identities():
    identities={
        'first_root_centering':
            '(tau+m*k)**2-1-m*(m+1)*k**2-(tau**2+(2*tau-k)*m*k-1)',
        'main_root_centering':
            '(a*c+s)**2-(a**2+H)*c**2-1-(2*a*c*s+s**2-H*c**2-1)',
        'auxiliary_root_centering':
            'I**2*(V**2-(V+nu)**2)+(V+nu)**2-1-((V+nu)**2-I**2*nu*(2*V+nu)-1)',
        'transport_pivot':
            '(K0+W)*C-(q-1)*z-((K0+W)*C-(q-1)*z)',
        'packing_pivot':
            '((q-1)*(q-F)+(q-F-C))*(q**2-1)+(MC+q*MF)*J0-((q-F)*(q**3-q)-C*(q**2-1)+(MC+q*MF)*J0)',
        'quotient_first_congruence':
            'c*(T*f-1)-R*f**2+c-f*(c*T-R*f)',
        'quotient_second_congruence':
            'c*(T*f-1)-R*f**2+R-c*(T*f-1-R*b)-R*(c*b-f**2+1)',
        'old_quotient_divisibility':
            'f*(o*f+R)-o*(f**2-1)-(o+R*f)',
        'new_k_restoration':
            '1-(c*(T*f-1)-R*f**2)+(T*f-1-R*b)*c+h*E-(R+1+h*E)-R*(f**2-c*b-1)',
        'separation_identity':
            '(k*(2*m+1))**2-4*(1+m*(m+1)*k**2)-(k**2-4)',
        'centered_norm_linear':
            '(I**2-1)*((n+m*k+S*V)**2-(1+m*(m+1)*k**2))-S**2*(I**2*V**2-1)-((I**2-1)*(n**2+2*n*(m*k+S*V)+2*m*k*S*V-m*k**2-1)+S**2*(1-V**2))',
        'quadratic_norm_factor_identity':
            '((n**2-A-B)**2-4*A*B)-((n**2+A-B)**2-4*n**2*A)',
        'descent_norm_identity':
            'Q*((2*Q-1)*V-2*(Q-1)*y)**2-(Q-1)*((2*Q-1)*y-2*Q*V)**2-(Q*V**2-(Q-1)*y**2)',
    }
    for name,expression in identities.items():
        require(parse(expression)==0,'exact local polynomial identity: '+name)
    # Root formula: 4n^2(tau^2-A) equals the norm numerator.
    require(parse('(n**2+A-B)**2-4*n**2*A-(n**4+A**2+B**2-2*n**2*A-2*n**2*B-2*A*B)')==0,
            'rational root extraction')
    return list(identities)+['rational_root_extraction']


def coefficients():
    binding=read('coefficients/BINDING.json');values={}
    for port,data in binding['ports'].items():
        raw=gzip.decompress((ROOT/data['path']).read_bytes())
        require(hashlib.sha256(raw).hexdigest()==data['raw_sha256'],'actual raw coefficient: '+port)
        require(len(raw)==data['raw_bytes'],'coefficient byte length: '+port)
        values[port]=int.from_bytes(raw,'little')
        require(values[port].bit_length()==data['bits'],'coefficient bit length: '+port)
        require(raw[-1]!=0,'minimal coefficient encoding: '+port)
    require(values['beta']==2**1064921-1,'exact Mersenne coefficient')
    require(values['cone_A']==2**1113 and values['cone_B']==2**666104,'exact fixed guard scales')
    b=values['beta']
    require(b%3==1 and 0<values['MC']<b and b<values['MF']<2*b and values['K0']>=0,'authentic source scalar bounds')
    require(sum(d['raw_bytes'] for d in binding['ports'].values())==615883,'complete tuple bytes')
    # Run only the inspected finite recipe function, not its historical CLI
    # wrapper. Every check in construct() is an explicit require, including -O.
    spec=importlib.util.spec_from_file_location('fixed_native_recipe',ROOT/'coefficients/recipe/source34_builder.py')
    recipe=importlib.util.module_from_spec(spec);spec.loader.exec_module(recipe)
    rebuilt,audit=recipe.construct()
    mapping={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}
    for port,old in mapping.items():require(values[port]==rebuilt[old],'full coefficient reconstruction: '+port)
    require(audit['d']==1064921 and audit['b']==121 and audit['L']==8801,'native recipe dimensions')
    return values


def source23_restoration():
    packet=read('equations/integer23_degree10.json')
    aliases={}
    for name,expr in packet['registers'].items():aliases[name]=parse(expr,aliases)
    rows=[parse(x,aliases) for x in packet['residuals']]
    restoration={name:Poly.symbol(name) for name in packet['variables']}
    restoration.update({
        'J3':parse('J'), 'w3':parse('w'), 'v_scale':parse('v'),
        'N':parse('q**3',aliases),'X':aliases['X'], 'L':parse('q**2-1',aliases),
        'C2':parse('c**2',aliases),'F2':parse('f**2'), 'Baux':parse('I**2'),
        'g':parse('nu*(2*V+nu)',aliases),'Delta':aliases['Delta'],
        'D':parse('a*c+main_gap',aliases),'P':parse('k+B0',aliases),
        'c':aliases['c'],'V':aliases['V'],
        'tau':parse('tau+B0',aliases),'y':parse('V+nu',aliases),
    })
    parent=read('upstream/quartic37.json')
    receipts=[];retained=[]
    for i,expr in enumerate(parent['residuals'][:-2]):
        pol=parse(expr).substitute(restoration)
        if pol==0:
            receipts.append({'parent_row':i,'result':'identically zero'})
        else:
            hits=[j for j,row in enumerate(rows[:-1]) if pol==row or pol==-row]
            require(len(hits)==1,'full retained arithmetic source row '+str(i))
            retained.append(hits[0]);receipts.append({'parent_row':i,'retained_row':hits[0]})
    require(sorted(retained)==list(range(10)),'all arithmetic rows matched once')
    require(sum('result' in r for r in receipts)==12,'twelve monic definitions eliminated')
    # The two old guards have precisely the promised d and eta*zeta arguments.
    cone={'cone_pos1':Poly.integer(0),'cone_pos2':Poly.integer(0),'cone_pos3':Poly.integer(0)}
    guard=parse(parent['residuals'][-2]).substitute(restoration).substitute(cone)
    require(guard==aliases['det']-1,'source determinant guard literal binding')
    private={f'eta_zeta_pos{i}':Poly.integer(0) for i in (1,2,3)}
    guard=parse(parent['residuals'][-1]).substitute(restoration).substitute(private)
    require(guard==aliases['Z']-1,'source eta*zeta guard literal binding')
    return receipts


def source17_restoration():
    """Every arithmetic source37 row, with the one divisibility relation exposed.

    b is an audit symbol for (f^2-1)/c; it is NOT a variable of the equation.
    Its integer existence is supplied by the proved strong-Pell bootstrap.
    """
    packet=read('equations/integer17_degree88.json')
    aliases={}
    # The full joint guard is deliberately not expanded: it is an existential
    # conjunction theorem, whereas the source arithmetic is an exact identity.
    for name,expr in packet['registers'].items():
        if name not in ('guard','Z'):aliases[name]=parse(expr,aliases)
    rowexprs=packet['residuals'][:-1]
    rows=[parse(x,aliases) for x in rowexprs]
    restore={name:Poly.symbol(name) for name in packet['variables']}
    restore.update({
        'J3':parse('J'),'w3':parse('w'),'v_scale':parse('v'),
        'F':aliases['F'],'alpha':aliases['alpha'],
        'N':parse('q**3',aliases),'X':aliases['X'],'L':parse('q**2-1',aliases),
        'E':aliases['E'],'a':aliases['a'], 'eta':aliases['eta'],'zeta':aliases['zeta'],
        'C2':parse('c**2'),'F2':parse('f**2'),'Baux':parse('I**2',aliases),
        'g':parse('nu*(2*V+nu)',aliases),'Delta':aliases['Delta'],
        'D':parse('a*c+main_gap',aliases),'P':parse('k+B0',aliases),
        'V':aliases['V'],'I':aliases['I'],
        'tau':parse('tau+B0',aliases),'y':parse('V+nu',aliases),
        'o':parse('c*T-R*f',aliases),'j':parse('T*f-1-R*b',aliases),
    })
    parent=read('upstream/quartic37.json');receipts=[];retained=[]
    conditional=parse('R*(c*b-f**2+1)',aliases)
    for i,expr in enumerate(parent['residuals'][:-2]):
        pol=parse(expr).substitute(restore)
        if pol==0:receipts.append({'parent_row':i,'result':'identically zero'})
        elif pol==conditional or pol==-conditional:
            receipts.append({'parent_row':i,'result':'plus or minus R*(c*b-f^2+1)',
                             'b_status':'proved integral witness; not a polynomial unknown'})
        else:
            hits=[j for j,row in enumerate(rows) if pol==row or pol==-row]
            require(len(hits)==1,'full source17 arithmetic restoration '+str(i))
            retained.append(hits[0]);receipts.append({'parent_row':i,'retained_row':hits[0]})
    require(sorted(retained)==list(range(4)),'all four retained arithmetic norms matched once')
    require(sum('b_status' in r for r in receipts)==1,'one precisely exposed divisibility use')
    return receipts


def evaluate(expression,values,modulus=None):
    def visit(n):
        if isinstance(n,ast.Name):return values[n.id]
        if isinstance(n,ast.Constant) and type(n.value) is int:return n.value
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -visit(n.operand)
        if isinstance(n,ast.BinOp):
            x=visit(n.left)
            if isinstance(n.op,ast.Pow):
                require(isinstance(n.right,ast.Constant) and type(n.right.value) is int and n.right.value>=0,'only fixed polynomial powers')
                return pow(x,n.right.value,modulus) if modulus else x**n.right.value
            y=visit(n.right)
            if isinstance(n.op,ast.Add):v=x+y
            elif isinstance(n.op,ast.Sub):v=x-y
            elif isinstance(n.op,ast.Mult):v=x*y
            else:raise ValueError('not ordinary polynomial arithmetic')
            return v%modulus if modulus else v
        raise ValueError('unsupported polynomial AST')
    return visit(ast.parse(expression,mode='eval').body)


def exact_degree_and_dag(packet,circuit,actual):
    variables=packet['variables'];ports=packet['fixed_ports']
    require(len(variables)==packet['variable_count'] and len(set(variables))==len(variables),'variable inventory')
    # A jet is a degree upper bound and the exact homogeneous component there.
    # Zero high components are retained as upper bounds, never mistaken for
    # exact degree. The final specified component must be nonzero.
    def add(a,b,sign=1):
        d=max(a[0],b[0]);p=Poly()
        if a[0]==d:p=p+a[1]
        if b[0]==d:p=p+sign*b[1]
        return d,p
    def mul(a,b):return a[0]+b[0],a[1]*b[1]
    def power(a,n):
        out=(0,Poly.integer(1))
        for _ in range(n):out=mul(out,a)
        return out
    env={v:(1,Poly.symbol(v)) for v in variables}
    env.update({p:(0,Poly.symbol(p)) for p in ports})
    def jet(expression):
        def walk(n):
            if isinstance(n,ast.Name):return env[n.id]
            if isinstance(n,ast.Constant):return 0,Poly.integer(n.value)
            if isinstance(n,ast.UnaryOp):
                a=walk(n.operand);return a[0],-a[1]
            if isinstance(n,ast.BinOp):
                a=walk(n.left)
                if isinstance(n.op,ast.Pow):return power(a,n.right.value)
                b=walk(n.right)
                if isinstance(n.op,ast.Add):return add(a,b)
                if isinstance(n.op,ast.Sub):return add(a,b,-1)
                if isinstance(n.op,ast.Mult):return mul(a,b)
            raise ValueError('non-polynomial jet')
        return walk(ast.parse(expression,mode='eval').body)
    for name,expr in packet['registers'].items():env[name]=jet(expr)
    row_jets=[jet(row) for row in packet['residuals']]
    equation=jet(packet['polynomial_expression'])
    require(equation[0]==packet['exact_degree'],'polynomial degree upper bound')
    cert=packet['leading_certificate']
    coefficient=equation[1].coefficient(cert['powers'],variables)
    require(coefficient==parse(cert['coefficient']),'exact highest-degree coefficient')
    require(coefficient!=0,'nonzero leading coefficient over symbolic ports')
    # All supplied coefficient formulas are positive on this actual slice.
    require(evaluate(cert['coefficient'],{'beta':1})>0,'positive beta coefficient certificate')
    # Exact DAG to AST binding by recursively inlining each gate and comparing
    # independent sparse-ring values is too large for the norm endpoint. Instead
    # reconstruct the free term algebra from the packet and compare its canonical
    # binary trees after commutative operand sorting, with the same documented
    # binary-power parenthesization. No modular sampling is used for this binding.
    def canonical(op,x,y):
        if op in ('add','mul') and repr(x)>repr(y):x,y=y,x
        return (op,x,y)
    terms={v:('variable',v) for v in variables}|{p:('fixed',p) for p in ports}
    def ast_term(expression):
        def walk(n):
            if isinstance(n,ast.Name):return terms[n.id]
            if isinstance(n,ast.Constant):return ('constant',n.value)
            if isinstance(n,ast.UnaryOp):return canonical('sub',('constant',0),walk(n.operand))
            if isinstance(n,ast.BinOp):
                x=walk(n.left)
                if isinstance(n.op,ast.Pow):
                    def pwr(n):
                        if n==0:return ('constant',1)
                        if n==1:return x
                        y=pwr(n//2);z=canonical('mul',y,y)
                        return canonical('mul',z,x) if n%2 else z
                    return pwr(n.right.value)
                return canonical({ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul'}[type(n.op)],x,walk(n.right))
            raise ValueError('invalid AST')
        return walk(ast.parse(expression,mode='eval').body)
    for key,expr in packet['registers'].items():terms[key]=ast_term(expr)
    trees=[ast_term(row) for row in packet['residuals']]
    require(trees==[ast_term(row) for row in packet['fully_inlined_residuals']],
            'exact fully inlined term-algebra binding')
    expected=ast_term(packet['polynomial_expression'])
    dagterms=[];counts={op:0 for op in ('add','sub','mul')}
    for i,node in enumerate(circuit['nodes']):
        typ=node['type']
        if typ in ('variable','fixed','constant'):
            dagterms.append((typ,node['value']))
        else:
            require(0<=node['left']<i and 0<=node['right']<i,'acyclic literal DAG')
            dagterms.append(canonical(typ,dagterms[node['left']],dagterms[node['right']]))
            counts[typ]+=1
    require(dagterms[circuit['output']]==expected,'exact literal binary term-algebra binding')
    require(counts==circuit['counts'] and sum(counts.values())==circuit['live_binary_operations'],'binary gate count')
    live=set()
    def mark(i):
        if i in live:return
        live.add(i);node=circuit['nodes'][i]
        if node['type'] in counts:mark(node['left']);mark(node['right'])
    mark(circuit['output']);require(len(live)==len(circuit['nodes']),'all gates and leaves live')
    # Independent modular evaluations with ACTUAL fixed integers are additional
    # transcription diagnostics, not an identity proof or semantic theorem.
    rng=random.Random(20261023)
    for prime in (1000000007,1000000009):
        for _ in range(12):
            vals={p:x%prime for p,x in actual.items()}|{v:rng.randrange(prime) for v in variables}
            e=dict(vals)
            for key,expr in packet['registers'].items():e[key]=evaluate(expr,e,prime)
            rowvals=[evaluate(row,e,prime) for row in packet['residuals']]
            require(rowvals==[evaluate(row,vals,prime) for row in packet['fully_inlined_residuals']], 'fully inlined transcription diagnostic')
            d=[]
            for node in circuit['nodes']:
                typ=node['type']
                if typ=='constant':x=node['value']
                elif typ in ('variable','fixed'):x=vals[node['value']]
                elif typ=='add':x=d[node['left']]+d[node['right']]
                elif typ=='sub':x=d[node['left']]-d[node['right']]
                else:x=d[node['left']]*d[node['right']]
                d.append(x%prime)
            require(d[circuit['output']]==evaluate(packet['polynomial_expression'],e,prime),'actual-coefficient circuit diagnostic')
    return {'name':packet['name'],'variables':len(variables),'rows':len(row_jets),
            'residual_degree_upper_bounds':[d for d,p in row_jets],
            'exact_polynomial_degree':equation[0],'leading_coefficient_verified':cert,
            'leading_homogeneous_terms':len(equation[1].terms),
            'live_binary_operations':sum(counts.values()),'literal_DAG_exact_binding':True,
            'modular_diagnostics':24}


def diagnostics():
    # A deliberately small rational-root exercise for the universal norm lemma.
    # It tests extracted roots and the V=0 rejection; it is not the proof.
    count=0
    for Q in range(2,30):
        for V in range(-15,16):
            B=Fraction(Q*V*V-1,Q-1)
            for a in range(1,7):
                A=a*a; S=A+1
                for n in range(-30,31):
                    norm=(n*n-A-S*S*B)**2-4*A*S*S*B
                    if norm==0:
                        require(V!=0 and n!=0,'separated norm degeneracies excluded')
                        t=Fraction(n*n+A-S*S*B,2*n);y=(n-t)/S
                        require(t.denominator==1 and y.denominator==1,'rational-root integrality diagnostic')
                        require(t*t==A and Q*V*V-(Q-1)*y*y==1,'recovered norm equations')
                        count+=1
    return {'small_root_extractions':count,'status':'diagnostics only; proof in PROOF.md'}


def main():
    pins=read('SOURCE_PINS.json')
    for item in pins['inputs']:
        raw=(ROOT/item['retained']).read_bytes()
        require(len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],
                'retained source byte identity: '+item['retained'])
    local=local_identities();actual=coefficients();rows=source23_restoration()
    rows17=source17_restoration()
    results=[]
    for name in ('integer23_degree10','integer17_degree88','integer16_degree192','integer16_degree184'):
        results.append(exact_degree_and_dag(read('equations/'+name+'.json'),read('circuits/'+name+'.json'),actual))
    result={'status':'PASS','exact_local_identities':local,'source23_full_arithmetic_restoration':rows,
            'source17_full_arithmetic_restoration':rows17,
            'fixed_coefficient_bytes':615883,'native_coefficients_rebuilt':True,
            'retained_source_files_authenticated':len(pins['inputs']),
            'equations':results,'diagnostics':diagnostics(),
            'proof_boundary':'Finite exact algebra/data and literal-DAG checks. Does not prove inherited universal compiler/Pell calibration or an internal-ZFC biconditional.'}
    (ROOT/'certificates'/'VERIFIED.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'equations':results},indent=2))


if __name__=='__main__':main()
