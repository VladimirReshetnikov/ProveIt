#!/usr/bin/env python3
"""Build factored ordinary integer polynomials; no source code is executed.

The only imported upstream objects are inert JSON packets. Fixed powers use
ordinary polynomial multiplication. Explanatory registers never add witnesses.
"""
from pathlib import Path
import ast, copy, hashlib, json, sys
sys.setrecursionlimit(20000)

ROOT = Path(__file__).resolve().parent

def require(ok, message):
    if not ok:
        raise ValueError(message)

def read(path):
    return json.loads(path.read_text())

def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def expanded(expression, definitions):
    active = set()
    memo = {}
    def visit(n):
        if isinstance(n, ast.Name) and n.id in definitions:
            key = n.id
            require(key not in active, 'acyclic definitions')
            if key not in memo:
                active.add(key)
                memo[key] = visit(ast.parse(definitions[key], mode='eval').body)
                active.remove(key)
            return copy.deepcopy(memo[key])
        if isinstance(n, ast.Name):
            return n
        if isinstance(n, ast.Constant):
            require(type(n.value) is int, 'integer leaves')
            return n
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub):
            n.operand = visit(n.operand)
            return n
        if isinstance(n, ast.BinOp) and isinstance(n.op, (ast.Add, ast.Sub, ast.Mult, ast.Pow)):
            if isinstance(n.op, ast.Pow):
                require(isinstance(n.right, ast.Constant) and type(n.right.value) is int and 0 <= n.right.value <= 256,
                        'fixed nonnegative powers')
            n.left = visit(n.left)
            n.right = visit(n.right)
            return n
        raise ValueError('disallowed syntax ' + ast.dump(n))
    return ast.unparse(ast.fix_missing_locations(visit(ast.parse(expression, mode='eval').body)))

def substitute(expression, replacements):
    class Sub(ast.NodeTransformer):
        def visit_Name(self, node):
            return ast.parse(replacements[node.id], mode='eval').body if node.id in replacements else node
    return ast.unparse(ast.fix_missing_locations(Sub().visit(ast.parse(expression, mode='eval').body)))

def build():
    pins = read(ROOT/'SOURCE_PINS.json')
    for record in pins['files']:
        require(hashlib.sha256((ROOT/record['stored_path']).read_bytes()).hexdigest() == record['sha256'],
                'upstream source hash ' + record['stored_path'])
    q = 'beta*(3*J3+1)+1'
    W = '4*(3*w3+1)'
    F = f'(K0+({W}))*C-z*(({q})-1)'
    alpha = f'({q})-({F})-C'
    replacements = {'F': F, 'alpha': alpha}
    outputs = []
    for n, degree in [(22,16),(21,20),(20,32),(19,88)]:
        name = f'joint{n}_degree{degree}'
        source_path = ROOT/'upstream'/('joint__'+name+'.json')
        source = read(source_path)
        variables = ['C' if v == 'alpha' else v for v in source['variables'] if v != 'F']
        # All supplied packets retain exactly one literal transport row.
        candidate_indices = [i for i, row in enumerate(source['residuals']) if 'K0' in row]
        require(len(candidate_indices) == 1, 'unique monic transport row')
        deleted = candidate_indices[0]
        rows = [substitute(row, replacements) for i,row in enumerate(source['residuals']) if i != deleted]
        packet = {
            'name':f'pivot{n-1}_degree{degree}',
            'domain':'unrestricted integers',
            'variables':variables,
            'variable_count':len(variables),
            'fixed_numerals':source['fixed_numerals'],
            'coefficient_binding':'../coefficients/BINDING.json',
            'residuals':rows,
            'residual_count':len(rows),
            'single_equation':'sum of squares of all residuals',
            'exact_degree':degree,
            'degree_witness':source['degree_witness'],
            'parent':str(source_path.relative_to(ROOT)),
            'parent_sha256':hashlib.sha256(source_path.read_bytes()).hexdigest(),
            'deleted_parent_row_zero_based':deleted,
            'parent_restoration':replacements,
            'proof_status':'New elementary zero-set isomorphism; inherited native/Pell/calibration theorem remains explicit.',
        }
        write(ROOT/'forms'/(packet['name']+'.json'),packet)
        outputs.append(packet)

    base = outputs[-1]
    definitions = {
        'J':'3*J3+1',
        'q':'beta*J+1',
        'W':'4*(3*w3+1)',
        'X':'q*W',
        'Y':'(2*v_scale+1)*q**3',
        'E':'X*Y',
        'a':'(X+1)*Y',
        'H':'4*a+3',
        'Delta':'a**2+H',
        'V':'f*o-c',
        'k':'1-V+j*c+h*E',
        'eta':'c-Y*k',
        'u':'E*Y*k',
        'A':'u*(u+k)+1',
        'F':'(K0+W)*C-z*(q-1)',
        'alpha':'q-F-C',
        'I':'(2*r+1)*c**2',
        'Q':'I**2',
        'delta':'Q-1',
        'R':'(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*J',
        'det':'(cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)**2',
        'T':'eta*(k-eta)',
        'pos':'1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)',
        'G':'det*T-(pair_root**2-det-T+1)**2-pos',
    }
    compact = [
        'tau**2-A',
        '(X+a*c+gamma*H)**2-Delta*c**2-1',
        'c*j-V-R',
        'Q-Delta*(f**2-1)',
        'Q*(V**2-y**2)+y**2-1',
        'G',
    ]
    write(ROOT/'certificates'/'COMPACT_BASE18.json',{'definitions':definitions,'rows':compact,
            'inlined_rows':[expanded(r,definitions) for r in compact],
            'compare_to':'forms/pivot18_degree88.json'})

    # Fraction-free midpoint centering. The new equation itself recovers parity.
    midpoint = 'tau_center**2+2*(2*u+k)*tau_center+k**2-4'
    midpoint_rows = [midpoint]+compact[1:]
    midvars = ['tau_center' if v == 'tau' else v for v in base['variables']]
    mid = {
        'name':'center18_degree80', 'domain':'unrestricted integers',
        'variables':midvars, 'variable_count':len(midvars),
        'fixed_numerals':base['fixed_numerals'], 'coefficient_binding':'../coefficients/BINDING.json',
        'definitions':definitions,
        'compact_residuals':midpoint_rows,
        'residuals':[expanded(r,definitions) for r in midpoint_rows],
        'residual_count':len(midpoint_rows),
        'single_equation':'(1+G)*(1+S)-1, where G is the last residual and S is the sum of squares of all other residuals',
        'exact_degree':80,
        'degree_witness':{'monomial':'h**6*w3**8*v_scale**14*J3**50*tau_center**2',
                          'coefficient_expression':'-2**34*3**58*beta**50'},
        'parent':'forms/pivot18_degree88.json',
        'root_change':{'forward':'tau_center=2*tau-2*u-k',
                       'inverse':'tau=(tau_center+2*u+k)/2; numerator even at every new zero'},
        'proof_status':'Ordinary arithmetic proof plus inherited source theorem; no new proof-assistant certificate.',
    }
    write(ROOT/'forms'/'center18_degree80.json',mid)
    outputs.append(mid)

    # Eliminate the first and auxiliary Pell roots using one centered sum.
    normdefs = dict(definitions)
    normdefs.update({
        'Bnum':'Q*V**2-1',
        'center':'root_sum**2+2*I*(2*u+k)*root_sum+Q*(k**2-4)',
        'norm_inner':'delta*center-4*Bnum',
        'N':'norm_inner**2-64*delta*Q*A*Bnum',
    })
    normrows = [compact[1],compact[2],compact[3],compact[5],'N']
    normvars = [v for v in base['variables'] if v not in ('tau','y')]+['root_sum']
    norm = {
        'name':'norm17_degree112', 'domain':'unrestricted integers',
        'variables':normvars, 'variable_count':len(normvars),
        'fixed_numerals':base['fixed_numerals'], 'coefficient_binding':'../coefficients/BINDING.json',
        'definitions':normdefs,
        'compact_residuals':normrows,
        'residuals':[expanded(r,normdefs) for r in normrows],
        'residual_count':len(normrows),
        'single_equation':'sum of squares of all residuals',
        'exact_degree':112,
        'degree_witness':{'monomial':'r**12*c**24*h**4*f**4*o**4*J3**44*w3**8*v_scale**12',
                          'coefficient_expression':'2**52*3**52*beta**44'},
        'parent':'forms/pivot18_degree88.json',
        'forward_map':'root_sum=2*(I*tau+y)-I*(2*u+k)',
        'reverse_map':'Recover signed rational roots from the two-root norm; rational-square integrality and adjacent-coefficient Pell descent make tau and y integers.',
        'proof_status':'New ordinary proof using a proved denominator descent; inherits the explicitly stated native/Pell/calibration theorem, without a new proof-assistant certificate.',
    }
    write(ROOT/'forms'/'norm17_degree112.json',norm)
    outputs.append(norm)
    # A secondary operation/degree tradeoff: center the auxiliary root at V.
    # N110 is exactly N112(root_sum+2V), written after its leading cancellation.
    doubledefs=dict(normdefs)
    doubledefs.update({
        'Jtail':'delta*(center+4*V*root_sum)-4*(V**2-1)',
        'Htail':'4*delta*I*(2*u+k)*V',
        'N110':'Jtail**2+2*Jtail*Htail+64*delta*Q*A*(1-V**2)+16*delta**2*Q*(k**2-4)*V**2',
    })
    doublerows=normrows[:-1]+['N110']
    double=dict(norm)
    double.update({
        'name':'norm17_degree110','definitions':doubledefs,'compact_residuals':doublerows,
        'residuals':[expanded(r,doubledefs) for r in doublerows],'exact_degree':110,
        'degree_witness':{'monomial':'r**12*c**24*h**4*f**2*o**2*root_sum**2*J3**44*w3**8*v_scale**12',
                          'coefficient_expression':'2**52*3**52*beta**44'},
        'parent':'forms/norm17_degree112.json',
        'forward_map':'root_sum_new=root_sum_old-2*V',
        'reverse_map':'root_sum_old=root_sum_new+2*V; integer-polynomial coordinate shear',
        'status':'Secondary degree/circuit-size tradeoff; degree112 remains the simpler supplied root-merger circuit.',
    })
    write(ROOT/'forms'/'norm17_degree110.json',double)
    outputs.append(double)
    write(ROOT/'certificates'/'BUILD.json',{'packets':[{'name':p['name'],'variables':p['variable_count'],
              'rows':p['residual_count'],'degree':p['exact_degree']} for p in outputs]})
    print(json.dumps(read(ROOT/'certificates'/'BUILD.json'),indent=2))

if __name__=='__main__':
    build()
