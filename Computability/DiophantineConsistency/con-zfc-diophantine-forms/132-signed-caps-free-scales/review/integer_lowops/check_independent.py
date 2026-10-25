#!/usr/bin/env python3
"""Independent literal-polynomial audit, wave16. No producer modules imported.
Run with Python 3 + SymPy, normally and with -O. All checks are explicit raises.
This finite audit is not an end-to-end proof-assistant or consistency certificate.
"""
import argparse
import ast
from collections import Counter, defaultdict
import copy
import gzip
import hashlib
import itertools
import json
from pathlib import Path
import sys
import sympy as sy
from sympy.polys.rings import ring
from sympy.polys.domains import GF

BASE = Path(__file__).resolve().parents[2] / 'integer_lowops'
VARIABLES = 'j C z h r v w T c n s'.split()
PORTS = 'beta K0 MC MF cone_A cone_B'.split()
EXPECTED = {
    'product_main_guard11_native': (924, 109),
    'product_main_guard11_short': (840, 110),
}

RAW_PINS = {
    'beta': '6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
    'K0': '18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
    'MC': '3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
    'MF': '78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722',
    'cone_A': '66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615',
    'cone_B': '42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401',
}
MACHINE_PIN = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def equal(a, b, message):
    need(sy.expand(a - b) == 0, message)


def shape(packet):
    need(packet['schema'] == 'integer-polynomial-dag-v1', 'literal DAG schema')
    need(packet['domain'] == 'unrestricted integers', 'integer domain')
    need(packet['name'] in EXPECTED, 'approved family member')
    need(packet['variables'] == VARIABLES and packet['variable_count'] == 11, 'eleven coordinates')
    need(packet['coefficient_binding'] == 'coefficients/BINDING.json', 'fixed numeral binding path')
    need(packet['center'] == 'none', 'uncentered metadata')
    need(packet['short'] == packet['name'].endswith('_short'), 'index metadata')
    need(packet['free_y'] is False, 'original cubic scale metadata')
    rows = packet['nodes']
    for index, row in enumerate(rows):
        need(isinstance(row, list) and bool(row), 'node encoding')
        op = row[0]
        need(op in ('variable', 'coefficient', 'integer', 'add', 'sub', 'mul'), 'primitive opcode')
        if op in ('add', 'sub', 'mul'):
            need(len(row) == 3 and all(type(x) is int and 0 <= x < index for x in row[1:]), 'binary topological edge')
        else:
            need(len(row) == 2, 'leaf arity')
            if op == 'integer':
                need(type(row[1]) is int, 'integer literal')
    need([r[1] for r in rows if r[0] == 'variable'] == VARIABLES, 'coordinate leaves exactly once')
    need([r[1] for r in rows if r[0] == 'coefficient'] == PORTS, 'fixed coefficient leaves exactly once')
    need(type(packet['output']) is int and 0 <= packet['output'] < len(rows), 'output index')
    pending, live = [packet['output']], set()
    while pending:
        i = pending.pop()
        if i not in live:
            live.add(i)
            if rows[i][0] in ('add', 'sub', 'mul'):
                pending.extend(rows[i][1:])
    need(live == set(range(len(rows))), 'every node reachable from output')
    for key, i in packet['named_registers'].items():
        need(type(i) is int and 0 <= i < len(rows), 'valid register index ' + key)
    counts = Counter(r[0] for r in rows if r[0] in ('add', 'sub', 'mul'))
    need(dict(counts) == packet['operation_counts'], 'arithmetic count by opcode')
    need(sum(counts.values()) == packet['operations'] == EXPECTED[packet['name']][1], 'literal total cost')
    return {'node_count': len(rows), 'live_binary_operations': sum(counts.values()), 'operation_counts': dict(counts)}


def definitions(packet):
    # Independent transcription of the complete displayed low-operations equation.
    return [
        ('J','6*j+1'), ('qm','beta*J'), ('q','qm+1'), ('q2','q**2'), ('q3','q**3'),
        ('W','12*w+4'), ('X','q*W'), ('Y','(2*v+1)*q3'), ('E','X*Y'),
        ('a','E+Y'), ('H','4*a+3'), ('Delta','a**2+H'), ('A','a+2'),
        ('F','(K0+W)*C-z*qm'), ('R','(q*(q-F)-C)*(q2-1)+(MC+q*MF)*J'),
        ('q24','4*q2'), ('k','R+1+4*h*q**4' if packet['short'] else 'R+1+h*E'),
        ('Yk','Y*k'), ('eta','c-Yk'), ('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'),
        ('Budget','k**2*(q2-Derr)-q24*eta**2'), ('L','E*Yk'), ('Dt','1+L*(L+k)'),
        ('D4','12*Budget-16'), ('Pg','Dt*s'), ('P','Dt+D4*Pg**2'),
        ('c2','c**2'), ('Dm','1+Delta*c2'), ('BP','Dm*P'), ('U','A*r*c2'),
        ('UBP','U*BP'), ('strong','Delta*U*UBP'), ('Df','strong+1'),
        ('Q','Delta*strong'), ('delta','Q-1'), ('V','Df*(c-R+4*UBP*T)-c'),
        ('Cy','Q*V**2-1'), ('K','X*(3*c-2*X)+2'), ('H2','H**2'), ('H3','H**3'),
        ('zc','H*T+K'), ('zc2','zc**2'), ('Ac','(zc**2+3*H**2)*(zc**3-19*H**3)'),
        ('S','s*r*H'), ('Z','S*n-Ac'), ('output','delta*Z**2-S**2*BP*Df*Cy'),
    ]


def literal_identities(packet):
    rows = packet['nodes']
    registers = dict(packet['named_registers'])
    registers.update({r[1]: i for i, r in enumerate(rows) if r[0] in ('coefficient', 'variable')})
    registers['output'] = packet['output']
    covered, checked = set(), []
    spec = definitions(packet)
    need(set(packet['named_registers']) <= set(VARIABLES) | {k for k, _ in spec}, 'no unreviewed named abbreviation')
    for target, expression in spec:
        need(target in registers, 'missing specified register ' + target)
        names = sorted({x.id for x in ast.walk(ast.parse(expression, mode='eval')) if isinstance(x, ast.Name)})
        atoms = {n: sy.Symbol(n) for n in names}
        cuts = {registers[n]: atoms[n] for n in names}
        need(len(cuts) == len(names), 'distinct symbolic input cuts ' + target)
        memo = dict(cuts)
        def walk(i):
            covered.add(i)
            if i in memo:
                return memo[i]
            op, *args = rows[i]
            if op == 'integer':
                out = sy.Integer(args[0])
            else:
                need(op in ('add', 'sub', 'mul'), 'unbound input in ' + target)
                a, b = map(walk, args)
                out = a + b if op == 'add' else a - b if op == 'sub' else a * b
            memo[i] = out
            return out
        actual = walk(registers[target])
        expected = eval(expression, {'__builtins__': {}}, atoms)
        equal(actual, expected, 'literal identity: ' + target)
        checked.append(target)
    gates = {i for i, r in enumerate(rows) if r[0] in ('add', 'sub', 'mul')}
    need(gates <= covered, 'all gates covered by exact local polynomial identities')
    return {'exact_register_identities': checked, 'covered_gates': len(gates)}


def algebra():
    A,B,c,R,T,P = sy.symbols('A B c R T P')
    D = A*A-1
    dm = 1+D*c*c
    bp = dm*P
    U = A*B
    df = 1+D*U*U*bp
    Q = D*D*U*U*bp
    V = df*(c-R+4*U*bp*T)-c
    Da = (Q-1)*(Q*V*V-1)
    equal(sy.rem(df-1,bp,P),0,'Df=1 mod BP')
    equal(sy.rem(Da-1,bp,P),0,'Da=1 mod BP')
    equal(sy.rem(Da-A*A*dm,df,B),0,'Da=A^2 Dm mod Df')
    equal(sy.rem(df-1,A,A),0,'Df=1 mod A')
    equal(sy.rem(df-1,dm,c),0,'Df=1 mod Dm')
    need(all(((a*a-1)*a*a)%4 == 0 for a in range(4)), 'sign bootstrap residue')
    delta,Z,S,BP,Df,Cy,y = sy.symbols('delta Z S BP Df Cy y')
    output = delta*Z**2-S**2*BP*Df*Cy
    equal(delta*output,delta**2*Z**2-S**2*BP*Df*(delta*Cy),'product square clearing')
    equal(output.subs(Cy,delta*y*y),delta*(Z**2-S**2*BP*Df*y*y),'root-integral divisor recovery')
    U,p0,T = sy.symbols('U p0 T')
    equal((U*p0)*(p0*T),U*p0*p0*T,'rescaled auxiliary product')
    X,a,c = sy.symbols('X a c')
    equal((4*a+3)*X*c-2*(X*(X+2*a*c)-1),X*(3*c-2*X)+2,'short projector')
    t,H = sy.symbols('t H')
    equal((t*t+3*H*H)*(t**3-19*H**3),t**5+3*H*H*t**3-19*H**3*t*t-57*H**5,'quintic expansion')
    q,X,Y,k,s,r,c,T = sy.symbols('q X Y k s r c T')
    a=X*Y
    budget=-4*q*q*Y*Y*k*k
    dt=(X*Y*Y*k)**2
    guard=12*budget*dt**2*s*s
    dm=a*a*c*c; bp=dm*guard; U=a*r*c*c
    df=a*a*U*U*bp; Q=a*a*df; V=4*df*U*bp*T
    cy=Q*V*V; S=4*a*s*r
    top=-S*S*bp*df*cy
    claimed=2**36*3**7*q**14*X**64*Y**106*k**42*s**16*r**12*c**34*T*T
    equal(top,claimed,'complete highest homogeneous form')
    return {'coprimality_remainders':True,'sign_residue':True,'product_square_clearing':True,
            'rescaling_and_divisor_recovery':True,'projector':True,'quintic_expansion':True,
            'complete_top_form':True}


def payload_values(base, override=None):
    binding = json.loads((base/'coefficients/BINDING.json').read_text())
    need(binding['tuple'] == 'mixed-parity-unrounded-1064921', 'coefficient tuple identifier')
    need(binding['MF_convention'] == 'MF_native + beta, already shifted', 'MF shift convention')
    need(set(binding['payloads']) == set(PORTS), 'exact six-port binding')
    result, records = {}, {}
    for name in PORTS:
        b = binding['payloads'][name]
        need(b['file'] == name+'.bin.gz', 'payload basename')
        raw = gzip.decompress((base/'coefficients'/b['file']).read_bytes())
        if override and name in override:
            raw = override[name]
        value = int.from_bytes(raw, 'little')
        need(raw and raw[-1] != 0, 'minimal unsigned integer encoding')
        need(sha(raw) == RAW_PINS[name] == b['raw_sha256'], 'independently pinned payload '+name)
        need(len(raw) == b['raw_bytes'] and value.bit_length() == b['bits'], 'payload shape '+name)
        result[name] = value
        records[name] = {'sha256': sha(raw), 'bits': value.bit_length(), 'raw_bytes': len(raw)}
    return result, records


def reconstruct(base, values):
    # Rebuild tile ordering directly from pinned machine transitions, independently
    # of source34_builder.py, then re-derive all six actual integer coefficients.
    recipe = base/'coefficients/recipe'
    machine = (recipe/'k215.tm').read_bytes()
    need(sha(machine) == MACHINE_PIN, 'fixed machine bytes')
    transitions = []
    for line in machine.decode().splitlines():
        if line and not line.startswith('#'):
            q, bit, written, direction, target = line.split()
            transitions.append((int(q), int(bit), int(written), direction, int(target)))
    need(len(transitions) == 430 and len({(q,b) for q,b,_,_,_ in transitions}) == 430, 'complete transition table')
    right = sorted({a[4] for a in transitions if a[3] == 'R'})
    left = sorted({a[4] for a in transitions if a[3] == 'L'})
    need((len(right), len(left)) == (199,45), 'signal cardinalities')
    rr, ll = dict(zip(right,range(6,205))), dict(zip(left,range(205,250)))
    head = lambda q,b: 2*q+2+b
    tiles = set()
    for q,b,w,m,t in transitions:
        need(m in ('R','L'), 'transition direction')
        tiles.add((0,head(q,b),rr[t],w) if m == 'R' else (ll[t],head(q,b),0,w))
    for b in (0,1):
        tiles.update(((0,head(215,b),0,head(215,b)),(0,b,0,b)))
        tiles.update((rr[q],b,0,head(q,b)) for q in right)
        tiles.update((0,b,ll[q],head(q,b)) for q in left)
    tiles.update((0,a,0,438) for a in (0,1,432,433))
    tiles.update(((2,434,2,0),(2,435,3,1),(3,436,4,188),(4,436,4,0)))
    tiles.update((1,438,1,a) for a in (434,435,436))
    tiles.update((a,437,b,437) for a in (0,1,4) for b in (0,1,2))
    first, forbidden = (2,435,3,1),(5,0,0,0)
    tiles.add(forbidden)
    ordered = [first,forbidden] + sorted(tiles-{first,forbidden})
    need(len(ordered) == 943 and [list(t) for t in ordered] == json.loads((recipe/'wang943_tiles.json').read_text()), 'full machine-to-tile equality')
    weights = [1 << (10+2*j) for j in range(44)]
    codes = {}
    for i, tile in enumerate(ordered):
        codes[i] = 1+sum(weights[40:])+sum(weights[10*k+j] for k,edge in enumerate(tile) for j in range(10) if ((edge+512) >> j)&1)
    for k,start in enumerate((1020,1000,980,960)):
        for j in range(10):
            codes[start+2*j] = weights[10*k+j]
    for j,e in enumerate((1095,1096,2195,3296)):
        codes[e] = weights[40+j]
    codes[1063] = codes[1064] = 0
    need(len(codes) == 989, 'packing support')
    dc = defaultdict(int)
    for e in (40,41,1100,2200):
        dc[e] += 1
    for e, value in codes.items():
        for target in (4393,5495):
            dc[target-e] += value
    radix, length = 121,8801
    B = 1 << (radix*length)
    mu = 1022+sum(weights)
    native = 4+(mu << (radix*4393))+(mu << (radix*5495))
    for j in range(10):
        native += (1 << (radix*(1000+2*j)))+(1 << (radix*(1021+2*j)))
    native += (1 << (radix*2195))+(1 << (radix*3296))
    native += sum(((1 << 119)-1) << (radix*e) for e in range(8792,8799))
    native += ((1 << 27)-1) << (radix*8799)
    rebuilt = {'beta': B-1, 'K0': sum(v << (radix*e) for e,v in dc.items())+(B << radix),
               'MC': B-1-sum(1 << (radix*e) for e in codes if e != 1)-(2 << (radix*1063)),
               'MF': native+B-1, 'cone_A': 1 << 1113, 'cone_B': 1 << 666104}
    for key in PORTS:
        need(rebuilt[key] == values[key], 'machine-to-payload exact reconstruction '+key)
    need(values['beta']%6 == 1 and values['MC']%4 == 2 and native%8 == 4, 'authentic residue inputs')
    return {'machine_sha256': sha(machine), 'tile_count': len(ordered), 'support_size': len(codes),
            'all_six_integer_values_reconstructed': True, 'MF_shift_applied_exactly_once': True}


def degree_upper(packet):
    degrees=[]
    for row in packet['nodes']:
        op=row[0]
        if op in ('integer','coefficient'):
            value=0
        elif op=='variable':
            value=1
        else:
            a,b=[degrees[i] for i in row[1:]]
            value=a+b if op=='mul' else max(a,b)
        degrees.append(value)
    want=EXPECTED[packet['name']][0]
    need(degrees[packet['output']] == want == packet['exact_degree'] == packet['syntactic_degree_bound'], 'degree upper bound')
    named=packet['named_registers']
    return {'proved_upper_bound':want,'method':'ordinary gate degree propagation; no cancellation cut',
            'register_bounds':{k:degrees[i] for k,i in named.items()}}


def lower_and_dependence(packet, values):
    p = 65521
    need(sy.isprime(p), 'degree-certificate field prime')
    ring_t, t = ring('t', GF(p))
    evals = []
    for row in packet['nodes']:
        op = row[0]
        if op == 'integer':
            value = ring_t(row[1])
        elif op == 'coefficient':
            value = ring_t(values[row[1]] % p)
        elif op == 'variable':
            value = (VARIABLES.index(row[1])+1)*t
        else:
            a,b = [evals[k] for k in row[1:]]
            value = a+b if op == 'add' else a-b if op == 'sub' else a*b
        evals.append(value)
    final = evals[packet['output']]
    need(final.degree() == EXPECTED[packet['name']][0], 'attained degree at actual coefficients')
    # A nonzero partial derivative at a point modulo p proves actual dependence
    # on that coordinate over Z, rather than merely syntactic liveness.
    witnessed = {}
    for attempt in range(1,8):
        point = [(i+attempt+1)**2+3*attempt for i in range(11)]
        vals = []
        for row in packet['nodes']:
            op = row[0]
            if op == 'variable':
                j = VARIABLES.index(row[1]); value = point[j] % p; grad = [int(i == j) for i in range(11)]
            elif op in ('integer','coefficient'):
                value = (row[1] if op == 'integer' else values[row[1]]) % p; grad = [0]*11
            else:
                (a,da),(b,db) = [vals[k] for k in row[1:]]
                if op == 'mul': value,grad = a*b, [x*b+y*a for x,y in zip(da,db)]
                elif op == 'add': value,grad = a+b, [x+y for x,y in zip(da,db)]
                else: value,grad = a-b, [x-y for x,y in zip(da,db)]
            vals.append((value % p,[x % p for x in grad]))
        for name, derivative in zip(VARIABLES,vals[packet['output']][1]):
            if derivative and name not in witnessed:
                witnessed[name] = {'point':point,'partial_derivative_mod_prime':derivative}
        if len(witnessed) == 11:
            break
    need(set(witnessed) == set(VARIABLES), 'every coordinate is algebraically essential')
    return {'prime':p,'substitution':{v:(i+1) for i,v in enumerate(VARIABLES)},
            'specialized_degree':final.degree(),'nonzero_leading_coefficient_mod_prime':int(final.LC),
            'authenticated_coefficient_residues':{k:v % p for k,v in values.items()}, 'essential_coordinate_certificates':witnessed}


def source_pins(base):
    manifest = json.loads((base/'SOURCE_PINS.json').read_text())
    records = manifest['dependencies']
    for name,rec in records.items():
        path = Path(name)
        need(not path.is_absolute() and '..' not in path.parts, 'safe dependency path')
        data = (base/path).read_bytes()
        need(sha(data) == rec['sha256'] and len(data) == rec['bytes'], 'retained dependency '+name)
    return {'dependency_count':len(records),'manifest_sha256':sha((base/'SOURCE_PINS.json').read_bytes())}


def frozen_inputs(base):
    path = Path(__file__).resolve().parent/'FROZEN_INPUTS.json'
    need(path.exists(), 'reviewer-owned freeze inventory is present')
    freeze = json.loads(path.read_text())
    for name,rec in freeze['files'].items():
        data = (base/name).read_bytes()
        need(len(data) == rec['bytes'] and sha(data) == rec['sha256'], 'frozen audited input '+name)
    return {'inventory_sha256':sha(path.read_bytes()),'file_count':len(freeze['files']),
            'producer_manifest_sha256_at_freeze':freeze['producer_manifest_sha256_at_freeze']}


def reject(label, call, output):
    try:
        call()
    except (ValueError, KeyError, IndexError, TypeError, SyntaxError) as exc:
        output.append({'mutation':label,'rejected_by':str(exc)})
        return
    raise ValueError('mutation escaped detection: '+label)


def mutation_controls(packets, base):
    results = []
    for packet in packets:
        name = packet['name']
        for i,row in enumerate(packet['nodes']):
            if row[0] not in ('add','sub','mul'):
                continue
            mutant = copy.deepcopy(packet)
            mutant['nodes'][i][0] = 'sub' if row[0] != 'sub' else 'add'
            # Bypass count and snapshot checks: the exact symbolic layer itself
            # must reject a mutation at every one of the 219 arithmetic gates.
            reject(name+': opcode at gate '+str(i), lambda m=mutant: literal_identities(m), results)
        for register in ('q','Dm','Z'):
            mutant = copy.deepcopy(packet)
            mutant['named_registers'][register] = mutant['named_registers']['c']
            reject(name+': wrong register binding '+register, lambda m=mutant: literal_identities(m), results)
        mutant = copy.deepcopy(packet)
        mutant['nodes'][mutant['output']][1] = mutant['output']
        reject(name+': cycle', lambda: shape(mutant), results)
        mutant = copy.deepcopy(packet)
        mutant['exact_degree'] += 1
        reject(name+': false degree', lambda: degree_upper(mutant), results)
    for key in PORTS:
        raw = gzip.decompress((base/'coefficients'/(key+'.bin.gz')).read_bytes())
        changed = bytes([raw[0]^1])+raw[1:]
        reject('actual raw payload bit flip '+key, lambda k=key,r=changed: payload_values(base,{k:r}), results)
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, default=BASE)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    base = args.source.resolve()
    packets = [json.loads((base/(name+'.json')).read_text()) for name in EXPECTED]
    values,payload_receipt = payload_values(base)
    result = {'status':'PASS','python_optimized':not __debug__,'python':sys.version.split()[0], 'sympy':sy.__version__,
              'scope':'Finite exact algebra, all literal gates, authenticated coefficients, exact degrees, essential variables, negative controls; not an unbounded theorem certificate.',
              'coefficient_payloads':payload_receipt,'independent_coefficient_reconstruction':reconstruct(base,values),
              'algebra':algebra(),'retained_sources':source_pins(base),'frozen_inputs':frozen_inputs(base),'polynomials':[]}
    for packet in packets:
        result['polynomials'].append({'name':packet['name'],'sha256':sha((base/(packet['name']+'.json')).read_bytes()),
                                     'shape':shape(packet),'literal_symbolic_bindings':literal_identities(packet),
                                     'degree_upper':degree_upper(packet),'degree_lower_and_variables':lower_and_dependence(packet,values)})
    result['negative_controls'] = mutation_controls(packets,base)
    result['negative_control_count'] = len(result['negative_controls'])
    result['proof_sha256'] = sha((base/'PROOF.md').read_bytes())
    result['metrics_sha256'] = sha((base/'METRICS.json').read_bytes())
    rendered = json.dumps(result,indent=2)+'\n'
    if args.receipt:
        args.receipt.write_text(rendered)
    print(json.dumps({'status':'PASS','optimized':not __debug__,'polynomials':len(packets),'negative_controls':len(result['negative_controls'])}))

if __name__ == '__main__':
    main()
