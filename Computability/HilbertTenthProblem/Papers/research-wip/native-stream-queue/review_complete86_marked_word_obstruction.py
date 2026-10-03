"""Independent source and theorem-boundary review of the marked-word obstruction.

Reads authenticated bytes only. No author module or historical suite executes.
"""
import argparse
import ast
import hashlib
import json
import random
from fractions import Fraction
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run without -O')

SUBJECT = {
    'complete86_marked_word_obstruction.py': '68ce3fe9dd0eff4b70d66047f75048f15dfd49089a3a7221923fc178f3094686',
    'complete86_marked_word_obstruction.json': 'fdaa4713693f17560eefc56ce8c19738f682e9e82bde4c4a1ad5af7e98a90e73',
    'complete86_marked_word_obstruction.md': '86f3a8beb0cf83d2ff239475a9a2981dec6cbd7fb12577584d9ffb2ca5dd8c76',
}
PINS = {
    'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
    'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
    'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b',
    'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b',
    'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
    '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md': 'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d',
}
EXTRA_PROOF = {'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2'}
FACTORS = ['norm_first', 'norm_main', 'norm_input', 'norm_aux', 'norm_index', 'norm_transport', 'norm_strong', 'norm_linear']


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(',', ':'), allow_nan=False)


def auth(root, pins):
    result = {}
    for name, pin in pins.items():
        raw = (root / name).read_bytes()
        require(sha(raw) == pin, 'Authentication failed: ' + name)
        result[name] = raw
    return result


class P:
    """Small independent exact coefficient engine, used only at local cuts."""
    def __init__(self, value=0):
        if isinstance(value, P):
            self.c = value.c.copy()
        elif type(value) is dict:
            self.c = {m: v for m, v in value.items() if v}
        elif type(value) is str:
            self.c = {(value,): 1}
        else:
            self.c = {(): value} if value else {}

    def __add__(self, other):
        other = P(other)
        c = self.c.copy()
        for m, v in other.c.items():
            c[m] = c.get(m, 0) + v
        return P(c)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -v for m, v in self.c.items()})

    def __sub__(self, other):
        return self + (-P(other))

    def __rsub__(self, other):
        return P(other) - self

    def __mul__(self, other):
        c = {}
        for m, v in self.c.items():
            for n, w in P(other).c.items():
                key = tuple(sorted(m + n))
                c[key] = c.get(key, 0) + v*w
        return P(c)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        result = P(1)
        for _ in range(exponent):
            result = result*self
        return result

    def __eq__(self, other):
        return self.c == P(other).c


def local_identities():
    q, F, Z, ell, C, K, X, W, z = map(P, ['q', 'F', 'Z', 'ell', 'C', 'K', 'X', 'W', 'z'])
    alpha = q-F-Z-ell-C
    require(q-F-Z-alpha-ell == C, 'Full marked-coordinate inverse')
    require((q-1)*(q-F)+(q-F-Z) == q*(q-F)-Z, 'Actual shared-gap rewrite')
    nt = lambda cc, zz: (K+X)*cc+(q-F)-zz*(q-1)
    require(nt(Z+q*q*W, z+(K+X)*(q+1)*W) == nt(Z+W,z), 'Exact transport compensation')
    A, p, n = map(P, ['A', 'half_power', 'n'])
    require(2*A*(2*p)-4*p-p == (4*A-5)*p, 'Gamma inhomogeneous recurrence')
    gn, gm = map(P, ['gamma_n', 'gamma_previous'])
    require((2*A*gn-gm+p)-gn == (2*A-2)*gn+(gn-gm)+p, 'Gamma strict-difference identity')
    # The prospective recurrence n*A^(n-1) for psi, reduced modulo A^2-1.
    require(2*A*(n*A)-(n-1)-(n+1) == 2*n*(A*A-1), 'Odd-index congruence induction coefficient')
    require((A-2)**2+(4*A-5) == A*A-1, 'Actual discriminant identity')
    return 7


def ledger(rows, free):
    known = set(free)
    graph = {}
    dependencies = {x: {x} for x in free}
    require(len(known) == len(free), 'Distinct input ports')
    for row in rows:
        require(type(row) is list and len(row) == 4, 'Literal four-field row')
        name, op, a, b = row
        require(type(name) is str and name not in known and op in ['+', '-', '*'], 'Typed fresh gate')
        require(all(type(v) is int or type(v) is str and v in known for v in (a,b)), 'Source closure')
        graph[name] = [a,b]
        dependencies[name] = set().union(*(dependencies[v] if type(v) is str else set() for v in (a,b)))
        known.add(name)
    stack, live = ['polynomial'], set()
    while stack:
        node = stack.pop()
        if type(node) is int or node in live:
            continue
        live.add(node)
        stack.extend(graph.get(node, []))
    require(live == known, 'Complete source and every free coordinate live')
    m = sum(row[1] == '*' for row in rows)
    return {'M':m, 'A':len(rows)-m, 'operations':len(rows), 'witnesses':19, 'all_live':True}, dependencies


class DAG:
    def __init__(self):
        self.nodes = {}

    def intern(self, key):
        if key not in self.nodes:
            self.nodes[key] = len(self.nodes)
        return self.nodes[key]

    def atom(self, name):
        return self.intern(('input',name))

    def literal(self, value):
        return self.intern(('literal',value))

    def op(self, op, a, b):
        if op in ['+', '*'] and a > b:
            a,b = b,a
        return self.intern((op,a,b))


def dag_proof(old, candidate, free):
    dag = DAG()
    child_inputs = {x:dag.atom(x) for x in free}
    def run(rows, parent=False):
        env = dict(child_inputs)
        get = lambda x: env[x] if type(x) is str else dag.literal(x)
        if parent:
            q = dag.op('+',dag.op('*',get('Bm1'),get('Jrep')),dag.literal(1))
            alpha = dag.op('-',dag.op('-',q,get('F')),get('Z'))
            alpha = dag.op('-',alpha,dag.op('*',get('twice_cell_bits'),get('x')))
            env['alpha'] = dag.op('-',alpha,get('C_word'))
        for name, op, a, b in rows:
            env[name] = dag.op(op,get(a),get(b))
            if name == 'marked_rhs':
                # Independent coefficient identity discharges the full inverse cone.
                require(parent, 'Marked cut belongs to the restored parent')
                env[name] = get('C_word')
            elif name == 'gap':
                # Independent identity uses literal q=repunit+1 in every source.
                env[name] = dag.op('-',dag.op('*',get('q'),get('q_minus_F')),get('Z'))
        return env
    before, after = run(old, True), run(candidate)
    common = sorted((set(before)&set(after))-set(free)-{'alpha','gap_product'})
    require(all(before[n] == after[n] for n in common), 'All retained downstream DAGs agree')
    require(all(before[n] == after[n] for n in FACTORS+['polynomial']), 'Every factor and the entire product agree')
    return len(common), len(FACTORS), 1


def eval_source(rows, values):
    env = dict(values)
    for name, op, a, b in rows:
        av = env[a] if type(a) is str else a
        bv = env[b] if type(b) is str else b
        if op == '*':
            env[name] = av*bv
        elif op == '+':
            env[name] = av+bv
        elif op == '-':
            env[name] = av-bv
        else:
            raise AssertionError('Unknown gate')
    return env


def pell_components():
    # Independent first-order multiplication in Z[sqrt(A^2-1)].
    cases, recurrence_checks, congruences = [], 0, 0
    for A in [3,6,11]:
        Delta, H, a = A*A-1, 4*A-5, A-2
        for t in [4,5,6]:
            q, e = 2**t, 3
            R = q*q+3
            shifted = e+2*t
            require(e < t and shifted < 3*t < q*q < R, 'Complete numerical width margins')
            pair = (1,0)
            gs = [0]
            selected = {}
            previous_gamma = 0
            for index in range(1,R+1):
                chi,psi = pair
                pair = (A*chi+Delta*psi,chi+A*psi)
                chi,psi = pair
                gamma, rem = divmod(chi-a*psi-2**index,H)
                require(rem == 0, 'Gamma integral from independent Pell multiplication')
                if index == 1:
                    require(gamma == 0, 'Gamma initial value')
                else:
                    require(gamma == 2*A*previous_gamma-gs[-2]+2**(index-2), 'Exact gamma recurrence')
                    require(gamma > previous_gamma, 'Strict gamma growth from index two')
                    recurrence_checks += 1
                gs.append(gamma)
                previous_gamma = gamma
                if index % 2:
                    require((psi-index)%Delta == 0, 'Odd-index psi congruence')
                    congruences += 1
                if index in [e, shifted, R]:
                    selected[index] = (chi,psi,gamma)
            main,c,main_gamma = selected[R]
            for n in [e,shifted]:
                mu,kappa,rho = selected[n]
                delta, rem = divmod(kappa-n,Delta)
                sigma = main_gamma-rho
                require(rem == 0 and min(delta,rho,sigma) > 0, 'All replacement input witnesses positive')
                require((2**n+a*(n+delta*Delta)+rho*H)**2-Delta*(n+delta*Delta)**2 == 1, 'Actual input norm equals one')
                require(2**R+a*c+(rho+sigma)*H == main, 'Actual main root fixed')
            require(2**shifted == q*q*2**e, 'Correct whole-width shift')
            cases.append({'A':A,'t':t,'R':R,'old_exponent':e,'new_exponent':shifted,
                          'main_bits':main.bit_length(),'scope':'Pell/width components; no compiler masks or auxiliary tower instantiated'})
    return cases, recurrence_checks, congruences


def verify(root, subject_root):
    root, subject_root = Path(root), Path(subject_root)
    subject = auth(subject_root,SUBJECT)
    dependencies = auth(root,PINS)
    auth(root,EXTRA_PROOF)
    author = json.loads(subject['complete86_marked_word_obstruction.json'])
    syntax = ast.parse(subject['complete86_marked_word_obstruction.py'])
    source_pins = [ast.literal_eval(n.value) for n in syntax.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='PINS' for t in n.targets)]
    require(source_pins == [PINS] and author['pins'] == PINS, 'Author source/receipt pin agreement')
    require(author['source_sha256'] == SUBJECT['complete86_marked_word_obstruction.py'], 'Author receipt source lineage')
    parent = json.loads(dependencies['complete86_factored_first_root.json'])['forms'][0]
    require(parent['normalized'] is True and parent['output'] == 'polynomial', 'Actual complete normalized form')
    old = parent['source']
    defs = {row[0]:row[1:] for row in old}
    expected_cuts = {
        'q':['+','repunit',1], 'q_minus_F':['-','q','F'],
        'q_minus_FZ':['-','q_minus_F','Z'], 'C_after_alpha':['-','q_minus_FZ','alpha'],
        'scaled_t':['*','twice_cell_bits','x'], 'marked_rhs':['-','C_after_alpha','scaled_t'],
        'gap_product':['*','repunit','q_minus_F'], 'gap':['+','gap_product','q_minus_FZ'],
        'gamma_sum':['+','rho','sigma'], 'gam':['*','gamma_sum','a4m5'], 'R14':['+','D1','gam'],
        'W':['-','marked_rhs','Z'], 'odd_index':['+','scaled_t','inner_bits'],
        'index_product':['*','delta','A'], 'index_rhs':['+','odd_index','index_product'],
        'difference_multiple':['*','index_rhs','R12'], 'exponent_partial':['+','W','difference_multiple'],
        'modulus_multiple':['*','rho','a4m5'], 'exponent_rhs':['+','exponent_partial','modulus_multiple'],
        'kinner':['+','Kconstant','wn2'], 'innerC':['*','kinner','marked_rhs'],
        'transport_partial':['+','innerC','q_minus_F'], 'local_rhs':['*','zplus','repunit'],
        'norm_transport':['-','transport_partial','local_rhs'],
    }
    require(all(defs[n] == row for n,row in expected_cuts.items()), 'All literal coordinate/input/transport cuts')
    consumers = lambda port:[row[0] for row in old if port in row[2:]]
    require(consumers('alpha') == ['C_after_alpha'], 'Private alpha')
    require(consumers('C_after_alpha') == ['marked_rhs'], 'Private marked bound')
    require(consumers('q_minus_FZ') == ['C_after_alpha','gap'], 'Exact gap-sharing closure')
    witnesses = ['C_word' if w == 'alpha' else w for w in parent['witnesses']]
    free = witnesses+['x']+parent['ledger']['fixed_numerals']
    require(len(witnesses)==19 and author['witnesses']==witnesses and author['free']==free, 'Complete coordinate and numeral preservation')
    forms = []
    for count in [84,83]:
        rows = []
        for name,op,a,b in old:
            if name in ['C_after_alpha','marked_rhs'] or count == 83 and name == 'q_minus_FZ':
                continue
            a = 'C_word' if a == 'marked_rhs' else a
            b = 'C_word' if b == 'marked_rhs' else b
            if count == 83 and name == 'gap_product':
                a,b = 'q','q_minus_F'
            if count == 83 and name == 'gap':
                op,a,b = '-','gap_product','Z'
            rows.append([name,op,a,b])
        forms.append(rows)
    require([r['source'] for r in author['forms']] == forms, 'Entire saved circuits reconstructed')
    old_ledger, olddeps = ledger(old,parent['witnesses']+['x']+parent['ledger']['fixed_numerals'])
    require((old_ledger['M'],old_ledger['A'])==(48,38), 'Literal baseline86')
    identity_count = local_identities()
    reviewed = []
    for i,rows in enumerate(forms):
        counts,deps = ledger(rows,free)
        require((counts['M'],counts['A']) == (48,36-i), 'Every complete paid gate recounted')
        require({k:counts[k] for k in ['M','A','operations','all_live']} == author['forms'][i]['ledger'], 'Saved complete ledger')
        common,factors,outputs = dag_proof(old,rows,free)
        # Five source factors are independent of every replaced supplied input.
        changed = {'x','C_word','zplus','delta','rho','sigma'}
        unchanged = ['norm_first','norm_aux','norm_index','norm_strong','norm_linear']
        require(all(not deps[f]&changed for f in unchanged), 'Unchanged five factors during semantic shift')
        require(deps['norm_main']&changed == {'rho','sigma'}, 'Main factor depends only on preserved quotient sum')
        # Finalizer is checked literally, in addition to its DAG identity.
        final_rows = [[n,op,a,b] for n,op,a,b in old if n in ['norm_pair','norm_triple','norm_four','norm_product','all_units','seven_units','eight_units','polynomial']]
        require(all(r in rows for r in final_rows) and len(final_rows)==8, 'Seven paid factor products and final subtraction unchanged')
        reviewed.append({'ledger':counts,'source_sha256':sha(canonical(rows).encode()),'common_DAG_registers':common,'factor_DAG_equalities':factors,'whole_output_DAG_equalities':outputs,'unaffected_shift_factors':unchanged})
    rng = random.Random(83310061)
    numeric = rational = signed = 0
    for i in range(32):
        values = {n:rng.randint(-4,5) for n in free}
        if i >= 24:
            values = {n:Fraction(v,5) for n,v in values.items()}
            rational += 2
        signed += 2
        original = {n:v for n,v in values.items() if n != 'C_word'}
        original['alpha'] = values['Bm1']*values['Jrep']+1-values['F']-values['Z']-values['twice_cell_bits']*values['x']-values['C_word']
        before = eval_source(old,original)
        for rows in forms:
            after = eval_source(rows,values)
            require(before['marked_rhs'] == values['C_word'], 'Full numerical inverse')
            require(all(before[f] == after[f] for f in FACTORS+['polynomial']), 'Independent complete signed evaluation')
            numeric += 1
    widths = 0
    for d in range(4,13):
        for N in range(1,13):
            for x in range(1,7):
                for b in [3,5,7,9]:
                    t,e = d*N,2*d*x+b
                    if e >= t:
                        continue
                    q,W = 2**t,2**e
                    ep = 2*d*(x+N)+b
                    require(ep == e+2*t and ep < 3*t < q*q, 'Ordinary input/width arithmetic')
                    require(q-1-2-2*d*(x+N)-q*q*W < 0, 'Inverse slack already negative at minimal F=Z=1')
                    widths += 1
    components, gamma_checks, congruences = pell_components()
    require(author['counts'] == {'exact_cut_identities':2,'whole_source_graph_comparisons':96,'exact_transport_identities':1,'input_shift_components':4}, 'Author evidence counts accurately scoped')
    return {
        'status':'PASS_INDEPENDENT_MARKED_WORD_OBSTRUCTION_REVIEW',
        'review_source_sha256':sha(Path(__file__).read_bytes()),'subject_pins':SUBJECT,'dependency_pins':PINS,'additional_proof_pin':EXTRA_PROOF,
        'baseline_ledger':old_ledger,'reviewed_forms':reviewed,
        'counts':{'independent_local_coefficient_identities':identity_count,'full_numeric_identities':numeric,'signed_numeric_identities':signed,'rational_numeric_identities':rational,'fixed_program_width_checks':widths,'input_main_components':len(components),'gamma_recurrence_and_growth_steps':gamma_checks,'odd_index_congruences':congruences},
        'input_main_components':components,
        'proof_review':{
            'ordinary_input_shift':'x -> x+N with identical program constants and q; e -> e+2*d*N',
            'strict_margin':'e<t implies e+2t<3t<q^2<=R',
            'canonical_chain':'raw complete accepting certificate; normalized canonical auxiliary reconstruction; positive asymmetric w_new=q^2*w_old; positive first root T=L+g',
            'new_positive_inputs':['C_word=Z+q^2*W','zplus_new=zplus+(K+X)*(q+1)*W','delta_new=(psi_A(e+2t)-(e+2t))/Delta','rho_new=gamma_(e+2t)','sigma_new=gamma_R-gamma_(e+2t)'],
            'unchanged_auxiliary_tower':True,'inverse_alpha_strictly_negative':True,
            'false_input_scope':'The same valid fixed singleton compiler S={1} has a child zero at 1+N, N>0.',
            'no_full_compiler_zero_materialized':True,
            'not_claimed':['all inputs accepted','all 83-operation representations impossible','standalone child universality','maintained public compiler API','independent historical suite replay']},
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',required=True,type=Path)
    p.add_argument('--subject-root',type=Path,default=Path(__file__).resolve().parent)
    p.add_argument('--output',type=Path)
    p.add_argument('--expect',type=Path)
    a = p.parse_args()
    result = verify(a.root,a.subject_root)
    if a.expect:
        require(canonical(result)==canonical(json.loads(a.expect.read_text())), 'Exact type-sensitive saved receipt')
    if a.output:
        a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(result['status'],result['counts'])


if __name__ == '__main__':
    main()
