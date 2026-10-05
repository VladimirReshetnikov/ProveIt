"""Original metadata-only full-source composition of the integer-plane cut.

Read pinned graphs as inert rows. No arithmetic/coefficients/degrees evaluated.
Freeze after this original emission; do not execute or import afterward.
"""
import hashlib
import json
from collections import Counter
from pathlib import Path

BASE = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PARENT = BASE / 'positive7_inverse_pair_compose_root.json'
PARENT_PIN = '182a9dc7a2efe4428a096263c1872bfbb5df264a79b50851de0b7b7c82b6a4f1'
LOCAL = BASE / 'positive7_inverse_pair_action_pascal.json'
LOCAL_PIN = 'b830a0644ae0b5ba8b04273a3ac445437af0af2c0b522c1caf3078203f7eab02'
PROOF = Path('/tmp/positive7_relator_plane_action_pascal.md')
PROOF_PIN = '374736feae3677e61a7e7676847d199956cef7a5664d1f83f5f57dc739ea3819'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_pinned(path, pin, parsed=True):
    raw = path.read_bytes()
    if sha(raw) != pin:
        raise ValueError('input changed: '+str(path))
    info = {'path':str(path),'sha256':pin,'bytes':len(raw)}
    return (json.loads(raw) if parsed else None), info


def counts(rows):
    ops = Counter(row[1] for row in rows)
    return {'M':ops['*'],'A':ops['+']+ops['-'],'operations':len(rows)}


def row_pin(rows):
    return sha(json.dumps(rows,separators=(',',':')).encode())


def inspect(rows, supplied, final):
    known = set(supplied)
    if len(known) != len(supplied):
        raise ValueError('duplicate supplied name')
    edges, roles = {}, set()
    for name,op,a,b in rows:
        if name in known or op not in ('+','-','*'):
            raise ValueError('invalid definition')
        for value in (a,b):
            if isinstance(value,str):
                if value not in known:
                    raise ValueError('undefined operand '+value)
            elif isinstance(value,dict):
                if set(value) != {'fixed'}:
                    raise ValueError('untyped role')
                roles.add(value['fixed'])
            elif not isinstance(value,int):
                raise ValueError('untyped literal')
        known.add(name)
        edges[name] = (a,b)
    live, pending = set(), [final]
    while pending:
        value = pending.pop()
        if isinstance(value,str) and value not in live:
            live.add(value)
            pending.extend(edges.get(value,()))
    if set(edges)-live or set(supplied)-live:
        raise ValueError('dead row or supplied name')
    return {'all_rows_live':True,'all_supplied_live':True,'topologically_closed':True,
            'named_fixed_roles':sorted(roles)}


def plane_append(index, permutation, accumulators):
    if sorted(permutation) != [0,1,2]:
        raise ValueError('not a fixed three-coordinate permutation')
    rows = []
    tag = 'plane_'+str(index)+'_'
    inputs = ['selected_'+str(slot)+'_'+str(port)
              for slot in (8+2*index,9+2*index) for port in (4,5,6,7)]

    def put(name,op,left,right):
        name = tag+name
        rows.append([name,op,left,right])
        return name

    def role(name):
        return {'fixed':tag+name}

    forms = []
    for label in ('alpha','beta'):
        terms = [put(label+'_term_'+str(j),'*',role(label+'_'+str(j)),field)
                 for j,field in enumerate(inputs)]
        value = terms[0]
        for j,term in enumerate(terms[1:],1):
            value = put(label+'_sum_'+str(j),'+',value,term)
        forms.append(value)
    A,B = forms
    X1 = put('X1','*',role('u1'),A)
    X2 = put('X2','*',role('v1'),B)
    Y1 = put('Y1','*',role('u2'),A)
    Y2 = put('Y2','*',role('v2'),B)
    Z = put('Z','*',role('v3'),B)
    X = put('X','+',X1,X2)
    Y = put('Y','+',Y1,Y2)
    updated = list(accumulators)
    for chart_coordinate,increment in enumerate((X,Y,Z)):
        original_coordinate = permutation[chart_coordinate]
        updated[original_coordinate] = put('append_'+str(original_coordinate),'+',
                                          accumulators[original_coordinate],increment)
    if counts(rows) != {'M':21,'A':19,'operations':40}:
        raise ValueError('wrong plane append census')
    return rows,updated,{'relator_index':index,'raw_inputs':inputs,
                         'permuted_row_original_indices':permutation,
                         'accumulators_before':accumulators,'accumulators_after':updated,
                         'dot_product_outputs':forms,'chart_outputs':[X,Y,Z],
                         'ledger':counts(rows),'source_sha256_compact':row_pin(rows)}


def compose(parent, local, permutations):
    r = parent['r']
    if len(permutations) != r:
        raise ValueError('missing fixed permutation')
    old = parent['source']
    begin = parent['substitution']['old_cut_first_index']
    end = next(i for i,row in enumerate(old) if row[0]=='five_increment_sum_1')
    if old[begin:begin+198] != local['source']:
        raise ValueError('paired cut mismatch')
    removed = old[begin+198:end]
    if any(not row[0].startswith(('relator_term_','paired_relator_sum_')) for row in removed):
        raise ValueError('unexpected removed row')
    if counts(removed) != {'M':24*r,'A':24*r,'operations':48*r}:
        raise ValueError('wrong old relator cost')
    replacements, append_metadata = [], []
    accumulators = local['outputs'][3:]
    for index,permutation in enumerate(permutations):
        rows,accumulators,metadata = plane_append(index,permutation,accumulators)
        replacements += rows
        append_metadata.append(metadata)
    outputs = local['outputs'][:3]+accumulators
    binding = dict(zip(parent['ports']['six_increments'],outputs))
    rename = lambda value: binding.get(value,value) if isinstance(value,str) else value
    suffix = [[name,op,rename(a),rename(b)] for name,op,a,b in old[end:]]
    rows = old[:begin+198]+replacements+suffix
    result = dict(parent)
    result['source'] = rows
    result['ports'] = dict(parent['ports'],six_increments=outputs)
    result['certificate_prefix_rows'] = parent['certificate_prefix_rows']-8*r
    result['certificate_ledger'] = counts(rows[:result['certificate_prefix_rows']])
    result['polynomial_ledger'] = counts(rows)
    result['stages'] = dict(parent['stages'],sparse_increment_rows=counts(local['source']+replacements))
    result['static_checks'] = inspect(rows,parent['ordinary_parameters']+parent['positive_auxiliaries'],parent['output'])
    roles = result['static_checks']['named_fixed_roles']
    if len(roles) != 4+21*r or any(name.startswith('relator_delta_') for name in roles):
        raise ValueError('wrong fixed role set')
    expected = {'M':parent['certificate_ledger']['M']-3*r,
                'A':parent['certificate_ledger']['A']-5*r,
                'operations':parent['certificate_ledger']['operations']-8*r}
    if result['certificate_ledger'] != expected:
        raise ValueError('whole certificate delta')
    result['substitution'] = {'parent_source_sha256_compact':row_pin(old),
                             'new_source_sha256_compact':row_pin(rows),
                             'old_relator_cut_zero_based':[begin+198,end],
                             'new_relator_cut_zero_based':[begin+198,begin+198+40*r],
                             'old_relator_ledger':counts(removed),'new_relator_ledger':counts(replacements),
                             'six_boundary_bindings':binding,
                             'all_prefix_and_paired_rows_identical':rows[:begin+198]==old[:begin+198],
                             'suffix_only_rebinds_boundary':rows[begin+198+40*r:]==suffix,
                             'relator_appends':append_metadata,
                             'formal_permutation_scope':'Static chart choices; coefficient recipe must choose each normal and row permutation consistently. Not a numerical universal instance.'}
    return result


def main():
    parent,parent_info = read_pinned(PARENT,PARENT_PIN)
    local,local_info = read_pinned(LOCAL,LOCAL_PIN)
    _,proof_info = read_pinned(PROOF,PROOF_PIN,False)
    charts = {0:[],1:[[2,0,1]],4:[[0,1,2],[1,0,2],[2,0,1],[0,2,1]]}
    examples = [compose(graph,local,charts[graph['r']]) for graph in parent['examples']]
    censuses = []
    for record in parent['static_shape_censuses']:
        new = dict(record)
        for key in ('certificate_ledger','polynomial_ledger'):
            old = record[key]
            new[key] = {'M':old['M']-3*record['r'],'A':old['A']-5*record['r'],
                        'operations':old['operations']-8*record['r']}
        censuses.append(new)
    result = {
        'status':'original metadata-only integral-plane composition PASS',
        'emitter_sha256':sha(Path(__file__).read_bytes()),'inputs':[parent_info,local_info,proof_info],
        'generic_ledger':{'certificate':'(276+53r+lambda)M+(550+69r)A',
                          'polynomial':'(299+53r+lambda)M+(595+69r)A',
                          'polynomial_operations':'894+122r+lambda(62+10r)',
                          'comparisons':23,'positive_witnesses':'96+10r',
                          'lambda':'floor(log2 ell)+popcount(ell)-1','ell':'62+10r',
                          'fixed_role_count':'4+21r','saving':'3rM+5rA=8r'},
        'fixed_data_recipe':[
            'Retain actual inherited alphabet, kappa_minus_one, dyadic K and program alpha/gamma from parent.',
            'For each actual relator P, W=[(S(P)-I)C | (S(P^-1)-I)C] on the eight unchanged raw selected words.',
            'Choose primitive common left normal (s,p-t,-q)/gcd unless zero; for P=+/-I use normal(1,0,0) and W=0.',
            'Choose fixed output permutation with first normal coordinate nonzero; apply same permutation to W rows.',
            'Let g=gcd(n1,n2)>0 and choose a*n1+b*n2=g; primitive normal proves gcd(g,n3)=1.',
            'For each permuted W column(x,y,z), precompile alpha=b*x-a*y and integer beta=z/g.',
            'Precompile u1=n2/g,u2=-n1/g,v1=-n3*a,v2=-n3*b,v3=g.',
            'Sixteen form coefficients and five basis coefficients are fixed integer numerals per relator, not independent witnesses.',
            'All divisions, gcd and permutation choices occur only in fixed preparation. Runtime source uses only +,-,*.',
            'Equality to parent is under this common actual-P recipe, not independent old/new coefficient-variable assignments.'],
        'static_shape_censuses':censuses,'examples':examples,
        'count_only_scope':'r=2,3,8 are inherited census minus proved8r delta; full graphs saved for r=0,1,4.',
        'execution_scope':{'metadata_only':True,'arithmetic_or_coefficient_evaluation':False,
                           'degree_propagation':False,'frozen_program_execution':False,
                           'numerical_universal_relator_data_supplied':False}}
    output = Path('/tmp/positive7_relator_plane_compose_root.json')
    if output.exists():
        raise ValueError('refuse overwrite')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'sha256':sha(output.read_bytes()),'rows':sum(len(g['source']) for g in examples),
                      'shape_censuses':censuses},indent=2))


if __name__ == '__main__':
    main()
