"""Independent data-only audit. Never imports or executes downloaded programs."""
import json
from collections import Counter
from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def load(p):
    return json.loads(p.read_text())

def sparse(terms):
    d = {}
    for c, m in terms:
        if type(c) is not int or c == 0 or not isinstance(m, list):
            raise ValueError('Invalid coefficient/monomial')
        if any(type(i) is not int or i < 0 for i in m) or m != sorted(m):
            raise ValueError('Invalid variable index/order')
        t = tuple(m)
        if t in d:
            raise ValueError('Duplicate monomial')
        d[t] = c
    return d

def quartic(p):
    eq, poly = load(p/'equation.json'), load(p/'expanded_polynomial.json')
    result = Counter()
    for row in eq['residuals']:
        terms = sparse(row['terms'])
        if max(map(len,terms), default=0) > 2:
            raise ValueError('Nonquadratic residual')
        for a, x in terms.items():
            for b, y in terms.items():
                result[tuple(sorted(a+b))] += x*y
    result = {m:c for m,c in result.items() if c}
    expected = sparse(poly['terms'])
    if result != expected:
        raise ValueError('Coefficient expansion mismatch at '+str(p))
    variables = set(i for m in result for i in m)
    n = len(eq['variables']) if isinstance(eq['variables'],list) else eq['variables']
    if variables != set(range(n)):
        raise ValueError('Variable census mismatch')
    return {'path':str(p.relative_to(ROOT)), 'domain':eq['domain'], 'variables':n,
            'rows':len(eq['residuals']), 'degree':max(map(len,result)),
            'terms':len(result), 'height':max(map(abs,result.values())),
            'equation_sha256':sha256((p/'equation.json').read_bytes()).hexdigest(),
            'polynomial_sha256':sha256((p/'expanded_polynomial.json').read_bytes()).hexdigest(),
            'all_coefficients_exactly_match_sum_of_squares':True}

def circuit(p):
    d=load(p)
    rows=d['source']; byname={}; degrees={x:1 for x in d['witnesses']}
    for x in d['fixed_numerals']:
        degrees[x]=0
    for name,op,a,b in rows:
        if name in degrees or op not in ['+','-','*']:
            raise ValueError('Invalid graph row')
        da=0 if type(a) is int else degrees[a]
        db=0 if type(b) is int else degrees[b]
        degrees[name]=da+db if op=='*' else max(da,db)
        byname[name]=(op,a,b)
    live=set(); pending=[d['output']]
    while pending:
        name=pending.pop()
        if name in byname and name not in live:
            live.add(name);pending += [x for x in byname[name][1:] if isinstance(x,str)]
    if len(live)!=d['operations']:
        raise ValueError('Live operation census mismatch')
    return {'path':str(p.relative_to(ROOT)), 'domain':d['domain'], 'variables':len(d['witnesses']),
            'live_operations':len(live),'operation_breakdown':dict(Counter(byname[n][0] for n in live)),
            'syntactic_degree_upper_bound':degrees[d['output']],
            'exact_degree_claim_from_source':d.get('exact_degree'),
            'exact_degree_not_reproved_here':True,'sha256':sha256(p.read_bytes()).hexdigest()}

def dag(p):
    d=load(p); nodes=d['nodes']; degree=[]
    for j,row in enumerate(nodes):
        kind=row[0]
        if kind in ['variable','coefficient','constant','integer']:
            degree.append(1 if kind=='variable' else 0)
        elif kind in ['add','sub','mul']:
            a,b=row[1:]
            if type(a) is not int or type(b) is not int or not 0<=a<j or not 0<=b<j:
                raise ValueError('Non-topological DAG')
            degree.append(degree[a]+degree[b] if kind=='mul' else max(degree[a],degree[b]))
        else:
            raise ValueError('Unknown node kind')
    live=set();pending=[d['output']]
    while pending:
        j=pending.pop()
        if j not in live:
            live.add(j)
            if nodes[j][0] in ['add','sub','mul']:
                pending.extend(nodes[j][1:])
    counts=Counter(nodes[j][0] for j in live if nodes[j][0] in ['add','sub','mul'])
    if sum(counts.values())!=d['operations']:
        raise ValueError('DAG cost mismatch')
    return {'path':str(p.relative_to(ROOT)),'domain':d['domain'],'variables':d['variable_count'],
            'live_operations':sum(counts.values()),'operation_breakdown':dict(counts),
            'syntactic_degree_upper_bound':degree[d['output']],
            'exact_degree_claim_from_source':d['exact_degree'],'exact_degree_not_reproved_here':True,
            'sha256':sha256(p.read_bytes()).hexdigest()}

def main():
    quartics=[quartic(p.parent) for p in sorted(ROOT.rglob('expanded_polynomial.json'))]
    circuits=[]
    for q in ['con-zfc-diophantine-forms/133-staged-certificates/compact/equation_84.json',
              'con-zfc-diophantine-forms/133-staged-certificates/compact/equation_85.json',
              'con-zfc-diophantine-forms/130-shared-index/center246/equation.json',
              'research/ten-positive-qcube-normalization/zero86.json']:
        circuits.append(circuit(ROOT/q))
    for p in sorted((ROOT/'con-zfc-diophantine-forms/131-shared-pell-caps-round16/scalar').rglob('*.json')):
        circuits.append(dag(p))
    receipt={'method':'Independent standard-library data-only exact arithmetic. No downloaded executable imported or run.',
             'scope':'All coefficients of listed quartics; graph syntax/live costs of listed circuits. No unbounded semantics or fixed-numeral reconstruction audited here.',
             'quartics':quartics,'circuits':circuits}
    (ROOT/'INDEPENDENT_DATA_AUDIT.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
