"""Independent finite integer coefficient collection; no producer imports.
The script is also suitable for passing verbatim to isolated Python -c.
"""
from collections import Counter, defaultdict
import copy
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys

root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('/release')

def require(ok, text):
    if not ok:
        raise ValueError(text)

def sparse(terms, n=None):
    result = {}
    for coefficient, monomial in terms:
        require(type(coefficient) is int and coefficient != 0, 'nonzero integer coefficient')
        require(all(type(i) is int and i >= 0 and (n is None or i < n) for i in monomial), 'valid coordinate')
        key = tuple(monomial)
        require(key == tuple(sorted(key)) and key not in result, 'canonical unique monomial')
        result[key] = coefficient
    return result

def add(target, source, scale=1):
    for monomial, coefficient in source.items():
        target[monomial] += coefficient * scale


def square_into(result, row):
    for left, c in row.items():
        for right, d in row.items():
            result[tuple(sorted(left + right))] += c * d


def clean(p):
    return {m:c for m,c in p.items() if c}


def metrics(p, n):
    require(p, 'nonempty polynomial')
    require({i for m in p for i in m} == set(range(n)), 'complete live coordinate range')
    height = max(map(abs,p.values()))
    return {'variables': n, 'monomials': len(p), 'degree': max(map(len,p)),
            'coefficient_height': height, 'constant': p.get((), 0),
            'individual_degree': max(max(Counter(m).values(), default=0) for m in p),
            'height_witness': next([c, list(m)] for m,c in p.items() if abs(c)==height)}


def network_energy(art, cert):
    n = len(art['variables'])
    def index(i,bound):return type(i) is int and 0<=i<bound
    require(cert['source_sha256'] in source_by_digest,'network literal source bytes present')
    src=source_by_digest[cert['source_sha256']]
    norm=cert['normalization'];logical=len(norm['variables']);original=len(src['variables'])
    require(norm['original_variables']==original,'network original source dimension')
    for i,v in enumerate(norm['variables']):
        if i<original:
            require(v=={'kind':'original','source_index':i},'strict original normalized coordinate')
        elif v['kind']=='scale':
            require(index(v['variable'],original) and type(v['coefficient']) is int and v['coefficient']>1,'strict normalized scale constructor')
        else:
            require(v['kind']=='constant' and type(v['value']) is int and v['value']>1,'strict normalized literal constructor')
    for row in norm['rows']:
        require(all(type(c) is int and c in (-1,1) and all(index(i,logical) for i in monomial) for c,monomial in row['terms']), 'strict normalized signed occurrences')
        if row['kind']=='source':require(index(row['source_row'],len(src['residuals'])),'strict normalized source row')
    for v in art['variables']:
        if v['kind'] in ('alias','equality_dummy'):
            require(v['normalized_variable'] is None or index(v['normalized_variable'],logical),'strict alias logical index')
    for p in cert['products']:
        require(len(p['factors'])==2 and all(index(i,n) for i in p['factors']),'strict product factors')
        require(all(i is None or index(i,logical) for i in p['logical_factors']),'strict product logical factors')
        for r,j,c in p['bindings']:
            require(index(r,len(norm['rows'])) and index(j,len(norm['rows'][r]['terms'])) and type(c) is int and c in (-1,1),'strict occurrence binding')
    nv = len(cert['vertices'])
    require(nv > 0, 'nonempty graph')
    vertices=[v for block in [cert['hub_vertices']]+cert['row_blocks'] for v in block]
    require(all(index(i,nv) for i in vertices) and sorted(vertices)==list(range(nv)),'strict complete graph vertex partition')
    divergence = [defaultdict(int) for _ in cert['vertices']]
    for edge in cert['edges']:
        require(all(type(edge[k]) is int and 0 <= edge[k] < nv for k in ['tail','head']), 'strict graph vertex index')
        require(edge['tail'] != edge['head'], 'no graph loop')
        require(type(edge['coefficient']) is int and edge['coefficient'] in (-1,1), 'signed edge coefficient')
        require(all(type(i) is int and 0 <= i < n for i in edge['monomial']), 'strict edge coordinate index')
        term = tuple(sorted(edge['monomial']))
        divergence[edge['tail']][term] += edge['coefficient']
        divergence[edge['head']][term] -= edge['coefficient']
    total = defaultdict(int)
    for row in divergence:
        square_into(total, clean(row))
    for cycle in cert['equality_cycles']:
        ids = cycle['aliases']
        require(index(cycle['normalized_variable'],logical),'strict equality logical index')
        require(ids and len(ids) == len(set(ids)) and all(type(i) is int and 0 <= i < n for i in ids), 'strict distinct cycle coordinates')
        require(cycle.get('mode', 'cycle') in ('cycle','quartic_pair','unit_product_cycle','anchored_cycle'), 'known equality mode')
        if cycle.get('mode', 'cycle') == 'anchored_cycle':
            require(len(ids)==2, 'anchored pair')
            forms=cycle['forms']
            require(type(forms) is list and len(forms)==3, 'three anchored forms')
            require(all(type(f) is list and len(f) in (1,2) and index(f[0],n) and f[0] in ids and (len(f)==1 or index(f[1],n) and f[1] in cert['unit_path']) for f in forms), 'strict anchored factors')
            require({f[0] for f in forms}==set(ids) and len({tuple(sorted(f)) for f in forms})==3, 'distinct forms cover both aliases')
            forms=[tuple(sorted(f)) for f in forms]
            relations=[{a:1,b:-1} for a,b in zip(forms,forms[1:]+forms[:1])]
        elif cycle.get('mode', 'cycle') == 'unit_product_cycle':
            require(len(ids)==2, 'unit-product pair')
            anchor,unit=cycle['anchor'],cycle['unit']
            require(type(anchor) is int and anchor in ids and type(unit) is int and unit in cert['unit_path'] and 0<=unit<n, 'strict unit-product anchor indices')
            a,b=ids
            product=tuple(sorted((anchor,unit)))
            relations=[{(a,):1,(b,):-1},{(b,):1,product:-1},{product:1,(a,):-1}]
        elif cycle.get('mode', 'cycle') == 'quartic_pair':
            require(len(ids)==2, 'quartic pair')
            a,b = ids
            ab = tuple(sorted((a,b)))
            relations = [{(a,a):1,(b,b):-1}, {(a,a):1,ab:-1}, {ab:1,(b,b):-1}]
        else:
            require(len(ids) != 2, 'no two-element simple cycle')
            relations = [{(a,):1,(b,):-1} for a,b in zip(ids,ids[1:]+ids[:1])] if len(ids)>1 else []
        for row in relations:
            square_into(total, row)
    units = cert['unit_path']
    require(len(units)>=2 and len(units)==len(set(units)) and all(type(i) is int and 0 <= i < n for i in units), 'strict distinct unit-path coordinates')
    square_into(total, {():1,(units[0],):-1})
    for a,b in zip(units,units[1:]):
        square_into(total, {(a,):1,(b,):-1})
    square_into(total, {(units[-1],):1,():-1})
    require(all(c % 2 == 0 for c in total.values()), 'integral half energy')
    return clean({m:c//2 for m,c in total.items()})


def load_chunked(art,path,n):
    require(art['schema']=='chunked-sparse-polynomial-v1','known chunk manifest schema')
    require(type(art['variables']) is int and art['variables']==n,'chunk dimension')
    require(art['ordering']=='strict lexicographic ascending monomial tuple','chunk order declaration')
    chunks=art['chunks']; require(type(chunks) is list and chunks,'nonempty chunk list')
    names=[item['path'] for item in chunks]
    require(len(names)==len(set(names)),'duplicate chunk name')
    require(all(str(PurePosixPath(name))==name and not PurePosixPath(name).is_absolute() and '..' not in PurePosixPath(name).parts for name in names),'safe canonical chunk paths')
    require(type(art['total_terms']) is int and art['total_terms']>0,'positive strict total count')
    actual={};last=None
    for item in chunks:
        chunk=path.parent/item['path'];raw=chunk.read_bytes()
        require(hashlib.sha256(raw).hexdigest()==item['sha256'],'chunk byte hash')
        data=json.loads(raw);require(data['schema']=='sparse-polynomial-chunk-v1','known chunk schema')
        ts=data['terms'];require(type(item['terms']) is int and item['terms']>0 and len(ts)==item['terms'],'chunk term count')
        require(ts[0][1]==item['first_monomial'] and ts[-1][1]==item['last_monomial'],'chunk actual boundary monomials')
        part=sparse(ts,n)
        for m,c in part.items():
            require(last is None or last<m,'strict global chunk monomial order')
            actual[m]=c;last=m
    require(len(actual)==art['total_terms'],'chunk full term count')
    return actual

index_controls = []
for label, bad in [
    ('negative coordinate', [[1,[-1]]]),
    ('upper-bound coordinate', [[1,[2]]]),
    ('boolean coordinate', [[1,[True]]]),
    ('boolean coefficient', [[True,[0]]]),
    ('repeated monomial', [[1,[0]],[1,[0]]]),
    ('uncanonical monomial', [[1,[1,0]]])]:
    try:
        sparse(bad,2)
    except ValueError:
        index_controls.append(label)
    else:
        raise ValueError('Invalid literal accepted: '+label)
source_literals=[]
source_by_digest={}
for path in sorted(root.rglob('*.json')):
    try:
        obj=json.loads(path.read_text())
    except (ValueError,UnicodeError):
        continue
    if not isinstance(obj,dict) or not isinstance(obj.get('variables'),list) or not isinstance(obj.get('residuals'),list):
        continue
    source_rows=[r for r in obj['residuals'] if isinstance(r,dict) and isinstance(r.get('terms'),list)]
    if len(source_rows)!=len(obj['residuals']):
        continue
    for row in source_rows:
        sparse(row['terms'],len(obj['variables']))
    source_by_digest[hashlib.sha256(path.read_bytes()).hexdigest()]=obj
    source_literals.append({'path':str(path.relative_to(root)),'variables':len(obj['variables']),'residuals':len(source_rows),'literal_terms':sum(len(r['terms']) for r in source_rows)})

results = []
skipped = []
for path in sorted(root.rglob('expanded_polynomial.json')):
    eqpath = path.with_name('equation.json')
    if not eqpath.is_file():
        skipped.append(str(path.relative_to(root)))
        continue
    eq = json.loads(eqpath.read_text())
    art = json.loads(path.read_text())
    if 'residuals' not in eq or ('terms' not in art and art.get('schema')!='chunked-sparse-polynomial-v1'):
        skipped.append(str(path.relative_to(root)))
        continue
    n = len(eq['variables'])
    require(n > 0, 'nonempty variable list')
    if 'variables' in art:
        require(art['variables'] == eq['variables'] if isinstance(art['variables'], list) else type(art['variables']) is int and art['variables']==n, 'same expansion variable declarations')
    if 'variable_count' in art:
        require(type(art['variable_count']) is int and art['variable_count'] == n, 'same expansion dimension')
    expected = defaultdict(int)
    for row in eq['residuals']:
        square_into(expected, sparse(row['terms'], n))
    actual = load_chunked(art,path,n) if art.get('schema')=='chunked-sparse-polynomial-v1' else sparse(art['terms'], n)
    chunk_controls=[]
    if art.get('schema')=='chunked-sparse-polynomial-v1':
        for label in ['chunk_hash','duplicate_chunk']:
            bad=copy.deepcopy(art)
            if label=='chunk_hash':bad['chunks'][0]['sha256']='0'*64
            else:bad['chunks'].append(copy.deepcopy(bad['chunks'][0]))
            try:load_chunked(bad,path,n)
            except ValueError:chunk_controls.append(label)
            else:raise ValueError('Invalid chunk metadata accepted: '+label)
    require(actual == clean(expected), 'SOS coefficient mismatch: ' + str(path))
    corrupted = dict(actual)
    corrupted[()] = corrupted.get((),0)+1
    require(corrupted != clean(expected), 'corruption did not differ')
    results.append(dict(path=str(path.relative_to(root)), kind='chunked literal SOS' if art.get('schema')=='chunked-sparse-polynomial-v1' else 'literal SOS', residuals=len(eq['residuals']), chunk_controls_rejected=chunk_controls,
                        sha256=hashlib.sha256(path.read_bytes()).hexdigest(), **metrics(actual,n)))
for path in sorted(root.rglob('octic_expanded.json')):
    art=json.loads(path.read_text())
    companion=json.loads(path.with_name('octic_residuals.json').read_text())
    n=art['metrics']['variables']
    require(type(n) is int and n > 0 and art['metrics']==companion['metrics'], 'octic shared dimension and metrics')
    expected=defaultdict(int)
    for row in companion['residuals']:
        square_into(expected,sparse(row['terms'],n))
    actual=sparse(art['polynomial'],n)
    require(actual==clean(expected),'octic complete coefficient identity')
    measured=metrics(actual,n)
    for k in ['variables','monomials','degree','coefficient_height']:
        require(measured[k]==art['metrics'][k],'octic independently measured '+k)
    results.append(dict(path=str(path.relative_to(root)),kind='literal octic SOS',residuals=len(companion['residuals']),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),**measured))
for path in sorted(root.rglob('*polynomial.json')):
    certpath = path.with_name(path.name.replace('polynomial.json','certificate.json'))
    if not certpath.is_file():
        continue
    art = json.loads(path.read_text())
    cert = json.loads(certpath.read_text())
    if not all(k in cert for k in ['vertices','edges','equality_cycles','unit_path']):
        continue
    actual = sparse(art['terms'], len(art['variables']))
    require(actual == network_energy(art,cert), 'half-energy coefficient mismatch: '+str(path))
    measured = metrics(actual,len(art['variables']))
    require(measured['coefficient_height']==1 and measured['degree']==4 and measured['constant']==1,
            'height-one quartic with constant one')
    for k,v in measured.items():
        if k in art.get('metrics',{}):
            require(art['metrics'][k]==v, 'metric mismatch: '+k)
    results.append(dict(path=str(path.relative_to(root)), kind='literal half energy',
                        sha256=hashlib.sha256(path.read_bytes()).hexdigest(), **measured))

residual_only=[]
for delivery in sorted(root.rglob('DELIVERY.json')):
    doc=json.loads(delivery.read_text())
    if doc.get('coefficient_payload')!='residuals only; no collected array delivered':continue
    folder=delivery.parent
    require(not (folder/'expanded_polynomial.json').exists(),'explicit residual-only payload has no fake expansion')
    eq=json.loads((folder/'equation.json').read_text());n=len(eq['variables']);expected=defaultdict(int)
    for row in eq['residuals']:square_into(expected,sparse(row['terms'],n))
    collected=clean(expected);measured=metrics(collected,n);declared=json.loads((folder/'metrics.json').read_text())
    for key,target in [('variables','variables'),('degree','degree'),('monomials','collected_terms'),('coefficient_height','coefficient_height')]:require(measured[key]==declared[target],'residual-only independently measured '+key)
    require(len(eq['residuals'])==declared['residuals'],'residual-only row census')
    require(sum(len(r['terms']) for r in eq['residuals'])==declared['residual_terms'],'residual-only source-term census')
    residual_only.append({'path':str(folder.relative_to(root)),'payload':'Literal residual arrays only; complete collected array independently rederived here but not delivered','kind':'residual-only exact SOS control','equation_sha256':hashlib.sha256((folder/'equation.json').read_bytes()).hexdigest(),**measured})

require(results, 'no polynomial pairs discovered')
print(json.dumps({'status':'PASS', 'equations_recollected':len(results), 'results':results,
                  'source_literal_files':len(source_literals),'source_literal_terms':sum(x['literal_terms'] for x in source_literals),'strict_index_controls_rejected':index_controls, 'source_literals':source_literals,
                  'unpaired_expansions':skipped,'explicit_residual_only_controls':residual_only,
                  'boundary':'Every listed coefficient independently recollected from literal residuals or energy certificates; zero-set equivalences and unbounded calibration are not inferred from this check.'}, indent=2))
