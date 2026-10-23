#!/usr/bin/env python3
"""Independent finite source, coefficient, calibration and literal-circuit audit.

This checker never imports the circuit builder. Modular tests are diagnostics;
source identities and the local cancellation identities are exact polynomials.
"""
from pathlib import Path
from collections import Counter, defaultdict
import copy
import gzip
import hashlib
import itertools
import json
import math
import random
import sys

ROOT = Path(__file__).resolve().parent
ZERO = (0,)*35


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(name):
    return json.loads((ROOT/name).read_text())


def digest(blob):
    return hashlib.sha256(blob).hexdigest()


def add(a, b, sign=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0)+sign*v
    return {k:v for k,v in out.items() if v}


def mul(a, b):
    out = defaultdict(int)
    for k, v in a.items():
        for l, w in b.items():
            out[tuple(x+y for x,y in zip(k,l))] += v*w
    return {k:v for k,v in out.items() if v}


def power(a, n):
    out = {tuple(0 for _ in next(iter(a))):1}
    for _ in range(n):
        out = mul(out, a)
    return out


def rows(source):
    return [{tuple(t['powers']):t['coefficient'] for t in row['terms']}
            for row in source['equations']]


def source_change(parent, source):
    names = parent['sparse_term_coordinate_order']
    basis = [{tuple(int(i==j) for j in range(35)):1} for i in range(35)]
    substitution = list(basis)
    substitution[names.index('P')] = add(add(basis[names.index('P')],
        basis[names.index('eta')]), basis[names.index('zeta')])
    substitution[names.index('N')] = add(add(basis[names.index('N')],
        mul(basis[names.index('J')], basis[names.index('beta')])), {ZERO:1})
    changed = []
    for row in rows(parent):
        value = {}
        for mon, coeff in row.items():
            term = {ZERO:coeff}
            for i, exponent in enumerate(mon):
                if exponent:
                    term = mul(term, power(substitution[i], exponent))
            value = add(value, term)
        changed.append(value)
    changed[13] = add(changed[13], changed[1])
    changed[14] = add(changed[14], changed[2])
    require(changed==rows(source), 'exact P/N affine source substitution')
    return {'identical_transformed_rows':22,
            'map':'P_old=P+eta+zeta; N_old=N+beta*J+1',
            'positive_inverse_hypotheses':'All old source variables positive; beta>0.',
            'inverse_positivity':'P_old-eta-zeta=E*(c-eta)>0; N_old-q=q^3-q>0.',
            'semantic_scope':'Polynomial identities plus the stated ordinary positive-source argument; no native calibration.'}


def extraction(code, kernels, source):
    w = code['weights']; targets = code['targets_by_row']
    require(len(w)==31 and len(set(w))==31 and min(w)>0, 'input positions')
    require(len(targets)==22 and len(set(targets))==22, 'target positions')
    require(code['targets']==sorted(targets), 'sorted targets')
    require(code['order']==[j+1 for j in sorted(range(22),key=targets.__getitem__)], 'row order')
    expected = [defaultdict(int) for _ in range(3)]
    for j, row in enumerate(rows(source)):
        for mon, coeff in row.items():
            degree = sum(mon[:31]); exponent = targets[j]-sum(a*b for a,b in zip(mon[:31],w))
            require(degree<=2 and exponent>=0, 'ordinary reversed exponent')
            weight = 2 if degree<2 or max(mon[:31])==2 else 1
            expected[degree][exponent, mon[31:]] += weight*coeff
    for d, layer in enumerate(kernels['kernels']):
        actual = {}
        for term in layer['terms']:
            for c in term['coefficient']:
                key = term['exponent'], tuple(c['port_powers'])
                require(key not in actual, 'unique literal coefficient entry')
                actual[key] = c['integer']
        require(actual=={k:v for k,v in expected[d].items() if v}, 'reconstructed weighted kernels')
    monomials = [[()], [(i,) for i in range(31)], list(itertools.combinations_with_replacement(range(31),2))]
    extracted = [defaultdict(int) for _ in range(22)]
    target_index = {q:j for j,q in enumerate(targets)}
    interactions = hits = 0
    for d, layer in enumerate(kernels['kernels']):
        for term in layer['terms']:
            for indices in monomials[d]:
                interactions += 1
                j = target_index.get(term['exponent']+sum(w[i] for i in indices))
                if j is None:
                    continue
                hits += 1
                coeff = 2 if d==2 and indices[0]!=indices[1] else 1
                mon = [0]*31
                for i in indices:
                    mon[i] += 1
                for c in term['coefficient']:
                    extracted[j][tuple(mon)+tuple(c['port_powers'])] += coeff*c['integer']
    require([{k:v for k,v in e.items() if v} for e in extracted]==
            [{k:2*v for k,v in r.items()} for r in rows(source)], 'all22 exact target identities')
    require(interactions==22450 and hits==85, 'all85 interactions')
    degrees = [max(t['exponent'] for t in l['terms']) for l in kernels['kernels']]
    require(degrees==[1627,1941,1850] and max(w)==116, 'kernel degrees')
    require(max(degrees[d]+d*116 for d in range(3))==2082 and max(targets)==2050, 'height and headroom')
    require(kernels['kernels'][2]['terms'][-1]['coefficient']==
            [{'integer':1,'port_powers':[0,0,0,0]}], 'positive quadratic leader')
    return {'records':85,'interactions':interactions,'target_hits':hits,
            'exact_target_identities':22,'kernel_degrees':degrees,
            'W':116,'height':2082,'maximum_target':2050,
            'quadratic_dominance_gaps':[25,455]}


def ports_and_fixed():
    ports = []
    for r in read('coefficients/COEFFICIENT_BINDING.json')['ports']:
        packed = (ROOT/'coefficients'/r['gzip_file']).read_bytes(); raw = gzip.decompress(packed)
        require(digest(raw)==r['sha256'] and digest(packed)==r['gzip_sha256'], 'whole tuple payload')
        require(len(raw)==r['bytes'] and int.from_bytes(raw,'little').bit_length()==r['bits'], 'whole tuple dimensions')
        ports.append(int.from_bytes(raw,'little'))
    require([x.bit_length() for x in ports]==[429959,434054,429959,429960], 'compact54 tuple order')
    require(ports[0]==(1<<429959)-1 and min(ports)>0, 'positive authentic ports')
    fixed = {}
    for r in read('fixed/BINDING.json')['records']:
        packed = (ROOT/r['path']).read_bytes(); raw = gzip.decompress(packed)
        require(digest(raw)==r['raw_sha256'] and digest(packed)==r['gzip_sha256'], 'materialized fixed leaf')
        require(packed[4:8]==b'\0'*4 and packed[9]==255, 'canonical generated gzip')
        value = r['sign']*int.from_bytes(raw,'little')
        require(abs(value).bit_length()==r['bits'] and len(raw)==r['raw_bytes'], 'fixed dimensions')
        fixed[r['name']] = value
    return ports, fixed


def coefficient_bounds(kernels, ports):
    bits = [429959,434054,429959,429960]; h = 864014
    records = []; factorized = []
    for d, layer in enumerate(kernels['kernels']):
        for term in layer['terms']:
            polynomial = {tuple(c['port_powers']):c['integer'] for c in term['coefficient']}
            bound = sum(abs(c)*(1<<sum(a*b for a,b in zip(m,bits))) for m,c in polynomial.items())
            before = bound.bit_length(); method = 'sum of absolute monomial bounds'
            if polynomial=={(1,0,0,0):2,(1,1,0,0):2}:
                bound = 2*((1<<bits[0])-1)*(1<<bits[1])
                method = '2*beta*(K0+1), K0+1<=2^434054'
                factorized.append({'degree':d,'exponent':term['exponent']})
            actual = sum(c*math.prod(v**e for v,e in zip(ports,m)) for m,c in polynomial.items())
            require(abs(actual)<=bound<(1<<h), 'strict generic and actual coefficient bound')
            records.append({'degree':d,'exponent':term['exponent'],'recipe':term['coefficient'],
                            'termwise_upper_bound_bits':before,'certified_upper_bound_bits':bound.bit_length(),
                            'actual_absolute_bits':abs(actual).bit_length(),'method':method})
    require(len(records)==85 and len(factorized)==1, 'all85 records and unique factorization')
    require(max(r['actual_absolute_bits'] for r in records)==h, 'minimal actual dyadic height')
    return {'status':'PASS','height_exponent':h,'kappa':h+12,'records':records,
            'factorized':factorized,'minimal_dyadic_height_for_literal_kernel':True,
            'generic_port_boxes':'0<=beta,MC<2^429959; 0<=K0<2^434054; 0<=MF<2^429960'}


def calibration(config):
    kappa = config['base_scale_exponent']; E = 2082+116+2; hp = E+116+23
    delta = (hp-15)%2; lp = (22-hp*kappa)%2
    ne = (hp-15-delta)//2; ce = ((15+delta)*kappa+lp-22)//2
    require((E,hp,delta,lp,ne,ce)==(2200,2339,0,0,1162,6480184), 'even-kappa exact calibration')
    require(config['threshold_scale_exponent']==ce and config['threshold_B_power']==ne and
            config['threshold_b_power']==delta and config['block_scale_power_of_two']==lp, 'configured calibration')
    # Equality of the constant and k coefficients proves the identity for every k>=0.
    lhs_const = hp*kappa+lp-22; lhs_k = 2*hp-30
    rhs_const = 2*(ce+ne*kappa); rhs_k = 2*(delta+2*ne)
    require((lhs_const,lhs_k)==(rhs_const,rhs_k), 'universal population identity in k')
    return {'Ecode':E,'Hp':hp,'delta':delta,'lp':lp,'N_B_exponent':ne,'threshold_scale_exponent':ce,
            'population_identity_constant':lhs_const,'population_identity_k_coefficient':lhs_k,
            'identity':'log2(L)+pop(T)=2log2(N) for every binary b=2^k, including k=0.'}


def audit_object(obj, fixed, ports, config):
    nodes = obj['nodes']; live = set(); todo = [obj['output']]
    for i, n in enumerate(nodes):
        require(n['kind'] in ['variable','literal','fixed','add','sub','mul'], 'division-free node kind')
        if n['kind'] in ['add','sub','mul']:
            require(0<=n['left']<i and 0<=n['right']<i, 'acyclic node')
    while todo:
        i = todo.pop()
        if i in live:
            continue
        live.add(i); n = nodes[i]
        if n['kind'] in ['add','sub','mul']:
            todo.extend([n['left'],n['right']])
    require(len(live)==len(nodes), 'all nodes live')
    require(obj['variables']==['b','g','h','s','w','C','i','j','n'], 'nine input order')
    require({n['name'] for n in nodes if n['kind']=='variable'}==set(obj['variables']), 'all nine inputs live')
    count = Counter(n['kind'] for n in nodes if n['kind'] in ['add','sub','mul'])
    require(dict(count)==obj['operation_counts'] and sum(count.values())==obj['total_operations'], 'independent operation count')
    require(sum(count.values())==(450 if obj['domain']=='natural' else 443), '443/450 counts')
    for key in ['base_scale_exponent','threshold_scale_exponent','threshold_B_power','threshold_b_power','block_scale_power_of_two']:
        require(obj[key]==config[key], 'literal outer register '+key)
    require(obj['source_sha256']==digest((ROOT/'data/H2082/source.json').read_bytes()) and
            obj['layout_sha256']==digest((ROOT/'data/H2082/layout.json').read_bytes()), 'literal source binding')
    require(obj['coefficient_bound_exponent']==864014 and obj['coherent_tuple']=='whole compact54-sharp',
            'literal compact coefficient metadata')
    for r in obj['coefficient_recipes']:
        value = sum(c['integer']*math.prod(v**e for v,e in zip(ports,c['port_powers'])) for c in r['terms'])
        require(value==fixed[r['name']], 'exact coefficient recipe')
    require(fixed['base_scale']==1<<864026 and fixed['threshold_6480184']==1<<6480184, 'exact scale leaves')
    require({n['name'] for n in nodes if n['kind']=='fixed'}==set(fixed), 'all11 fixed leaves used')
    return {'operations':sum(count.values()),'operation_counts':dict(count),'all_nodes_live':True,
            'variables':9,'fixed_leaves':len(fixed),'domain':obj['domain']}


def evaluate(obj, vals, fixed, mod):
    out = []
    for n in obj['nodes']:
        k = n['kind']
        if k=='variable':v = vals[n['name']]
        elif k=='literal':v = n['value']
        elif k=='fixed':v = fixed[n['name']]
        else:
            l = out[n['left']]; r = out[n['right']]
            v = l+r if k=='add' else l-r if k=='sub' else l*r
        out.append(v%mod)
    return out[obj['output']], {k:out[i] for k,i in obj['named_nodes'].items()}


def formula(obj, vals, ports, kernels, code, mod):
    v = dict(vals)
    if obj['domain']=='positive':v['j']-=1
    else:
        for name in v:
            if name!='j':v[name]+=1
    b,g,h,s,w,C,i,j,n = [v[name]%mod for name in obj['variables']]
    B = pow(2,864026,mod)*b*b%mod
    def coeff(ts):
        return sum(t['integer']*math.prod(pow(q,e,mod) for q,e in zip(ports,t['port_powers'])) for t in ts)%mod
    ds = [sum(coeff(t['coefficient'])*pow(B,t['exponent'],mod) for t in layer['terms'])%mod for layer in kernels['kernels']]
    ell = sum(pow(B,x,mod) for x in code['weights'])%mod
    targets = sum(pow(B,x,mod) for x in code['targets'])%mod
    N0 = pow(B,117,mod); word = (ell+g)%mod
    source = (ds[2]*word*word+ds[1]*word+ds[0])%mod
    S = (g+N0*(2*source+targets))%mod
    T = (N0-1-(b-1)*ell+N0*(B-2)*targets)%mod
    L = b*pow(B,2200,mod)%mod
    N = pow(2,6480184,mod)*pow(B,1162,mod)%mod
    R = (L*(S+T+1)-S-1)%mod; t = b*pow(B,116,mod)%mod
    U = N*N*w%mod; Y = N*N*s%mod; M = R*Y%mod; P = 2*M*M*U%mod
    K = (R+1+h*(P-1))%mod; A = M*(U+1)%mod; B1 = (2*R+1)%mod
    W = b*w%mod; J = (4*A-5)%mod; Q = (3*W*C-2*(W*W-1))%mod
    D = ((A*A-1)*C*C+1)%mod; k = i*J*C%mod; E = k*D*C%mod
    F = ((A*A-1)*E*E+1)%mod; G = (A+F*(C*D+1-A))%mod
    H = (C+F*(B1+j*C))%mod; I = ((G*G-1)*H*H+1)%mod
    V0 = P*K%mod; V1 = k*(8*D*D-4*D-1)*G*H%mod
    a0 = ((P*P-1)*K*K+1)%mod; a1 = D*F*I%mod
    margin = (K*K*(4*t-g)-16*t*(C-K*Y)**2)%mod
    omega = J*margin%mod; e0 = (J*(n+W*W)+Q)%mod
    theta = (e0-omega*(V0+V1))%mod
    value = ((theta*theta-omega*omega*(a0+64*a1))**2-256*pow(omega,4,mod)*a0*a1)%mod
    return value, {'B':B,'Usource':word,'Gsource':source,'Scode':S,'Tcode':T,'L':L,'N':N,'R':R,'capbase':t,
                   'A':A,'D':D,'F':F,'G':G,'H':H,'Tmajor':k*(8*D*D-4*D-1)%mod,
                   'V1':V1,'Omega':omega,'margin':margin}


def cancellation_identities():
    # Exact sparse polynomial identities in six free formal symbols.
    z = (0,)*6
    vs = [{tuple(int(i==j) for j in range(6)):1} for i in range(6)]
    one = {z:1}
    def scale(a,k):return {m:k*c for m,c in a.items() if k*c}
    A,C,i,G,H,_ = vs
    D = add(mul(add(power(A,2),one,-1),power(C,2)),one)
    k = mul(mul(i,add(scale(A,4),scale(one,5),-1)),C)
    E = mul(mul(k,D),C)
    F = add(mul(add(power(A,2),one,-1),power(E,2)),one)
    B8 = add(add(scale(power(D,2),8),scale(D,4),-1),one,-1)
    error = add(mul(add(scale(D,8),one),power(k,2)),scale(D,64),-1)
    require(add(add(power(mul(k,B8),2),scale(mul(D,F),64),-1),error,-1)=={}, 'exact ordinary majorant defect')
    V1 = mul(mul(mul(k,B8),G),H)
    I = add(mul(add(power(G,2),one,-1),power(H,2)),one)
    delta = add(mul(error,power(mul(G,H),2)),scale(mul(mul(D,F),add(power(H,2),one,-1)),64))
    require(add(add(power(V1,2),scale(mul(mul(D,F),I),64),-1),delta,-1)=={}, 'exact auxiliary norm defect')
    e,o,v0,v1,K,a1 = vs
    a0 = add(add(power(v0,2),power(K,2),-1),one)
    theta = add(e,mul(o,add(v0,v1)),-1)
    inner = add(power(theta,2),mul(power(o,2),add(a0,scale(a1,64))),-1)
    resolved = add(add(power(e,2),scale(mul(mul(e,o),add(v0,v1)),2),-1),
        mul(power(o,2),add(add(add(power(K,2),one,-1),add(power(v1,2),scale(a1,64),-1)),scale(mul(v0,v1),2))))
    require(inner==resolved, 'exact cancellation-resolved inner norm')
    r = 4*2200-1; nu = 2*1162; W = 116; cap = 2*W+1; a = r+4*nu+2
    omega = 5*r+20*nu+cap+12; v0d = 4*r+12*nu+7
    dd = 2*a+2; kd = a+2; fd = 8*a+10; gd = 10*a+13; hd = 8*a+r+10
    delta_degree = dd+2*kd+2*gd+2*hd
    v1d = kd+2*dd+gd+hd
    require(delta_degree>dd+fd+2*hd, 'first auxiliary defect term dominates')
    inner_degree = 2*omega+delta_degree
    require(inner_degree>max(2*(a+4),a+4+omega+v1d,2*omega+v0d+v1d), 'unique dominant inner term')
    require(2*inner_degree>4*omega+2*v0d+2*v1d, 'final subtraction has smaller degree')
    degree = 104*r+400*nu+8*W+316
    require(2*inner_degree==degree==1845940, 'resolved exact degree')
    require(4*W+104*(2*2200-1)+400*1162==922760, 'diagonal leader base exponent')
    return {'exact_sparse_identities':3,'exact_degree':degree,'R_degree':r,'N_degree':nu,
            'diagonal_leading_coefficient':'2^186 * base_scale^922760 * threshold_scale^400 > 0',
            'scope':'Exact local cancellation identities, universal degree comparison and nonzero positive leader; source/finalizer degree propagation follows the retained ordinary proof.'}


def rejected(fn):
    try:fn()
    except ValueError:return True
    return False


def main():
    config = read('CONFIG.json'); provenance = read('PROVENANCE.json')
    for name, sha in provenance['inert_source_and_tuple_pins'].items():
        require(digest((ROOT/name).read_bytes())==sha, 'pinned source/tuple file '+name)
    require(digest((ROOT/'arithmetic.py').read_bytes())==provenance['adapted_builder_sha256'], 'adapted builder pin')
    code = read('data/H2082/layout.json'); kernels = read('data/H2082/kernels.json'); source = read('data/H2082/source.json')
    require(digest((ROOT/'data/H2082/source.json').read_bytes())==kernels['source_sha256']==code['source_sha256'], 'source pin')
    require(digest((ROOT/'data/H2082/layout.json').read_bytes())==kernels['code_sha256'], 'layout pin')
    ports, fixed = ports_and_fixed()
    report = {'status':'PASS','assertions_disabled':bool(sys.flags.optimize),
              'scope':'Finite arithmetic/source candidate; no native/compiler or object-language ZFC theorem.',
              'source_change':source_change(read('data/parent_source.json'),source),
              'extraction':extraction(code,kernels,source),
              'coefficient_bounds':coefficient_bounds(kernels,ports),
              'calibration':calibration(config),'degree':cancellation_identities(),'circuits':[]}
    rng = random.Random(208254); cases = 0; bodies = {}
    for domain in ['positive','natural']:
        obj = read('generated/gap2082_'+domain+'.json'); bodies[domain]=obj
        metrics = audit_object(obj,fixed,ports,config)
        for mod in [101,1009,1000003]:
            for trial in range(60):
                vals = {v:rng.randrange(0 if domain=='natural' else 1,200) for v in obj['variables']}
                got,named = evaluate(obj,vals,fixed,mod); want,registers = formula(obj,vals,ports,kernels,code,mod)
                require(got==want, 'independent direct output')
                for name,value in registers.items():require(named[name]==value,'independent register '+name)
                cases += 1
        metrics['sha256'] = digest((ROOT/'generated'/('gap2082_'+domain+'.json')).read_bytes())
        report['circuits'].append(metrics)
    bad = copy.deepcopy(kernels);bad['kernels'][0]['terms'][0]['coefficient'][0]['integer']+=1
    require(rejected(lambda:extraction(code,bad,source)), 'kernel mutation must fail mathematically')
    bad_cal = dict(config,block_scale_power_of_two=1)
    require(rejected(lambda:calibration(bad_cal)), 'old odd-kappa block factor must fail')
    bad_cal = dict(config,threshold_scale_exponent=6480185)
    require(rejected(lambda:calibration(bad_cal)), 'threshold mutation must fail')
    bad_fixed = dict(fixed);bad_fixed[next(iter(bodies['positive']['coefficient_recipes']))['name']]+=1
    require(rejected(lambda:audit_object(bodies['positive'],bad_fixed,ports,config)), 'coherently rehashed fixed value must fail its recipe')
    report['mathematical_negative_controls'] = 4
    report['modular_output_and_register_cases'] = cases
    report['tuple_raw_bytes'] = sum(r['bytes'] for r in read('coefficients/COEFFICIENT_BINDING.json')['ports'])
    report['fixed_leaves'] = len(fixed)
    require(read('HEIGHT_CERTIFICATE.json')==report['coefficient_bounds'], 'complete85-record height ledger')
    require(read('SOURCE_CERTIFICATE.json')=={'status':'PASS','source_change':report['source_change'],
            'extraction':report['extraction']}, 'source certificate ledger')
    require(read('generated/DEGREE_CERTIFICATE.json')==report['degree'], 'degree certificate ledger')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
