#!/usr/bin/env python3
"""Independent exact audit of integer polynomial witness transformations.

This file uses Python's standard library only and imports no construction,
optimization, or upstream audit code. Sparse substitution checks the complete
forward and backward polynomial identities; it is not a sampled-zero test.
"""
import argparse
import copy
import hashlib
import json
from collections import Counter
from math import gcd
from pathlib import Path


class BadCertificate(Exception):
    pass


def require(test, message):
    if not test:
        raise BadCertificate(message)


def sha_json(obj):
    return hashlib.sha256((json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n').encode()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


def polynomial(terms, n, bound=4):
    ans = Counter()
    for c, m in terms:
        require(type(c) is int and c != 0, 'invalid integer coefficient')
        require(len(m) <= bound, 'excess degree')
        require(all(type(i) is int and 0 <= i < n for i in m), 'invalid coordinate')
        ans[tuple(sorted(m))] += c
    return {m: c for m, c in ans.items() if c}


def add(a, b, scale=1):
    ans = dict(a)
    for m, c in b.items():
        ans[m] = ans.get(m, 0) + scale*c
    return {m: c for m, c in ans.items() if c}


def mul(a, b):
    ans = Counter()
    for u, c in a.items():
        for v, d in b.items():
            ans[tuple(sorted(u+v))] += c*d
    return {m: c for m, c in ans.items() if c}


def scale(a, k):
    return {m: c*k for m, c in a.items() if c*k}


def substitute(poly, maps):
    ans = {}
    for m, c in poly.items():
        term = {(): c}
        for i in m:
            term = mul(term, maps[i])
        ans = add(ans, term)
    return ans


def serial(poly):
    return [[c, list(m)] for m, c in sorted(poly.items())]


def equation_data(eq, residual_bound=2):
    require(eq.get('domain') == 'unrestricted integers', 'domain must be unrestricted integers')
    require(eq.get('polynomial') == 'sum(square(row) for row in residuals)', 'unsupported combiner')
    require(isinstance(eq.get('variables'), list) and eq['variables'], 'missing variables')
    n = len(eq['variables'])
    rows = [polynomial(r['terms'], n, residual_bound) for r in eq['residuals']]
    return n, rows


def radical_step(eq, cert):
    n, rows = equation_data(eq)
    require(sha_json(eq) == cert['input_sha256'], 'radical input hash mismatch')
    pivot, rownum = cert['pivot'], cert['deleted_row']
    require(type(pivot) is int and 0 <= pivot < n, 'bad pivot')
    require(type(rownum) is int and 0 <= rownum < len(rows), 'bad deleted row')
    v = dict(cert['direction'])
    require(len(v) == len(cert['direction']), 'duplicate direction coordinate')
    require(all(type(j) is int and 0 <= j < n and type(c) is int for j, c in v.items()), 'bad direction')
    require(v.get(pivot) == 1, 'direction pivot must be one')
    retained = [j for j in range(n) if j != pivot]
    require(retained == cert['retained_old_indices'], 'wrong retained coordinate list')
    require(eq['variables'][pivot]['name'] == cert['pivot_name'], 'wrong pivot name')
    slope = cert['slope']
    require(slope in (-1, 1), 'pivot slope must be a unit')
    old_to_new = {j: i for i, j in enumerate(retained)}

    # The coordinate section y has y_p=0.  Find the forced x_p polynomial.
    section = [{(old_to_new[j],): 1} if j != pivot else {} for j in range(n)]
    qr_section = substitute(rows[rownum], section)
    t = scale(qr_section, -slope)
    stated = polynomial(cert['sheared_pivot_solution'], n, 2)
    require(substitute(stated, section) == t, 'false restoration polynomial')
    require(all(pivot not in m for m in stated), 'restoration depends on eliminated coordinate')
    lift = [add(section[j], t, v.get(j, 0)) for j in range(n)]
    outputs_all = [substitute(q, lift) for q in rows]
    require(not outputs_all[rownum], 'eliminated row does not vanish after lift')
    require(all(len(m) <= 2 for out in outputs_all for m in out), 'lift increases residual degree')

    # Explicit inverse on the section: z_j=x_j-v_j*x_p.  Verify both
    # compositions symbolically, with the only source ideal term Q_r.
    projection = [add({(j,): 1}, {(pivot,): 1}, -v.get(j, 0)) for j in retained]
    require(all(substitute(z, lift) == {(i,): 1} for i, z in enumerate(projection)),
            'projection after lift is not identity')
    for j in range(n):
        expected = add({(j,): 1}, rows[rownum], -slope*v.get(j, 0))
        require(substitute(lift[j], projection) == expected,
                'lift after projection fails source-ideal identity')

    # Each source residual is its projected residual plus a constant
    # multiple of Q_r. This certifies the reverse implication, not just
    # the existence of a polynomial section.
    for i, q in enumerate(rows):
        directional_slope = sum(q.get((j,), 0)*c for j, c in v.items())
        expected = add(substitute(outputs_all[i], projection), rows[rownum], directional_slope*slope)
        require(q == expected, 'source residual reconstruction identity failed')

    out = copy.deepcopy(eq)
    out.pop('metrics', None)
    out['variables'] = [copy.deepcopy(eq['variables'][j]) for j in retained]
    for j in retained:
        if v.get(j):
            out['variables'][old_to_new[j]]['name'] = f'radical{n}.{j}'
    out['residuals'] = []
    for i, poly in enumerate(outputs_all):
        if i == rownum:
            continue
        r = copy.deepcopy(eq['residuals'][i])
        r['terms'] = serial(poly)
        out['residuals'].append(r)
    out['variant'] = eq.get('variant', '') + ':radical_projection'
    require(sha_json(out) == cert['output_sha256'], 'radical output hash mismatch')
    return out


def audit_radical(source, target_dir, negative_controls=True):
    source_eq = load(source)
    cert = load(Path(target_dir)/'projection_certificate.json')
    require(cert['schema'] == 'common_hessian_radical_projection_v1', 'wrong radical schema')
    current = source_eq
    for step in cert['steps']:
        current = radical_step(current, step)
    require(current == load(Path(target_dir)/'equation.json'), 'radical final equation differs')
    result = audit_metrics(target_dir)
    result['projection_steps'] = len(cert['steps'])
    result['source_file_sha256'] = hashlib.sha256(Path(source).read_bytes()).hexdigest()
    result['source_canonical_sha256'] = sha_json(source_eq)
    result['target_canonical_sha256'] = sha_json(current)
    if negative_controls:
        cases = []
        first = cert['steps'][0]
        c = copy.deepcopy(first); c['direction'][1][1] += 1; cases.append(('direction', source_eq, c))
        c = copy.deepcopy(first); c['slope'] *= -1; cases.append(('slope_sign', source_eq, c))
        c = copy.deepcopy(first); c['slope'] = 2; cases.append(('nonunit_slope', source_eq, c))
        c = copy.deepcopy(first); c['sheared_pivot_solution'][0][0] += 1; cases.append(('restoration', source_eq, c))
        c = copy.deepcopy(first); c['retained_old_indices'] = c['retained_old_indices'][::-1]; cases.append(('coordinate_order', source_eq, c))
        e = copy.deepcopy(source_eq); e['domain']='nonnegative integers'; c=copy.deepcopy(first);c['input_sha256']=sha_json(e);cases.append(('domain',e,c))
        e = copy.deepcopy(source_eq);e['residuals'][0]['terms'].append([1,[first['pivot'],first['pivot']]]);c=copy.deepcopy(first);c['input_sha256']=sha_json(e);cases.append(('quadratic_term_with_fresh_hash',e,c))
        rejected=[]
        for label,e,c in cases:
            try:
                radical_step(e,c)
            except BadCertificate:
                rejected.append(label)
            else:
                raise BadCertificate('corruption accepted: '+label)
        result['negative_controls_rejected']=rejected
    return result


def audit_metrics(target_dir, residual_bound=2):
    path = Path(target_dir)
    eq = load(path/'equation.json')
    n, rows = equation_data(eq, residual_bound)
    full = {}
    for r in rows:
        full = add(full, mul(r,r))
    disk = load(path/'expanded_polynomial.json')
    terms = disk['terms'] if isinstance(disk, dict) else disk
    require(polynomial(terms,n,2*residual_bound) == full, 'expanded polynomial coefficient mismatch')
    used = set(j for m in full for j in m)
    require(used == set(range(n)), 'declared variable absent from full polynomial')
    result = {'variables':n,'rows':len(rows),'degree':max(map(len,full)),
              'monomials':len(full),'height':max(map(abs,full.values())),
              'row_height':max(abs(c) for r in rows for c in r.values()),
              'residual_terms':sum(map(len,rows))}
    expected = load(path/('metrics.json' if (path/'metrics.json').exists() else 'METRICS.json'))
    aliases={'rows':'residuals','monomials':'collected_terms','height':'coefficient_height','row_height':'residual_height'}
    for k,v in result.items():
        if k in expected:
            require(expected[k] == v, 'metric mismatch: '+k)
        elif k in aliases and aliases[k] in expected:
            require(expected[aliases[k]] == v, 'metric mismatch: '+aliases[k])
    if 'maximum_residual_degree' in expected:
        require(expected['maximum_residual_degree']==max(len(m) for r in rows for m in r), 'residual degree mismatch')
    if 'all_coordinates_used' in expected:
        require(expected['all_coordinates_used'] is True,'invalid coordinate census')
    result['equation_file_sha256'] = hashlib.sha256((path/'equation.json').read_bytes()).hexdigest()
    result['full_expansion_checked']=True
    return result


def check_affine(source_eq,target,cert):
    n,rows=equation_data(source_eq);m,output_rows=equation_data(target)
    require(cert['schema']=='integral_affine_hyperplane_v1','wrong affine schema')
    require(n==cert['input_dimension'] and m==cert['output_dimension'] and m==n-1,'wrong affine dimensions')
    require(sha_json(source_eq)==cert['input_sha256'],'affine input hash mismatch')
    require(sha_json(target)==cert['output_sha256'],'affine output hash mismatch')
    combination=cert['row_combination']
    require(all(type(c) is int and c!=0 and type(i) is int and 0<=i<len(rows) for c,i in combination),'bad row combination')
    require(len({i for c,i in combination})==len(combination),'duplicate combination row')
    L={}
    for c,i in combination:L=add(L,rows[i],c)
    stated=polynomial(cert['affine_terms'],n,1)
    require(L==stated,'false affine consequence')
    nonzero_linear=[(mon,c) for mon,c in L.items() if len(mon)==1]
    require(nonzero_linear,'affine consequence has no variable')
    omitted=cert['omitted_row']
    require(omitted in {i for c,i in combination},'omitted row absent from consequence')
    lift=[polynomial(p,m,1) for p in cert['lift_old_from_new']]
    project=[polynomial(p,n,1) for p in cert['project_new_from_old']]
    require(len(lift)==n and len(project)==m,'wrong map dimensions')
    require(not substitute(L,lift),'lift does not land on affine hyperplane')
    for i in range(m):
        require(substitute(project[i],lift)=={(i,):1},'projection after affine lift fails')
    probe,coeff=nonzero_linear[0]
    for i in range(n):
        diff=add(substitute(lift[i],project),{(i,):1},-1)
        # No division is performed by a witness map. This coefficient
        # cross-product certifies diff is a rational multiple of L.
        require(scale(diff,coeff)==scale(L,diff.get(probe,0)),'affine inverse fails on hyperplane')
    expected=[substitute(q,lift) for i,q in enumerate(rows) if i!=omitted]
    require(expected==output_rows,'affine output coefficient mismatch')
    require([r['label'] for i,r in enumerate(source_eq['residuals']) if i!=omitted]==[r['label'] for r in target['residuals']], 'affine output row labels differ')
    require(all(len(mon)<=2 for q in expected for mon in q),'affine map increased residual degree')
    return True


def audit_affine(source,target_dir,negative_controls=True):
    source_eq=load(source);target=load(Path(target_dir)/'equation.json')
    cert=load(Path(target_dir)/'affine_lattice_certificate.json')
    check_affine(source_eq,target,cert)
    result=audit_metrics(target_dir)
    result['source_canonical_sha256']=sha_json(source_eq)
    result['target_canonical_sha256']=sha_json(target)
    result['exact_lift_projection_and_inverse_checked']=True
    result['source_row_combination_checked']=True
    if negative_controls:
        bad=[]
        c=copy.deepcopy(cert);c['row_combination'][0][0]+=1;bad.append(('row_combination',source_eq,target,c))
        c=copy.deepcopy(cert);c['affine_terms'][0][0]+=1;bad.append(('affine_identity',source_eq,target,c))
        c=copy.deepcopy(cert);c['lift_old_from_new'][0][0][0]+=1;bad.append(('lift_map',source_eq,target,c))
        c=copy.deepcopy(cert);c['project_new_from_old'][0][0][0]+=1;bad.append(('projection_map',source_eq,target,c))
        c=copy.deepcopy(cert);c['omitted_row']=next(i for i in range(len(source_eq['residuals'])) if i not in {j for _,j in c['row_combination']});bad.append(('wrong_omitted_row',source_eq,target,c))
        t=copy.deepcopy(target);t['residuals'][0]['terms'][0][0]+=1;c=copy.deepcopy(cert);c['output_sha256']=sha_json(t);bad.append(('target_coefficient_with_fresh_hash',source_eq,t,c))
        rejected=[]
        for label,e,t,c in bad:
            try:check_affine(e,t,c)
            except BadCertificate:rejected.append(label)
            else:raise BadCertificate('affine corruption accepted: '+label)
        result['negative_controls_rejected']=rejected
    return result


def check_unit_affine(source_eq,target,cert):
    n,rows=equation_data(source_eq);m,output_rows=equation_data(target)
    require(cert['schema']=='unit-affine-projection-v1','wrong unit-affine schema')
    pivot=cert['eliminated_coordinate'];omitted=cert['omitted_residual']
    require(type(pivot) is int and 0<=pivot<n and m==n-1,'invalid affine pivot')
    require(cert['eliminated_variable']==source_eq['variables'][pivot],'incorrect eliminated variable metadata')
    consequence=cert['affine_consequence'];combination=consequence['row_combination'];L={}
    require(all(type(c) is int and c!=0 and type(i) is int and 0<=i<len(rows) for c,i in combination),'invalid affine combination')
    for c,i in combination:L=add(L,rows[i],c)
    require(L==polynomial(consequence['affine_terms'],n,1),'unit-affine consequence is false')
    content=0
    for c in L.values():content=gcd(content,abs(c))
    require(content>0 and content==consequence['whole_content'],'wrong affine content')
    primitive={mon:c//content for mon,c in L.items()}
    a=primitive.get((pivot,),0)
    require(a in (-1,1),'unit-affine pivot not unit after content normalization')
    replacement=scale(add(primitive,{(pivot,):1},-a),-a)
    require(replacement==polynomial(cert['restoration_terms_original_indices'],n,1),'unit-affine restoration differs')
    retained=[j for j in range(n) if j!=pivot];rename={j:i for i,j in enumerate(retained)}
    require(target['variables']==[source_eq['variables'][j] for j in retained],'unit-affine variable order differs')
    lift=[]
    for j in range(n):
        lift.append({tuple(rename[k] for k in mon):c for mon,c in replacement.items()} if j==pivot else {(rename[j],):1})
    project=[{(j,):1} for j in retained]
    normalized={'schema':'integral_affine_hyperplane_v1','input_dimension':n,'output_dimension':m,
                'input_sha256':sha_json(source_eq),'output_sha256':sha_json(target),
                'row_combination':combination,'affine_terms':serial(L),'omitted_row':omitted,
                'lift_old_from_new':[serial(p) for p in lift],
                'project_new_from_old':[serial(p) for p in project]}
    check_affine(source_eq,target,normalized)
    return True


def audit_unit_affine(source,target_dir,negative_controls=True):
    source_eq=load(source);target=load(Path(target_dir)/'equation.json');cert=load(Path(target_dir)/'projection_certificate.json')
    require(hashlib.sha256(Path(source).read_bytes()).hexdigest()==cert['input_sha256'],'unit-affine raw input hash mismatch')
    require(hashlib.sha256((Path(target_dir)/'equation.json').read_bytes()).hexdigest()==cert['output_sha256'],'unit-affine raw output hash mismatch')
    check_unit_affine(source_eq,target,cert)
    result=audit_metrics(target_dir);result['exact_unit_affine_maps_checked']=True
    result['source_canonical_sha256']=sha_json(source_eq);result['target_canonical_sha256']=sha_json(target)
    if negative_controls:
        bad=[]
        c=copy.deepcopy(cert);c['affine_consequence']['row_combination'][0][0]+=1;bad.append(('row_combination',source_eq,target,c))
        c=copy.deepcopy(cert);c['affine_consequence']['whole_content']*=2;bad.append(('nonunit_content',source_eq,target,c))
        c=copy.deepcopy(cert);c['restoration_terms_original_indices'][0][0]+=1;bad.append(('restoration',source_eq,target,c))
        c=copy.deepcopy(cert);c['omitted_residual']=next(i for i in range(len(source_eq['residuals'])) if i not in {j for _,j in c['affine_consequence']['row_combination']});bad.append(('wrong_omitted_row',source_eq,target,c))
        t=copy.deepcopy(target);t['residuals'][0]['terms'][0][0]+=1;bad.append(('target_coefficient',source_eq,t,cert))
        rejected=[]
        for label,e,t,c in bad:
            try:check_unit_affine(e,t,c)
            except BadCertificate:rejected.append(label)
            else:raise BadCertificate('unit-affine corruption accepted: '+label)
        result['negative_controls_rejected']=rejected
    return result


def check_reciprocal(source_eq,target,cert):
    n,rows=equation_data(source_eq);m,output_rows=equation_data(target,5)
    require(cert['schema']=='reciprocal-pooling-certificate-v1','wrong reciprocal schema')
    require(sha_json(source_eq)==cert['input_sha256'],'reciprocal input hash mismatch')
    require(sha_json(target)==cert['output_sha256'],'reciprocal output hash mismatch')
    require(n-3==m and len(output_rows)==len(rows)-3,'wrong reciprocal dimensions')
    names=[v['name'] for v in source_eq['variables']]
    labels=[r['label'] for r in source_eq['residuals']]
    groups=cert['groups']
    require(len(groups)==2 and [g['group'] for g in groups]==['radix','radix_plus_one'],'wrong pool groups')
    removed_vars=set();removed_rows=set();Es=[];Ts=[];bases=[];two_As=[]
    for g in groups:
        name=g['group'];K=g['K'];L=g['L'];ia=g['aggregate_row'];ib=g['norm_row']
        require(names[K]==name+'.K' and names[L]==name+'.L','wrong private coordinate labels')
        require(labels[ia]==name+'.bilinear_aggregate' and labels[ib]==name+'.pooled_norm','wrong pool row labels')
        require(K!=L and ia!=ib,'overlapping pool labels')
        base=polynomial(g['base'],n,1);a=polynomial(g['a'],n,1)
        E=polynomial(g['E'],n,3);T=polynomial(g['T'],n,2)
        ar,br=rows[ia],rows[ib]
        ar0={mon:c for mon,c in ar.items() if K not in mon and L not in mon}
        br0={mon:c for mon,c in br.items() if K not in mon and L not in mon}
        require(ar==add(add({(K,):1},mul(a,{(L,):1})),ar0),'wrong aggregate row structure')
        require(br==add(add(br0,mul(base,{(K,):1}),-1),{(L,):1}),'wrong pool norm structure')
        require(E==add(br0,mul(base,ar0)),'wrong error numerator')
        twoA=add(base,a,-1)
        derivedT=add(add(mul(twoA,base),mul(base,base),-1),{():-1})
        require(T==derivedT,'wrong Pell modulus')
        require(add(E,mul(T,{(L,):1}),-1)==add(br,mul(base,ar)),'pool elimination identity failed')
        require(all(K not in mon and L not in mon for poly in [base,a,E,T] for mon in poly),'private coordinates retained in pool formulas')
        Es.append(E);Ts.append(T);bases.append(base);two_As.append(twoA)
        removed_vars.update((K,L));removed_rows.update((ia,ib))
    require(len(removed_vars)==4 and len(removed_rows)==4,'overlapping pools')
    require(sorted(removed_vars)==cert['removed_variables'] and sorted(removed_rows)==cert['removed_rows'],'wrong deleted-coordinate or row list')
    for i,q in enumerate(rows):
        if i not in removed_rows:require(all(not(set(mon)&removed_vars) for mon in q),'private coordinate occurs outside pools')
    for g in groups:
        other=removed_vars-{g['K'],g['L']}
        require(all(not(set(mon)&other) for i in [g['aggregate_row'],g['norm_row']] for mon in rows[i]),'pools have cross-private coordinates')
    require(add(bases[1],bases[0],-1)=={():1},'pool bases are not consecutive')
    require(two_As[0]==two_As[1]==polynomial(cert['two_A_original'],n,1),'Pell parameters are not shared')
    require(cert['new_variable_original_index']==n,'wrong new coordinate placement')
    new=add(add(mul(Es[0],Ts[1]),mul(Es[1],Ts[0])),mul({(n,):1},mul(Ts[0],Ts[1])),-1)
    require(new==polynomial(cert['new_residual_original_indices'],n+1,5),'wrong reciprocal residual')
    retained=[j for j in range(n) if j not in removed_vars]
    require(retained==cert['retained_old_indices'],'wrong reciprocal coordinate order')
    rename={j:k for k,j in enumerate(retained)};rename[n]=len(retained)
    def ren(q):return {tuple(rename[j] for j in mon):c for mon,c in q.items()}
    expected=[ren(q) for i,q in enumerate(rows) if i not in removed_rows]+[ren(new)]
    require(expected==output_rows,'reciprocal output coefficient mismatch')
    require(target['variables'][:-1]==[source_eq['variables'][j] for j in retained] and target['variables'][-1]['name']=='reciprocal.z','reciprocal variable metadata mismatch')
    require([r['label'] for i,r in enumerate(source_eq['residuals']) if i not in removed_rows]+['reciprocal.consecutive_bases']==[r['label'] for r in target['residuals']],'reciprocal residual labels mismatch')
    return True


def audit_reciprocal(source,target_dir,negative_controls=True):
    source_eq=load(source);target=load(Path(target_dir)/'equation.json');cert=load(Path(target_dir)/'certificate.json')
    check_reciprocal(source_eq,target,cert)
    result=audit_metrics(target_dir,5)
    result['source_canonical_sha256']=sha_json(source_eq)
    result['target_canonical_sha256']=sha_json(target)
    result['exact_pool_elimination_and_compilation_checked']=True
    result['scope']='Finite polynomial identities only; equivalence of zero existence additionally uses the reciprocal-pooling arithmetic theorem and inherited Pell-frame calibration.'
    if negative_controls:
        bad=[]
        for key in ['E','T','base','a']:
            c=copy.deepcopy(cert);c['groups'][0][key][0][0]+=1;bad.append((key,source_eq,target,c))
        c=copy.deepcopy(cert);c['retained_old_indices'][0:2]=c['retained_old_indices'][1::-1];bad.append(('coordinate_order',source_eq,target,c))
        t=copy.deepcopy(target);t['residuals'][-1]['terms'][0][0]+=1;c=copy.deepcopy(cert);c['output_sha256']=sha_json(t);bad.append(('target_with_fresh_hash',source_eq,t,c))
        e=copy.deepcopy(source_eq);e['residuals'][0]['terms'].append([1,[cert['groups'][0]['K']]]);c=copy.deepcopy(cert);c['input_sha256']=sha_json(e);bad.append(('nonprivate_coordinate_with_fresh_hash',e,target,c))
        rejected=[]
        for label,e,t,c in bad:
            try:check_reciprocal(e,t,c)
            except BadCertificate:rejected.append(label)
            else:raise BadCertificate('reciprocal corruption accepted: '+label)
        result['negative_controls_rejected']=rejected
    return result


def audit_rows(source, target_dir):
    source_eq=load(source);n,rows=equation_data(source_eq)
    cert=load(Path(target_dir)/'row_certificate.json')
    require(sha_json(source_eq)==cert['input_sha256'],'row input hash mismatch')
    initial=copy.deepcopy(rows)
    for dst,src,k in cert['operations']:
        require(type(dst) is int and type(src) is int and 0<=dst<len(rows) and 0<=src<len(rows) and dst!=src,'invalid row operation')
        require(type(k) is int,'noninteger row multiplier')
        rows[dst]=add(rows[dst],rows[src],k)
    target=load(Path(target_dir)/'equation.json');n2,final=equation_data(target)
    require(n==n2 and source_eq['variables']==target['variables'],'row operation changed variables')
    require(rows==final,'row output coefficient mismatch')
    require(sha_json(target)==cert['output_sha256'],'row output hash mismatch')
    for dst,src,k in reversed(cert['operations']):
        rows[dst]=add(rows[dst],rows[src],-k)
    require(rows==initial,'inverse row sequence failed')
    result=audit_metrics(target_dir);result['integer_row_operations']=len(cert['operations']);result['inverse_row_operations_checked']=True
    protection_path=Path(target_dir)/'protection.json'
    if protection_path.exists():
        protection=load(protection_path)
        expected_labels={g+'.'+suffix for g in ['radix','radix_plus_one'] for suffix in ['bilinear_aggregate','pooled_norm']}
        protected={i for i,r in enumerate(source_eq['residuals']) if r['label'] in expected_labels}
        require(len(protected)==4,'not four protected pool rows')
        require(sorted(protected)==protection['protected_rows'],'wrong protected row list')
        require(all(dst not in protected and src not in protected for dst,src,k in cert['operations']),'row sequence touches a pool row')
        require(all(source_eq['residuals'][i]==target['residuals'][i] for i in protected),'protected pool row changed')
        expected_names={g+'.'+suffix for g in ['radix','radix_plus_one'] for suffix in ['K','L']}
        private={i for i,v in enumerate(source_eq['variables']) if v['name'] in expected_names}
        require(len(private)==4 and sorted(private)==protection['protected_variables'],'wrong protected variable list')
        require(protection['retained_operations']==len(cert['operations']),'wrong protection operation count')
        result['protected_pool_rows_unchanged']=True
        result['no_pool_row_used_as_source_or_target']=True
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument('source');parser.add_argument('target_dir');parser.add_argument('--mode',choices=['radical','rows','affine','unit_affine','reciprocal','metrics'],default='radical');parser.add_argument('--output')
    a=parser.parse_args()
    if a.mode=='radical':result=audit_radical(a.source,a.target_dir)
    elif a.mode=='rows':result=audit_rows(a.source,a.target_dir)
    elif a.mode=='affine':result=audit_affine(a.source,a.target_dir)
    elif a.mode=='unit_affine':result=audit_unit_affine(a.source,a.target_dir)
    elif a.mode=='reciprocal':result=audit_reciprocal(a.source,a.target_dir)
    else:result=audit_metrics(a.target_dir)
    text=json.dumps({'status':'PASS','method':'independent exact sparse polynomial identities','result':result},indent=2,sort_keys=True)+'\n'
    if a.output:Path(a.output).write_text(text)
    print(text,end='')


if __name__=='__main__':
    main()
