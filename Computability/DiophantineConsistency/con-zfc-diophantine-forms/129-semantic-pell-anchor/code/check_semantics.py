#!/usr/bin/env python3
"""Independent local semantic-row audit; imports no equation producer.

This checks finite algebraic bindings of the combined Pell-cap compiler.
The unbounded mathematical proof is supplied separately.
"""
from pathlib import Path
from functools import lru_cache
import argparse
import copy
import hashlib
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(*polys):
    result = {}
    for p in polys:
        for m, c in p.items():
            result[m] = result.get(m, 0) + c
    return {m: c for m, c in result.items() if c}


def scale(p, c):
    return {m: c*v for m, v in p.items() if c*v}


def mul(p, q):
    result = {}
    for m, c in p.items():
        for n, d in q.items():
            mn = tuple(sorted(m+n))
            result[mn] = result.get(mn, 0) + c*d
    return {m: c for m, c in result.items() if c}


def atom(a):
    kind, value = a
    if kind == 'c':
        return {(): value} if value else {}
    require(kind == 'v', 'unknown atom kind')
    return {(value,): 1}


def sq(p):
    return mul(p, p)


C1 = {(): 1}


class Audit:
    def __init__(self, meta):
        self.m = meta
        self.rows = meta['rows']
        self.gates = {int(k): v for k, v in meta['gates'].items()}
        self.by_name = {}
        for i, v in enumerate(meta['variables']):
            require(v['name'] not in self.by_name, 'duplicate variable name')
            self.by_name[v['name']] = ['v', i]
        self.by_label = {}
        for r in self.rows:
            if r['gate'] is None:
                require(r['label'] not in self.by_label, 'duplicate semantic label')
                self.by_label[r['label']] = r
        for v, j in self.gates.items():
            r = self.rows[j]
            require(r['gate'] == v, 'gate index disagrees with defining row')
            p = self.literal(r)
            require(p.get((v,)) == 1, 'gate is not monic')
            for monomial in p:
                if monomial != (v,):
                    require(all(i < v for i in monomial), 'gate dependency is not earlier')
        self.checked = []

    @staticmethod
    def literal(row):
        return add(*[{tuple(sorted(m)): c} for c, m in row['terms']])

    def named(self, name):
        require(name in self.by_name, 'missing variable '+name)
        return self.by_name[name]

    def expansion(self, stop):
        stop = frozenset(a[1] for a in stop if a[0] == 'v')

        @lru_cache(None)
        def coordinate(v):
            if v in stop or v not in self.gates:
                return {(v,): 1}
            p = self.literal(self.rows[self.gates[v]])
            p.pop((v,))
            return scale(polynomial(p), -1)

        def polynomial(p):
            terms = []
            for monomial, coefficient in p.items():
                term = {(): coefficient}
                for v in monomial:
                    term = mul(term, coordinate(v))
                terms.append(term)
            return add(*terms)

        return coordinate, polynomial

    def check_row(self, label, expected, stop):
        require(label in self.by_label, 'missing semantic row '+label)
        _, expand = self.expansion(stop)
        actual = expand(self.literal(self.by_label[label]))
        require(actual == expected or actual == scale(expected, -1),
                'row mismatch: '+label)
        self.checked.append(label)

    def check_atom(self, label, expression, expected, stop):
        coord, _ = self.expansion(stop)
        actual = atom(expression) if expression[0] == 'c' else coord(expression[1])
        require(actual == expected, 'atom mismatch: '+label)
        self.checked.append(label)

    def run(self):
        m = self.m
        cap = m['cap']
        W, A, Z = m['scale']
        H = cap['index']
        semantic_anchor = m.get('semantic_anchor', False)
        L = m['lower_A']
        X, Y = cap['pair']
        U, V, B = cap['auxiliary']
        S, R = cap['comparison']
        require(A == cap['base'], 'anchor parameters disagree')
        require(H == (m['amplification']['derived_label_sum'] if semantic_anchor else W),
                'anchor index is not the specified semantic atom')
        sigma, zm1 = self.named('shared.A_slack'), self.named('shared.Zminus1')
        self.check_atom('split lower scale', A, add(atom(L), atom(sigma)), [L, sigma])
        self.check_atom('positive lower ordinate multiplier', Z, add(C1, atom(zm1)), [zm1])
        wl = mul(atom(W), atom(Z))
        self.check_row('shared.last_norm_lower',
                       add(sq(atom(L)), sq(wl), scale(mul(sq(add(atom(W), C1)), sq(wl)), -1), scale(C1, -1)),
                       [W, L, Z])
        for label, base, x, y in [('index_cap.norm1', A, X, Y),
                                  ('index_cap.norm2', A, U, V),
                                  ('index_cap.norm3', B, S, R)]:
            expected = add(sq(atom(x)), sq(atom(y)), scale(mul(sq(atom(base)), sq(atom(y))), -1), scale(C1, -1))
            self.check_row(label, expected, [base, x, y])
        d = self.named('index_cap.q4minus1')
        self.check_atom('anchor B definition', B,
                       add(C1, scale(mul(atom(Y), add(atom(d), C1)), 4)), [Y, d])
        e = self.named('index_cap.Vquotient_minus1')
        self.check_row('index_cap.V_positive_multiple',
                       add(atom(V), scale(mul(sq(atom(Y)), add(atom(e), C1)), -1)), [V, Y, e])
        for label, left, constant, multiplier, qname, factor in [
            ('index_cap.B_mod_U', B, A, U, 'index_cap.Bquotient', 1),
            ('index_cap.S_mod_U', S, X, U, 'index_cap.Squotient', 1),
            ('index_cap.R_mod_4Y', R, H, Y, 'index_cap.Rquotient', 4),
        ]:
            q = self.named(qname)
            expected = add(atom(left), scale(atom(constant), -1), scale(mul(atom(multiplier), atom(q)), -factor))
            self.check_row(label, expected, [left, constant, multiplier, q])

        seeds = m['seed_certificates']
        require(len({tuple(s['index']) for s in seeds}) == len(seeds), 'duplicate seed index')
        by_index = {tuple(s['index']): s for s in seeds}
        if semantic_anchor:
            require(tuple(H) not in by_index, 'anchor was duplicated as an independent seed')
            by_index[tuple(H)] = dict(index=H, first=X, ordinate=Y, kind='standard')
        required = {tuple(p['exponent']) for p in m['powers']} | {tuple(r['n']) for r in m['modular_requests']}
        require(required == set(by_index), 'seed family does not equal request indices')
        require(len(seeds) == (14 if semantic_anchor else 15) and len(m['powers']) == 6 and len(m['modular_requests']) == 11,
                'unexpected source request cardinalities')
        for s in seeds:
            first, y = s['first'], s['ordinate']
            if m['coordinates'] == 'standard':
                expected = add(sq(atom(first)), sq(atom(y)), scale(mul(sq(atom(A)), sq(atom(y))), -1), scale(C1, -1))
            else:
                expected = add(sq(atom(first)), sq(atom(y)), scale(mul(atom(A), mul(atom(first), atom(y))), -2), scale(C1, -1))
            self.check_row(s['label'], expected, [A, first, y])

        cb, cr = m['cap_bound'], m['cap_residue']
        require(cb['ordinates'] == [s['ordinate'] for s in seeds], 'aggregate seed order mismatch')
        require(cr['seeds'] == [{'exponent':s['index'], 'pair':[s['first'],s['ordinate']]} for s in seeds],
                'pooled seed identity mismatch')
        slack, quotient = cb['slack'], cr['quotient']
        self.check_row(cb['row_label'],
                       add(atom(Y), scale(atom(H), -1), scale(C1, -1), scale(atom(slack), -1),
                           *[scale(atom(s['ordinate']), -1) for s in seeds]),
                       [Y, H, slack]+[s['ordinate'] for s in seeds])
        expected = add(*[sq(add(atom(s['ordinate']), scale(atom(s['index']), -1))) for s in seeds],
                       scale(mul(atom(A),atom(quotient)), -1), atom(quotient))
        self.check_row(cr['row_label'], expected,
                       [A, quotient]+[a for s in seeds for a in [s['ordinate'],s['index']]])

        frame = m['frame']
        atoms = {tuple(a) for p in m['powers'] for a in [p['base'],p['exponent'],p['output']]}
        atoms |= {tuple(r['n']) for r in m['modular_requests']}
        actual_atoms = {tuple(a) for a in frame['atoms']}
        optional_atom = tuple(m['radix']['root_base'])
        require(actual_atoms == atoms or actual_atoms == atoms | {optional_atom},
                'frame omits/adds semantic atoms')
        require(frame['offset'] == len(seeds)+2, 'frame seed-count offset mismatch')
        require(tuple(m['radix']['radix']) in actual_atoms and frame['offset']>=2,
                'cannot derive q+1<W from frame')
        self.check_row('shared.frame_definition',
                       add(atom(W), {():-frame['offset']}, *[scale(atom(a), -1) for a in frame['atoms']]),
                       [W]+frame['atoms'])
        require(all(a[1] < W[1] for a in frame['atoms'] if a[0]=='v'),
                'frame depends on private scale or cap witness')

        q, qb, N = [m['radix'][k] for k in ['radix','root_base','modulus']]
        t, F, K, radius, product_B = [m['amplification'][k] for k in ['t','F','K','R','B']]
        x, y = self.named('x'), self.named('y')
        t0, b0 = self.named('t0'), self.named('reciprocal.Bminus2')
        self.check_atom('horizon', t, add(atom(t0),{():16}), [t0])
        self.check_atom('positive product coordinate',product_B,add(atom(b0),{():2}),[b0])
        self.check_atom('amplification radius',radius,add({():2},atom(t),atom(F),atom(x),atom(y)),[t,F,x,y])
        self.check_atom('amplification index',K,scale(atom(radius),2),[radius])
        require(len(m['factorials'])==len(m['binomials'])==1, 'factorial/binomial not merged')
        factorial, binomial = m['factorials'][0],m['binomials'][0]
        require(factorial['input']==t and factorial['output']==F and factorial['binomial']==product_B,
                'factorial semantic ports mismatch')
        require(binomial['k']==t and binomial['output']==product_B,'exact binomial ports mismatch')
        self.check_atom('factorial squared radius',factorial['radius'],sq(atom(F)),[F])
        self.check_atom('exact binomial top',binomial['n'],add(sq(atom(F)),atom(t)),[F,t])
        p0,p1,p2,p3,p4,p5=m['powers']
        require(p0['exponent']==t and p0['output']==factorial['numerator'],'factorial power ports mismatch')
        self.check_atom('factorial power base',p0['base'],add(sq(atom(F)),C1),[F])
        require(p1['base']==product_B and p1['exponent']==K and p1['output']==N,'first amplification power mismatch')
        require(p2['base']==N and p2['exponent']==K and p2['output']==q,'radix power mismatch')
        require(p3['base']==q and p3['exponent']==t,'t denominator mismatch')
        require(p4['base']==q and p5['base']==q,'large denominator bases mismatch')
        self.check_atom('y denominator index',p4['exponent'],add(atom(y),C1),[y])
        self.check_atom('x denominator index',p5['exponent'],add(atom(x),C1),[x])
        vr,rem,fslack=factorial['numerator'],factorial['remainder'],factorial['slack']
        self.check_row('fact0.ceiling',add(atom(vr),atom(product_B),scale(mul(atom(product_B),atom(F)),-1),scale(atom(rem),-1),scale(C1,-1)),[vr,product_B,F,rem])
        self.check_row('fact0.remainder_bound',add(atom(product_B),scale(atom(rem),-1),scale(atom(fslack),-1),scale(C1,-1)),[product_B,rem,fslack])
        u0,r0,ut=[self.named(k) for k in ['endpoint.u0','endpoint.r0','endpoint.ut']]
        self.check_row('endpoint.first_quotient',add(atom(x),scale(atom(F),-1),scale(C1,-1),scale(mul(add(atom(y),C1),atom(u0)),-1)),[x,F,y,u0])
        self.check_row('endpoint.first_remainder',add(atom(y),scale(atom(F),-1),scale(C1,-1),scale(atom(r0),-1)),[y,F,r0])
        self.check_row('endpoint.last_quotient',add(atom(x),scale(C1,-1),scale(mul(add(C1,mul(add(atom(t),C1),atom(y))),atom(ut)),-1)),[x,t,y,ut])
        aggregate_records=[r for r in m['ranges'] if r[3]!='crt.range.derived_label_sum']
        require(len(aggregate_records)==m['radix']['aggregate_count']==9,'aggregate request count mismatch')
        aggregate_factor=10 if semantic_anchor else 9
        if semantic_anchor:
            require(m['radix']['aggregate_factor']==10,'shifted CRT aggregate coefficient mismatch')
        aggregate_slack=m['radix']['aggregate_slack']
        self.check_row('crt.aggregate_representative_bound',add(scale(sq(atom(N)),aggregate_factor),
                       scale(atom(aggregate_slack),-1),*[scale(atom(r[0]),-1) for r in aggregate_records]),
                       [N,aggregate_slack]+[r[0] for r in aggregate_records])
        root, h0 = m['radix']['root_modulus'], m['radix']['root_quotient']
        self.check_atom('modular base', qb, add(atom(q),C1), [q])
        self.check_row('modular.common_root',
                       add(scale(mul(atom(A),atom(qb)), 2), scale(sq(atom(qb)), -1),
                           scale(C1,-1), scale(mul(atom(root),atom(h0)),-1)), [A,qb,root,h0])
        if m['dominant_modulus']:
            dx = m['radix']['dominant_denominator']
            require(dx==p5['output'],'dominant denominator is not q^(x+1)')
            self.check_atom('dominant root modulus', root, mul(atom(N),atom(dx)), [N,dx])
        else:
            denoms = m['radix']['root_denominators']
            expected = atom(q)
            for d in denoms:
                expected = mul(expected,atom(d))
            self.check_atom('product root modulus',root,expected,[q]+denoms)

        def representative(seed, base):
            first,y = seed['first'],seed['ordinate']
            if seed['kind'] == 'standard':
                return add(atom(first),mul(atom(base),atom(y)),scale(mul(atom(A),atom(y)),-1))
            return add(mul(atom(base),atom(y)),scale(atom(first),-1))

        for i,p in enumerate(m['powers']):
            seed = by_index[tuple(p['exponent'])]
            quotient = self.named('pow'+str(i)+'.quotient')
            n = p['base']
            # The T coordinate is the only non-gate witness other than the
            # named quotient remaining after local graph expansion.
            candidates = [(name,a) for name,a in self.by_name.items() if name.startswith('base') and name.endswith('.T')]
            match = []
            for name,T in candidates:
                label=name[:-2]+'.T_definition'
                expected=add(atom(T),scale(mul(atom(A),atom(n)),-2),sq(atom(n)),C1)
                try:
                    self.check_row(label,expected,[T,A,n])
                except ValueError:
                    continue
                match.append(T)
            require(len(match)==1,'exact-power base modulus mismatch')
            T=match[0]
            expected=add(representative(seed,n),scale(atom(p['output']),-1),scale(mul(atom(T),atom(quotient)),-1))
            self.check_row('pow'+str(i)+'.power_congruence',expected,
                           [A,n,p['output'],T,quotient,seed['first'],seed['ordinate']])

        for request in m['modular_requests']:
            seed = by_index[tuple(request['n'])]
            require(request['pair']==[seed['first'],seed['ordinate']], 'modular request uses wrong pair')
            den,r,rs,quotient,modulus = [request[k] for k in ['den','remainder','remainder_slack','quotient','modulus']]
            residue=atom(r)
            stops=[A,qb,den,r,rs,quotient,modulus,seed['first'],seed['ordinate']]
            if request['kind']=='exact':
                residue=add(residue,mul(atom(den),atom(request['output'])))
                stops.append(request['output'])
                os=self.named(request['label']+'.modular_oslack')
                self.check_row(request['label']+'.digit_bound',
                               add(atom(q),scale(atom(request['output']),-1),scale(atom(os),-1),scale(C1,-1)),
                               [q,request['output'],os])
            self.check_atom(request['label']+' modulus',modulus,
                           mul(atom(den),atom(q if request['kind']=='exact' else N)),
                           [den,q if request['kind']=='exact' else N])
            self.check_row(request['label']+'.modular_digit',
                           add(representative(seed,qb),scale(residue,-1),scale(mul(atom(modulus),atom(quotient)),-1)),stops)
            self.check_row(request['label']+'.remainder_bound',
                           add(atom(den),scale(atom(r),-1),scale(atom(rs),-1),scale(C1,-1)),[den,r,rs])
        return {'verified':True,'coordinates':m['coordinates'],'dominant_modulus':m['dominant_modulus'],'semantic_anchor':semantic_anchor,
                'seeds':len(seeds),'exact_powers':len(m['powers']),'modular_requests':len(m['modular_requests']),
                'checked_local_identities':len(self.checked),'checked_labels':self.checked}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('semantic',type=Path)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--negative-controls',action='store_true')
    parser.add_argument('--parent-semantic',type=Path)
    args=parser.parse_args()
    data=args.semantic.read_bytes()
    meta=json.loads(data)
    result=Audit(meta).run()
    if args.parent_semantic:
        parent_bytes=args.parent_semantic.read_bytes()
        parent=json.loads(parent_bytes)
        endpoint=next(i for i,r in enumerate(parent['rows']) if r['label']=='modular.common_root')
        allowed=set()
        if meta.get('semantic_anchor',False):
            allowed.add('crt.aggregate_representative_bound')
        if meta['dominant_modulus']:
            allowed.add('modular.common_root')
        changed=[]
        for i in range(endpoint+1):
            old,new=parent['rows'][i],meta['rows'][i]
            if old!=new:
                require(old['label'] in allowed and old['label']==new['label'] and old['gate'] is None,
                        'unlicensed change to inherited semantic source row')
                changed.append(old['label'])
        require(set(changed)==allowed,'expected source transformations are not exactly present')
        last=max(v for r in parent['rows'][:endpoint+1] for c,monomial in r['terms'] for v in monomial)
        require(parent['variables'][:last+1]==meta['variables'][:last+1],
                'inherited semantic source variable prefix changed')
        fields=['powers','factorials','binomials','ranges','product','amplification',
                'local_majorant','syntax','local_names','denominator_derivations']
        for field in fields:
            require(parent[field]==meta[field],'inherited source metadata changed: '+field)
        result['parent_binding']={'parent_sha256':hashlib.sha256(parent_bytes).hexdigest(),
            'source_prefix_rows':endpoint+1,'source_prefix_variables':last+1,
            'explicitly_reviewed_row_changes':changed,'identical_metadata_fields':fields}
    if args.negative_controls:
        controls=[]

        def reject(name, change):
            altered=copy.deepcopy(meta)
            change(altered)
            try:
                Audit(altered).run()
            except (ValueError,KeyError) as error:
                controls.append({'name':name,'rejected':True,'reason':str(error)})
            else:
                raise ValueError('negative control was accepted: '+name)

        def bad_pooled_row(m):
            row=next(r for r in m['rows'] if r['label']=='index_cap.squared_index_errors')
            row['terms'][0][0]+=1

        def bad_anchor_norm(m):
            row=next(r for r in m['rows'] if r['label']=='index_cap.norm2')
            row['terms'][0][0]+=1

        def bad_modular_pair(m):
            m['modular_requests'][0]['pair']=m['modular_requests'][1]['pair']

        def omitted_modular_index(m):
            target=m['modular_requests'][-1]['n']
            m['frame']['atoms']=[a for a in m['frame']['atoms'] if a!=target]

        def bad_aggregate_row(m):
            row=next(r for r in m['rows'] if r['label']=='crt.aggregate_representative_bound')
            row['terms'][0][0]+=1

        for name,change in [('pooled coefficient changed',bad_pooled_row),
                            ('anchor auxiliary norm changed',bad_anchor_norm),
                            ('modular request uses another index',bad_modular_pair),
                            ('modular upper index omitted from frame',omitted_modular_index),
                            ('aggregate bound changed',bad_aggregate_row)]:
            reject(name,change)
        result['negative_controls']=controls
    result['input_sha256']=hashlib.sha256(data).hexdigest()
    result['scope']='exact local semantic bindings; not an unbounded arithmetic or logical proof'
    text=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text)


if __name__=='__main__':
    main()
