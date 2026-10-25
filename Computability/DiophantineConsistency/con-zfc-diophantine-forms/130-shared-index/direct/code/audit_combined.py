#!/usr/bin/env python3
"""Independent exact boundary audit of the common-cap/binomial composition.

This checker does not import the builder or contraction code. It checks the
literal uncontracted arithmetic boundary supporting the ordinary proof.
It is not a proof of the inherited C222/ZFC calibration.
"""
import argparse
from collections import defaultdict
from functools import lru_cache
import hashlib
import json
from pathlib import Path


def add(*polys):
    out = defaultdict(int)
    for p in polys:
        for m, c in p.items():
            out[m] += c
    return {m: c for m, c in out.items() if c}


def scale(p, n):
    return {m: n*c for m, c in p.items() if n*c}


def mul(p, q):
    out = defaultdict(int)
    for a, c in p.items():
        for b, d in q.items():
            out[tuple(sorted(a+b))] += c*d
    return {m: c for m, c in out.items() if c}


def var(i):
    return {(i,): 1}


def con(n):
    return {(): n} if n else {}


def neg(p):
    return scale(p, -1)


def square(p):
    return mul(p, p)


def audit(path, parent, self_radix=False):
    raw_bytes = path.read_bytes()
    data = json.loads(raw_bytes)
    old = json.loads(parent.read_bytes())
    rows = data['rows']
    by_label = {}
    for row in rows:
        by_label.setdefault(row['label'], []).append(row)
    gate_rows = {int(v): rows[i] for v, i in data['gates'].items()}
    names = {v['name']: i for i, v in enumerate(data['variables'])}
    checks = []

    def check(name, condition):
        if not condition:
            raise ValueError('FAILED: ' + name)
        checks.append(name)

    def idx(atom):
        if atom[0] != 'v':
            raise ValueError('expected coordinate atom')
        return atom[1]

    def gate_rhs(i):
        row = gate_rows[i]
        own = [c for c, m in row['terms'] if m == [i]]
        if own != [1] or any(i in m for c, m in row['terms'] if m != [i]):
            raise ValueError('non-monic gate in audited boundary')
        return [( -c, m) for c, m in row['terms'] if m != [i]]

    def expand_terms(terms, cut):
        @lru_cache(None)
        def expand_var(i):
            if i in cut or i not in gate_rows:
                return var(i)
            return expand_list(gate_rhs(i))
        def expand_list(ts):
            summands = []
            for c, m in ts:
                p = con(c)
                for i in m:
                    p = mul(p, expand_var(i))
                summands.append(p)
            return add(*summands)
        return expand_list(terms)

    def row_eq(label, expected, cut):
        rr = by_label.get(label, [])
        check('unique row: ' + label, len(rr) == 1)
        check('exact row: ' + label,
              expand_terms(rr[0]['terms'], frozenset(cut)) == expected)

    @lru_cache(None)
    def lower(i):
        if i not in gate_rows:
            return 0
        total = 0
        for c, m in gate_rhs(i):
            if c < 0:
                raise ValueError('negative gate coefficient in positive-prefix check')
            p = c
            for j in m:
                p *= lower(j)
            total += p
        return min(total, 1024)

    cap = data['cap_certificate']
    W, A, Z = map(idx, data['scale'])
    L = idx(data['lower_A'])
    Xc, Yc = map(idx, cap['cap']['pair'])
    Uc, Vc, Bc = map(idx, cap['cap']['auxiliary'])
    Sc, Rc = map(idx, cap['cap']['comparison'])
    seeds = [(idx(s['exponent']), *map(idx, s['pair'])) for s in data['seeds']]
    seedk = [k for k, x, y in seeds]
    seedys = [y for k, x, y in seeds]
    frame = list(map(idx, cap['semantic_frame_atoms']))
    expected_frame = set()
    for p in data['powers']:
        expected_frame.update(idx(p[k]) for k in ('base', 'exponent', 'output'))
    expected_frame.update(idx(p['n']) for p in data['modular_requests'])
    check('semantic frame is exactly power atoms union modular upper indices', set(frame) == expected_frame)
    check('frame coordinates are distinct', len(frame) == len(set(frame)))
    check('seed exponent coordinates are distinct', len(seedk) == len(set(seedk)))
    check('every seed exponent is a frame atom', set(seedk) <= set(frame))
    lower_bounds = {str(k): lower(k) for k in seedk}
    check('every seed exponent is positive before semantic interpretation', all(v >= 1 for v in lower_bounds.values()))
    check('anchor coordinates are absent from semantic frame', not ({Xc,Yc,Uc,Vc,Bc,Sc,Rc,W,A,Z,L} & set(frame)))
    check('aggregate contains exactly seed ordinates', list(map(idx, cap['aggregate']['ordinates'])) == seedys)
    check('no additive indices require an additional audit', data['derivations'] == [])
    if not self_radix:
        check('pre-scale arithmetic prefix unchanged',
              data['variables'][:W] == old['variables'][:W]
              and [r for r in rows if all(i < W for c,m in r['terms'] for i in m)] ==
                  [r for r in old['rows'] if all(i < W for c,m in r['terms'] for i in m)])
    row_eq('shared.frame_definition', add(var(W), con(-2), *[neg(var(i)) for i in frame]), [W]+frame)
    row_eq('shared.last_norm_lower',
           add(square(var(L)), neg(mul(add(square(add(var(W),con(1))),con(-1)), square(mul(var(W),var(Z))))), con(-1)),
           [W,L,Z])
    sigma = names['shared.A_slack']
    check('adjustable base is L plus a natural slack', expand_terms([(1,[A])],frozenset([L,sigma])) == add(var(L),var(sigma)))
    check('scale ordinate multiplier Z is positive', lower(Z) >= 1)
    slack = idx(cap['aggregate']['slack'])
    row_eq('index_cap.all_indices_bound',
           add(var(Yc),neg(var(W)),con(-1),neg(var(slack)),*[neg(var(y)) for y in seedys]),
           [Yc,W,slack]+seedys)
    quotient = idx(cap['residue']['quotient'])
    row_eq('index_cap.squared_index_errors',
           add(*[square(add(var(y),neg(var(k)))) for k,x,y in seeds],neg(mul(add(var(A),con(-1)),var(quotient)))),
           [A,quotient]+seedk+seedys)

    def norm(base, x, y):
        return add(square(var(x)), neg(mul(add(square(var(base)),con(-1)),square(var(y)))),con(-1))
    for label, base, x, y in [('index_cap.norm1',A,Xc,Yc),('index_cap.norm2',A,Uc,Vc),('index_cap.norm3',Bc,Sc,Rc)]:
        row_eq(label,norm(base,x,y),[base,x,y])
    for k,x,y in seeds:
        matching = [r for r in rows if r['gate'] is None and r['label'].endswith('.norm1')
                    and (1,[x,x]) in [(c,m) for c,m in r['terms']]]
        check('unique principal norm for seed ' + str(k), len(matching) == 1)
        row_eq(matching[0]['label'],norm(A,x,y),[A,x,y])
    q4 = names['index_cap.q4minus1']
    vd = names['index_cap.Vquotient_minus1']
    bq = names['index_cap.Bquotient']
    sq = names['index_cap.Squotient']
    rq = names['index_cap.Rquotient']
    check('anchor comparison base exact progression',
          expand_terms([(1,[Bc])],frozenset([Yc,q4])) == add(con(1),scale(mul(var(Yc),add(var(q4),con(1))),4)))
    row_eq('index_cap.V_positive_multiple', add(var(Vc),neg(mul(square(var(Yc)),add(var(vd),con(1))))),[Vc,Yc,vd])
    row_eq('index_cap.B_mod_U',add(var(Bc),neg(var(A)),neg(mul(var(Uc),var(bq)))),[Bc,A,Uc,bq])
    row_eq('index_cap.S_mod_U',add(var(Sc),neg(var(Xc)),neg(mul(var(Uc),var(sq)))),[Sc,Xc,Uc,sq])
    row_eq('index_cap.R_mod_4Y',add(var(Rc),neg(var(W)),scale(mul(var(Yc),var(rq)),-4)),[Rc,W,Yc,rq])
    q, qb, modulus, h0 = [idx(data['radix'][k]) for k in ('radix','root_base','root_modulus','root_quotient')]
    check('modular root base is q plus one',expand_terms([(1,[qb])],frozenset([q])) == add(var(q),con(1)))
    row_eq('modular.common_root', add(scale(mul(var(A),var(qb)),2),neg(square(var(qb))),con(-1),neg(mul(var(modulus),var(h0)))),[A,qb,modulus,h0])
    check('six exact-power requests retained', len(data['powers']) == 6)
    check('eleven modular requests retained', len(data['modular_requests']) == 11)

    if self_radix:
        # Compare the source prefix modulo gate renaming and the deliberate
        # replacement of the horizon's lower bound (t0+16 by t0+12).
        def semantic_hasher(d):
            gr = {int(v):d['rows'][r] for v,r in d['gates'].items()}
            tindex = idx(d['amplification']['t'])
            @lru_cache(None)
            def hv(i):
                if i == tindex:
                    return 'semantic_horizon_t'
                if i not in gr:
                    return 'leaf:' + d['variables'][i]['name']
                terms = []
                for c,m in gr[i]['terms']:
                    if m != [i]:
                        terms.append([-c, sorted(hv(j) for j in m)])
                return hashlib.sha256(json.dumps(sorted(terms),separators=(',',':')).encode()).hexdigest()
            def hr(r):
                return sorted([c,sorted(hv(i) for i in m)] for c,m in r['terms'])
            return hv,hr
        hv,hr = semantic_hasher(data)
        ov,orr = semantic_hasher(old)
        inherited_labels = ['fact0.ceiling','fact0.remainder_bound','endpoint.first_quotient',
                            'endpoint.first_remainder','endpoint.last_quotient',
                            'crt.reciprocal_index_congruence','crt.nonnegative_evaluation']
        for label in inherited_labels:
            oldrow = [r for r in old['rows'] if r['label'] == label]
            check('source row preserved modulo horizon/gate renaming: '+label,
                  len(oldrow) == 1 and len(by_label.get(label,[])) == 1
                  and hr(by_label[label][0]) == orr(oldrow[0]))
        check('local majorant certificate unchanged', data['local_majorant'] == old['local_majorant'])
        check('literal calibrated source hash unchanged',
              data['wire_eliminated_source_sha256'] == old['wire_eliminated_source_sha256'])
        oldranges = {r[3]:r for r in old['ranges']}
        for r in data['ranges']:
            prior = oldranges[r[3]]
            check('range request retained: '+r[3],
                  [hv(idx(a)) for a in r[:3]] == [ov(idx(a)) for a in prior[:3]])
        amp = data['amplification']
        t,F,B,K,N = [idx(amp[k]) for k in ('t','F','B','K','N')]
        check('amplification K is literally R', amp['K'] == amp['R'])
        t0,xouter,youter = [names[n] for n in ('t0','x','y')]
        check('horizon is t0+12', expand_terms([(1,[t])],frozenset([t0])) == add(var(t0),con(12)))
        check('R is 2+t+x+y+F',expand_terms([(1,[K])],frozenset([t,xouter,youter,F])) == add(con(2),var(t),var(xouter),var(youter),var(F)))
        check('B is syntactically at least two',lower(B) >= 2)
        S = idx(data['radix']['representative_sum'])
        reps = [idx(r[0]) for r in data['ranges'] if r[3] != 'crt.range.derived_label_sum']
        check('there are nine distinct independent representatives',len(reps) == len(set(reps)) == 9)
        check('all independent representatives are syntactically positive',all(lower(r)>=1 for r in reps))
        check('S is exactly the sum of the nine representatives',
              expand_terms([(1,[S])],frozenset(reps)) == add(*[var(r) for r in reps]))
        check('old aggregate representative bound is absent', 'crt.aggregate_representative_bound' not in by_label)
        fact = data['factorials']
        check('one factorial certificate is retained',len(fact)==1)
        V0,rho = idx(fact[0]['numerator']),idx(fact[0]['radius'])
        check('factorial radius is F squared',expand_terms([(1,[rho])],frozenset([F])) == square(var(F)))
        pp = {(idx(p['base']),idx(p['exponent'])):idx(p['output']) for p in data['powers']}
        numerators = [p for p in data['powers'] if idx(p['output']) == V0]
        check('factorial numerator is one retained exact power at t',len(numerators)==1 and idx(numerators[0]['exponent'])==t)
        check('factorial power base is F squared plus one',
              expand_terms([(1,[idx(numerators[0]['base'])])],frozenset([F])) == add(square(var(F)),con(1)))
        check('N is B to K',pp.get((B,K)) == N)
        radbase = idx(data['radix']['base'])
        check('self radix power base is S plus one',expand_terms([(1,[radbase])],frozenset([S])) == add(var(S),con(1)))
        radpower = pp.get((radbase,K))
        check('self radix power is retained',radpower is not None)
        check('q is N times the self radix power',
              expand_terms([(1,[q])],frozenset([N,radpower])) == mul(var(N),var(radpower)))
        check('exact binomial is the shared factorial/CRT binomial',
              len(data['binomials']) == 1 and idx(data['binomials'][0]['output'])==B
              and idx(data['binomials'][0]['k'])==t
              and expand_terms([(1,[idx(data['binomials'][0]['n'])])],frozenset([F,t])) == add(square(var(F)),var(t)))
        for p in data['powers']:
            nn,kk,mm = [idx(p[z]) for z in ('base','exponent','output')]
            pair = next((pair for key,*pair in seeds if key==kk),None)
            check('power exponent has a certified pair: '+str(mm),pair is not None)
            xx,yy = pair
            tag = data['variables'][mm]['name'].removesuffix('.output')
            hh = names[tag+'.quotient']
            candidates = [i for name,i in names.items() if name.startswith('base') and name.endswith('.T')]
            found=[]
            for TT in candidates:
                expected=add(var(xx),mul(var(nn),var(yy)),neg(mul(var(A),var(yy))),neg(var(mm)),neg(mul(var(TT),var(hh))))
                if expand_terms(by_label[tag+'.power_congruence'][0]['terms'],frozenset([A,xx,yy,nn,mm,hh]+candidates))==expected:
                    found.append(TT)
            check('power congruence exact: '+tag,len(found)==1)
            TT=found[0]
            row_eq(data['variables'][TT]['name']+'_definition',
                   add(scale(mul(var(A),var(nn)),2),neg(square(var(nn))),con(-1),neg(var(TT))),
                   [A,nn,TT])
        root_denoms = list(map(idx,data['radix']['root_denominators']))
        root_expr=var(q)
        for dd in root_denoms:
            root_expr=mul(root_expr,var(dd))
        check('common-root modulus is the printed denominator product',
              expand_terms([(1,[modulus])],frozenset([q]+root_denoms))==root_expr)
        all_denoms={idx(r['den']) for r in data['modular_requests']}
        omitted=idx(data['radix']['omitted_denominator'])
        dominating=idx(data['radix']['dominating_denominator'])
        check('only the dominated t denominator is omitted from the root product',
              set(root_denoms)==all_denoms-{omitted} and dominating in root_denoms
              and expand_terms([(1,[dominating])],frozenset([q,omitted]))==mul(var(q),var(omitted)))
        # Every modular denominator is a retained exact power or its one
        # certified successor; bind the binomial rows to the certified pairs.
        exactden = {(idx(p['base']),idx(p['exponent'])):idx(p['output']) for p in data['powers']}
        derivs = data['denominator_derivations']
        for r in data['modular_requests']:
            den,karg,narg = idx(r['den']),idx(r['k']),idx(r['n'])
            good = exactden.get((q,karg)) == den
            if not good:
                dd = [z for z in derivs if idx(z['output'])==den and idx(z['base'])==q and idx(z['exponent'])==karg]
                if len(dd)==1:
                    source_k=idx(dd[0]['source_exponent'])
                    source_d=exactden.get((q,source_k))
                    good = (source_d is not None and
                            expand_terms([(1,[karg])],frozenset([source_k])) == add(var(source_k),con(1)) and
                            expand_terms([(1,[den])],frozenset([q,source_d])) == mul(var(q),var(source_d)))
            check('modular denominator certified: '+r['label'],good)
            pair=next((pair for kk,*pair in seeds if kk==narg),None)
            check('modular pair uses the certified upper index: '+r['label'],pair == list(map(idx,r['pair'])))
            xx,yy=pair
            quotient,rem,slack_r = [idx(r[z]) for z in ('quotient','remainder','remainder_slack')]
            mod=idx(r['modulus'])
            targetmod=mul(var(den),var(q if r['kind']=='exact' else N))
            check('modular digit modulus: '+r['label'],
                  expand_terms([(1,[mod])],frozenset([den,q,N])) == targetmod)
            residual=add(var(xx),mul(var(qb),var(yy)),neg(mul(var(A),var(yy))),neg(var(rem)),neg(mul(var(mod),var(quotient))))
            cut=[xx,yy,qb,A,rem,mod,quotient]
            if r['kind']=='exact':
                out=idx(r['output'])
                residual=add(residual,neg(mul(var(den),var(out))))
                cut += [den,out]
                os=names[r['label']+'.modular_oslack']
                row_eq(r['label']+'.digit_bound',add(var(q),neg(var(out)),neg(var(os)),con(-1)),[q,out,os])
            row_eq(r['label']+'.modular_digit',residual,cut)
            row_eq(r['label']+'.remainder_bound',add(var(den),neg(var(rem)),neg(var(slack_r)),con(-1)),[den,rem,slack_r])
        check('horizon-12 elementary budget constants',
              amp['factorial_floor']==479001600 and amp['local_degree_bound']==8388608
              and amp['label_degree_bound']==4194304 and
              479001600 > 2**28 and 28*8388608 < 2**28 and 2*8388608 <= 2**28
              and 3*4194304*13 < 2*479001600)
    receipt = {'status':'PASS','checks':len(checks),'check_names':checks,
               'raw_sha256':hashlib.sha256(raw_bytes).hexdigest(),
               'seed_count':len(seeds),'seed_presemantic_lower_bounds_capped_at_1024':lower_bounds,
               'frame_atom_count':len(frame),'self_radix_extension':self_radix,
               'scope':'Exact independent boundary check; ordinary cap proof and inherited calibration are separate.'}
    return receipt


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('raw',type=Path)
    p.add_argument('parent',type=Path)
    p.add_argument('--output',type=Path)
    p.add_argument('--self-radix',action='store_true')
    args = p.parse_args()
    result = audit(args.raw,args.parent,args.self_radix)
    text = json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text)
