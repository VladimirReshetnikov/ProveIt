#!/usr/bin/env python3
"""Independent sparse-row and arithmetic audit of the staged cap.

Uses JSON as inert data and imports no construction or inherited checker.
Finite checks support, but do not replace, INDEPENDENT_REVIEW.md.
"""
from collections import defaultdict
from functools import lru_cache
from pathlib import Path
import argparse
import hashlib
import json


def need(condition, message):
    if not condition:
        raise ValueError(message)


def clean(p):
    return {m: c for m, c in p.items() if c}


def add(*ps):
    q = defaultdict(int)
    for p in ps:
        for m, c in p.items():
            q[m] += c
    return clean(q)


def scale(p, c):
    return clean({m: a*c for m, a in p.items()})


def mul(p, q):
    r = defaultdict(int)
    for a, c in p.items():
        for b, d in q.items():
            r[tuple(sorted(a+b))] += c*d
    return clean(r)


def var(i):
    return {(i,): 1}


def num(i):
    return {} if not i else {(): i}


def sq(p):
    return mul(p, p)


def read(path):
    return json.loads(path.read_text())


def raw_poly(terms):
    p = defaultdict(int)
    for c, m in terms:
        p[tuple(sorted(m))] += c
    return clean(p)


def audit(path):
    source_path = path if (path/'raw/raw_audit_input.json').is_file() else path.parent
    natural_path = path/'natural' if (path/'natural/equation.json').is_file() else path
    d = read(source_path/'raw/raw_audit_input.json')
    c = read(source_path/'raw/cap_certificate.json')
    rows = {r['label']:r for r in d['rows'] if r['gate'] is None}
    gate_rows = {r['gate']:r for r in d['rows'] if r['gate'] is not None}
    names = {v['name']:i for i,v in enumerate(d['variables'])}
    row_checks = []

    def expanded_row(label, stops):
        stops = frozenset(stops)
        @lru_cache(None)
        def expr(i):
            if i in stops or i not in gate_rows:
                return var(i)
            p = raw_poly(gate_rows[i]['terms'])
            need(p.get((i,)) == 1, 'gate must have monic defining term')
            del p[(i,)]
            return scale(expand(p), -1)
        def expand(p):
            out = {}
            for mon, coefficient in p.items():
                term = num(coefficient)
                for i in mon:
                    term = mul(term, expr(i))
                out = add(out,term)
            return out
        return expand(raw_poly(rows[label]['terms']))

    def check(label, expected, stops):
        need(expanded_row(label, stops) == expected, 'row mismatch: '+label)
        row_checks.append(label)

    W,A,Z = [a[1] for a in d['scale']]
    L = d['lower_A'][1]
    capX,capY = [a[1] for a in c['cap']['pair']]
    capU,capV,capB = [a[1] for a in c['cap']['auxiliary']]
    capS,capR = [a[1] for a in c['cap']['comparison']]
    atoms = [a[1] for a in c['frame_atoms']]
    check('shared.frame_definition',add(var(W),num(-2),*[scale(var(i),-1) for i in atoms]),{W,*atoms})
    check('shared.last_norm_lower',add(sq(var(L)),scale(mul(add(sq(add(var(W),num(1))),num(-1)),sq(mul(var(W),var(Z)))),-1),num(-1)),{W,L,Z})
    need(c['staged'] is True and c['modular_indices_in_frame'] is False,'must be staged frame')
    need(len(c['groups'])==2,'must have two congruence groups')
    groups=[[s['exponent'][1] for s in g['seeds']] for g in c['groups']]
    need([len(g) for g in groups]==[5,10],'group cardinalities')
    all_seeds=d['seeds']
    need(len(all_seeds)==15,'fifteen seed pairs')
    need(set(groups[0]).isdisjoint(groups[1]),'groups must be disjoint')
    need(set(groups[0]+groups[1])=={s['exponent'][1] for s in all_seeds},'groups must partition seeds')

    for label,x,y,a in [('index_cap.norm1',capX,capY,A),('index_cap.norm2',capU,capV,A),('index_cap.norm3',capS,capR,capB)]:
        expected=add(sq(var(x)),sq(var(y)),scale(mul(sq(var(a)),sq(var(y))),-1),num(-1))
        check(label,expected,{x,y,a})
    vd,bq,sq0,rq,qm=[names['index_cap.'+s] for s in ['Vquotient_minus1','Bquotient','Squotient','Rquotient','q4minus1']]
    check('index_cap.V_positive_multiple',add(var(capV),scale(mul(sq(var(capY)),add(var(vd),num(1))),-1)),{capV,capY,vd})
    check('index_cap.B_mod_U',add(var(capB),scale(var(A),-1),scale(mul(var(capU),var(bq)),-1)),{capB,A,capU,bq})
    check('index_cap.S_mod_U',add(var(capS),scale(var(capX),-1),scale(mul(var(capU),var(sq0)),-1)),{capS,capX,capU,sq0})
    check('index_cap.R_mod_4Y',add(var(capR),scale(var(W),-1),scale(mul(var(capY),var(rq)),-4)),{capR,W,capY,rq})
    rows['cap_B_definition']=gate_rows[capB]
    check('cap_B_definition',add(var(capB),num(-1),scale(mul(var(capY),add(var(qm),num(1))),-4)),{capB,capY,qm})
    sig=names['shared.A_slack'];zm=names['shared.Zminus1']
    rows['free_A_definition']=gate_rows[A]
    check('free_A_definition',add(var(A),scale(var(L),-1),scale(var(sig),-1)),{A,L,sig})
    rows['positive_Z_definition']=gate_rows[Z]
    check('positive_Z_definition',add(var(Z),scale(var(zm),-1),num(-1)),{Z,zm})
    for s in all_seeds:
        x,y = [a[1] for a in s['pair']]
        stem=d['variables'][x]['name'].rsplit('.',1)[0]
        expected=add(sq(var(x)),sq(var(y)),scale(mul(sq(var(A)),sq(var(y))),-1),num(-1))
        check(stem+'.norm1',expected,{x,y,A})

    ys = [s['pair'][1][1] for s in all_seeds]
    u = c['bound']['slack'][1]
    check('index_cap.all_indices_bound',add(var(capY),scale(var(W),-1),num(-1),scale(var(u),-1),*[scale(var(y),-1) for y in ys]),{capY,W,u,*ys})
    for j,g in enumerate(c['groups']):
        qi = g['quotient'][1]
        expected=add(scale(mul(var(A),var(qi)),-1),var(qi))
        stops={A,qi}
        for s in g['seeds']:
            k,y=s['exponent'][1],s['pair'][1][1]
            stops|={k,y}
            expected=add(expected,sq(add(var(y),scale(var(k),-1))))
        check('index_cap.squared_index_errors.'+str(j),expected,stops)

    # Semantic atom identities establishing the first-stage bound, without powers.
    F=d['factorials'][0]['output'][1]
    t=d['factorials'][0]['input'][1]
    n0=d['binomials'][0]['n'][1]
    baseV=d['powers'][0]['base'][1]
    for out,expected,stops in [(n0,add(sq(var(F)),var(t)),{F,t}), (baseV,add(sq(var(F)),num(1)),{F})]:
        r=gate_rows[out]
        synthetic='semantic_gate_'+str(out)
        rows[synthetic]=r
        # Stop at the gate output while expanding its RHS.
        check(synthetic,add(var(out),scale(expected,-1)),stops|{out})
    need(baseV in atoms and t in atoms and baseV!=t,'F squared plus one and t must be distinct frame atoms')
    exponents={p['exponent'][1] for p in d['powers']}
    need(len(d['powers'])==6 and len(exponents)==4,'six exact powers, four indices')
    need(set(groups[0])==exponents|{n0},'first-stage semantic group')
    need(exponents<=set(atoms),'all power indices in frame')

    # Lower bounds are only used capped at 100, avoiding irrelevant huge values.
    @lru_cache(None)
    def lower(i):
        if i not in gate_rows:return 0
        p=raw_poly(gate_rows[i]['terms']);del p[(i,)]
        total=0
        for mon,c0 in p.items():
            need(c0<=0,'nonnegative arithmetic gate')
            v=-c0
            for j in mon:v*=lower(j)
            total+=v
        return min(total,100)
    Wlower=2+sum(lower(i) for i in atoms)
    need(Wlower>=18,'frame enough for all fifteen seeds')
    need(all(lower(k)>=1 for k in groups[0]),'first-stage indices syntactically positive')

    # Check common-root polynomial directly with semantic wires as leaves.
    q=d['radix']['radix'][1]
    M=d['radix']['root_modulus'][1]
    h0=d['radix']['root_quotient'][1]
    qb=add(var(q),num(1))
    check('modular.common_root',add(scale(mul(var(A),qb),2),scale(sq(qb),-1),num(-1),scale(mul(var(M),var(h0)),-1)),{q,A,M,h0})

    # The dominant-modulus change must be checked in the literal gates,
    # rather than inferred from the descriptive certificate alone.
    def semantic_gate(out, expected, stops, label):
        need(out in gate_rows, 'missing semantic gate: '+label)
        rows[label]=gate_rows[out]
        check(label,add(var(out),scale(expected,-1)),set(stops)|{out})

    N=d['radix']['modulus'][1]
    K=d['radix']['K'][1]
    V=d['factorials'][0]['numerator'][1]
    B=d['factorials'][0]['binomial'][1]
    Dt=d['radix']['omitted_denominator'][1]
    Dx=d['radix']['dominating_denominator'][1]
    x,y=names['x'],names['y']
    t1=d['denominator_derivations'][0]['exponent'][1]
    y1=d['powers'][4]['exponent'][1]
    x1=d['powers'][5]['exponent'][1]
    Dy=d['powers'][4]['output'][1]
    Dt1=d['denominator_derivations'][0]['output'][1]
    semantic_gate(t1,add(var(t),num(1)),{t},'dominant.t_plus_one')
    semantic_gate(y1,add(var(y),num(1)),{y},'dominant.y_plus_one')
    semantic_gate(x1,add(var(x),num(1)),{x},'dominant.x_plus_one')
    semantic_gate(B,add(var(names['reciprocal.Bminus2']),num(2)),
                  {names['reciprocal.Bminus2']},'dominant.B_at_least_two')
    semantic_gate(K,scale(add(var(t),var(x),var(y),var(F),num(2)),2),
                  {t,x,y,F},'dominant.K_positive')
    expected_powers={(baseV,t,V),(B,K,N),(N,K,q),
                     (q,t,Dt),(q,y1,Dy),(q,x1,Dx)}
    need({(p['base'][1],p['exponent'][1],p['output'][1])
          for p in d['powers']}==expected_powers,
         'dominant-modulus exact-power identification')
    need(len(d['denominator_derivations'])==1,
         'one multiplied denominator')
    dd=d['denominator_derivations'][0]
    need(dd['kind']=='multiply_by_base' and dd['base']==['v',q]
         and dd['source_exponent']==['v',t],
         'q^(t+1) denominator derivation')
    semantic_gate(Dt1,mul(var(q),var(Dt)),{q,Dt},
                  'dominant.D_t_plus_one')
    semantic_gate(M,mul(var(N),var(Dx)),{N,Dx},
                  'dominant.root_modulus_is_N_Dx')

    # The early endpoint bound uses only exact powers and these raw rows;
    # it does not presuppose B's binomial meaning or F=t!.
    rem=d['factorials'][0]['remainder'][1]
    slack=d['factorials'][0]['slack'][1]
    check('fact0.ceiling',add(var(V),var(B),
          scale(mul(var(B),var(F)),-1),scale(var(rem),-1),num(-1)),
          {V,B,F,rem})
    check('fact0.remainder_bound',add(var(B),scale(var(rem),-1),
          scale(var(slack),-1),num(-1)),{B,rem,slack})
    need(add(expanded_row('fact0.ceiling',{V,B,F,rem,slack}),
             scale(expanded_row('fact0.remainder_bound',
                                {V,B,F,rem,slack}),-1))
         ==add(var(V),var(slack),scale(mul(var(B),var(F)),-1)),
         'derived raw identity V+slack=BF')
    u0,r0,ut=[names['endpoint.'+s] for s in ['u0','r0','ut']]
    check('endpoint.first_quotient',add(var(x),scale(var(F),-1),
          num(-1),scale(mul(add(var(y),num(1)),var(u0)),-1)),
          {x,F,y,u0})
    check('endpoint.first_remainder',add(var(y),scale(var(F),-1),
          num(-1),scale(var(r0),-1)),{y,F,r0})
    check('endpoint.last_quotient',add(var(x),num(-1),
          scale(mul(add(num(1),mul(add(var(t),num(1)),var(y))),
                    var(ut)),-1)),{x,t,y,ut})

    # Each requested modulus must be one proved to divide N*Dx.
    den_by_k={t:Dt,t1:Dt1,y1:Dy,x1:Dx}
    requests=d['modular_requests']
    exact=[r for r in requests if r['kind']=='exact']
    need(len(exact)==1 and exact[0]['label']=='choose0'
         and exact[0]['n']==['v',n0] and exact[0]['k']==['v',t]
         and exact[0]['output']==['v',B]
         and exact[0]['den']==['v',Dt]
         and exact[0]['modulus']==['v',Dt1],
         'exact binomial modulus q^(t+1)')
    divisible=[r for r in requests if r['kind']=='divisible']
    need(len(divisible)==10 and len(requests)==11,
         'ten range requests and one exact request')
    ranges={r[3]:(r[0],r[1],r[2]) for r in d['ranges']}
    for req in divisible:
        k=req['k'][1]
        need(k in den_by_k and req['den']==['v',den_by_k[k]],
             'range denominator: '+req['label'])
        need(ranges.get(req['label'])==(req['n'],req['k'],['v',N]),
             'range modulus binding: '+req['label'])
        den=req['den'][1]; mod=req['modulus'][1]
        semantic_gate(mod,mul(var(N),var(den)),{N,den},
                      'dominant.range_modulus.'+req['label'])

    # Independently collect the literal quartic, with no implementation imports.
    e=read(natural_path/'equation.json')
    terms={}
    live=set()
    for r in e['residuals']:
        p=raw_poly(r['terms'])
        need(max((len(m) for m in p),default=0)<=2,'nonquadratic residual')
        live.update(i for m in p for i in m)
        terms=add(terms,sq(p))
    expected=raw_poly(read(natural_path/'expanded_polynomial.json')['terms'])
    need(terms==expected,'collected quartic differs')
    n=e['metrics']['variables']
    need(live==set(range(n)),'variable liveness')
    metrics={'variables':n,'rows':len(e['residuals']),'monomials':len(terms),'degree':max(len(m) for m in terms),'height':max(abs(v) for v in terms.values())}
    need(metrics['degree']==4,'quartic degree')
    need(metrics['monomials']==e['metrics']['expanded_monomials'],'monomial metric')
    need(metrics['height']==e['metrics']['max_abs_expanded_coefficient'],'height metric')
    return {'path':str(path),'source_path':str(source_path),'row_checks':row_checks,'group_sizes':[5,10],'frame_atoms':len(atoms),'syntactic_frame_lower_bound':Wlower,'metrics':metrics,'equation_sha256':hashlib.sha256((natural_path/'equation.json').read_bytes()).hexdigest()}


def pell(a,n):
    x,y=1,0
    for _ in range(n):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y


def regressions():
    count=0
    for W in range(3,13):
        a=W**3+2
        cap=pell(a,W)[1]
        for n in range(1,W):
            ks=[n]*(W-2)
            ys=[pell(a,k)[1] for k in ks]
            need(cap-W-1-sum(ys)>=0,'aggregate completeness fixture')
            need(sum((y-k)**2 for y,k in zip(ys,ks))%(a-1)==0,'pooled divisibility fixture')
            need(sum((k-k)**2 for k in ks)<a-1,'bounded error fixture')
            count+=1
    # A large intended index is not authenticated by the cap alone.
    a,W,j,k=100,3,1,100
    y=pell(a,j)[1]
    cap=pell(a,W)[1]
    need(a-1>W**3 and cap-W-1-y>=0 and (y-k)**2%(a-1)==0 and j!=k,'unbounded-index counterexample')
    return {'canonical_cap_fixtures':count,'range_hypothesis_counterexample':{'A':a,'W':W,'actual_index':j,'requested_index':k,'ordinate':y,'cap_ordinate':cap,'pooled_quotient':(y-k)**2//(a-1)}}


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('outputs',nargs='+',type=Path);p.add_argument('--receipt',type=Path)
    a=p.parse_args()
    out={'status':'pass','audit_scope':'new raw cap/frame/groups, dominant modulus and denominator bindings, early raw endpoint identities, plus literal SOS expansion; no new kernel proof or full inherited source re-verification','results':[audit(x) for x in a.outputs],'regressions':regressions()}
    if a.receipt:a.receipt.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
