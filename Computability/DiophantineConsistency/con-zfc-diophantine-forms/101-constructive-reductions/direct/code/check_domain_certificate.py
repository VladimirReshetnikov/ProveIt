#!/usr/bin/env python3
"""Independent exact checker of frame-based domain recovery.

No producer, shared-power builder, or sign-rule discovery function is imported.
Each proposed rule is rederived from a literal target residual. Every raw
compiler row is checked after an explicit polynomial restoration. Frame,
base-modulus, and power-congruence identities are expanded independently.
"""
from pathlib import Path
from collections import Counter,defaultdict
from functools import lru_cache
from hashlib import sha256
import json,argparse
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def need(ok,message):
    if not ok:raise ValueError(message)
def collect(terms):
    d=defaultdict(int)
    for c,m in terms:d[tuple(sorted(m))]+=c
    return {m:c for m,c in d.items() if c}
def add(*polys):
    return collect((c,m) for p in polys for m,c in p.items())
def scale(p,c):return {m:c*v for m,v in p.items() if c*v}
def mul(p,q):return collect((a*b,m+n) for m,a in p.items() for n,b in q.items())
def cst(c):return {():c} if c else {}
def atom(i):return {(i,):1}
def evaluate(poly,values):
    terms=[]
    for mon,c in poly.items():
        p=cst(c)
        for i in mon:p=mul(p,values(i))
        terms.extend((v,k) for k,v in p.items())
    return collect(terms)

def sign_bound(poly,known,strict=False):
    """Integer monomials with positive coefficients and even powers."""
    lower=poly.get((),0)
    for mon,c in poly.items():
        if not mon:continue
        if c<0:return False
        powers=Counter(mon)
        if any(k%2 and (v,0) not in known for v,k in powers.items()):return False
        if all((v,1) in known for v in powers):lower+=c
    return lower>=(1 if strict else 0)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=ROOT/'DOMAIN_CERTIFICATE.json')
    parser.add_argument('--raw-interface',type=Path,default=ROOT/'RAW_FRAME_INTERFACE.json')
    parser.add_argument('--output',type=Path,help='Optional receipt; default verification is read-only')
    args=parser.parse_args()
    eqfile=ROOT/'equations_v3/cap64/equation.json'
    eq=json.loads(eqfile.read_text());rows=[collect(r['terms']) for r in eq['residuals']]
    src=json.loads((ROOT/'equations_v3/source/equation.json').read_text())
    elim=json.loads((ROOT/'equations_v3/cap64/elimination_certificate.json').read_text())
    cert=json.loads(args.certificate.read_text())
    raw=json.loads(args.raw_interface.read_text())
    need(cert['final_equation_sha256']==sha256(eqfile.read_bytes()).hexdigest(),'equation digest')
    n=len(eq['variables']);names=[v['name'] for v in raw['variables']]
    need(len(set(names))==len(names),'raw names are not unique')
    rawindex={name:i for i,name in enumerate(names)}
    retained={rawindex[v['name']]:i for i,v in enumerate(eq['variables'])}
    source_names=[v['name'] for v in src['variables']]
    restore={rawindex[source_names[s['variable_original_index']]]:
             collect((c,[rawindex[source_names[i]] for i in mon]) for c,mon in s['restoration'])
             for s in elim['steps']}
    gates={g['out'][1]:g for g in raw['gates']}
    need(len(gates)==len(raw['gates']),'duplicate gate metadata')
    def raw_atom(a):
        need(a[0] in ('c','v'),'invalid raw atom type')
        return cst(a[1]) if a[0]=='c' else atom(a[1])
    gate_rows={r['gate']:collect(r['terms']) for r in raw['rows'] if r.get('gate') is not None}
    need(len(gate_rows)==sum(r.get('gate') is not None for r in raw['rows']),'duplicate raw gate equation')
    need(set(gates)==set(gate_rows),'metadata/gate-row domain mismatch')
    for out,g in gates.items():
        need(g['out'][0]=='v' and g['op'] in ('add','mul'),'invalid gate metadata')
        l,r=raw_atom(g['left']),raw_atom(g['right'])
        value=add(l,r) if g['op']=='add' else mul(l,r)
        need(add(atom(out),scale(value,-1))==gate_rows[out],'gate metadata disagrees with defining residual')
    active=set()
    @lru_cache(None)
    def translate(i):
        if i in retained:return atom(retained[i])
        need(i not in active,'restoration cycle');active.add(i)
        if i in restore:p=evaluate(restore[i],translate)
        else:
            need(i in gates,'unmapped raw variable');g=gates[i]
            p=add(read(g['left']),read(g['right'])) if g['op']=='add' else mul(read(g['left']),read(g['right']))
        active.remove(i)
        need(all(c>=0 for c in p.values()),'restoration coefficient negative')
        return p
    def read(a):return cst(a[1]) if a[0]=='c' else translate(a[1])
    target_set={tuple(sorted(p.items())) for p in rows}
    restored=zero=0
    for row in raw['rows']:
        p=evaluate(collect(row['terms']),translate)
        if not p:zero+=1
        else:
            need(tuple(sorted(p.items())) in target_set,'raw row does not restore: '+row['label'])
            restored+=1

    known={(i,0) for i in cert['guards']}
    need(len(known)==len(cert['guards']) and all(0<=i<n for i,_ in known),'guard inventory')
    def steps(sequence):
        for step in sequence:
            v,strict=step['target'];need(0<=v<n and strict in (0,1),'bad target')
            need((v,strict) not in known,'redundant rule')
            if step['row'] is None:
                need(strict==0 and (v,1) in known,'invalid strict-to-weak rule')
            else:
                r=rows[step['row']];sign=step['sign'];need(sign in (-1,1),'bad orientation')
                need(all(mon.count(v)<=1 for mon in r),'nonlinear pivot')
                a=collect((sign*c,[j for j in mon if j!=v]) for mon,c in r.items() if v in mon)
                bb=collect((-sign*c,mon) for mon,c in r.items() if v not in mon)
                need(sign_bound(a,known,True),'pivot coefficient not positive')
                need(sign_bound(bb,known,bool(strict)),'pivot right side has unknown sign')
            known.add((v,strict))
    steps(cert['pre_steps'])
    before=sum((i,0) in known for i in range(n))

    def cut_row(rid,cuts):
        cuts={tuple(a) for a in cuts if a[0]=='v'}
        @lru_cache(None)
        def val(a):
            if a[0]=='c':return cst(a[1])
            if a in cuts or a[1] not in gates:return atom(a[1])
            g=gates[a[1]];l=val(tuple(g['left']));r=val(tuple(g['right']))
            return add(l,r) if g['op']=='add' else mul(l,r)
        return evaluate(collect(raw['rows'][rid]['terms']),lambda i:val(('v',i)))
    def symbolic(a):return cst(a[1]) if a[0]=='c' else atom(a[1])
    f=raw['frame'];W,A,Z=[f[k] for k in ('W','A','Z')]
    Ws,As,Zs=map(symbolic,(W,A,Z))
    norm=add(mul(As,As),cst(-1),scale(mul(mul(mul(Ws,Ws),Ws),mul(add(Ws,cst(2)),mul(Zs,Zs))),-1))
    need(cut_row(f['norm_row'],(W,A,Z))==norm,'shared norm identity')
    requested={tuple(p[k]) for p in raw['powers'] for k in ('base','exponent','output')}
    expected_sum=add(Ws,cst(-2),*(scale(symbolic(a),-1) for a in requested))
    need(cut_row(f['sum_row'],[W]+list(requested))==expected_sum,'frame sum identity')
    need(all(sign_bound(read(a),known) for a in requested),'unproved frame input sign')
    need(sign_bound(read(A),known) and sign_bound(read(Z),known,True),'unproved frame orientation')
    # These exact identities and verified signs imply W>=2 and A>W^2.
    expected_facts=set()
    for base in f['bases']:
        nn,T=base['base'],base['T'];ns,Ts=map(symbolic,(nn,T))
        need(tuple(nn) in requested and sign_bound(read(nn),known,True),'base positivity precedes frame step')
        expected=add(scale(mul(As,ns),2),scale(Ts,-1),scale(mul(ns,ns),-1),cst(-1))
        need(cut_row(base['row'],(A,nn,T))==expected,'modulus defining identity')
        need(T[0]=='v' and T[1] in retained,'modulus target not retained')
        expected_facts.add((retained[T[1]],1))
    x_targets=set()
    for p in raw['powers']:
        xx,yy,nn,mm,tt,qq=[p[k] for k in ('X','Y','base','output','T','quotient')]
        Xs,Ys,ns,ms,Ts,qs=map(symbolic,(xx,yy,nn,mm,tt,qq))
        expected=add(Xs,mul(Ys,ns),scale(mul(Ys,As),-1),scale(ms,-1),scale(mul(Ts,qs),-1))
        need(cut_row(p['row'],(xx,yy,nn,A,mm,tt,qq))==expected,'power congruence identity')
        need(all(sign_bound(read(a),known) for a in (yy,mm,qq)),'power right-side sign precedes frame step')
        need((retained[tt[1]],1) in expected_facts,'uncovered modulus')
        need(xx[0]=='v' and xx[1] in retained,'abscissa target not retained')
        x_targets.add((retained[xx[1]],0))
    expected_facts |= x_targets
    need(set(map(tuple,cert['frame_conclusions']))==expected_facts,'frame conclusions differ')
    for v,s in expected_facts:known.add((v,s));known.add((v,0))
    steps(cert['post_steps'])
    need(all((i,0) in known for i in range(n)),'domain recovery incomplete')
    result={'status':'PASS','guard_variables':len(cert['guards']),
            'preclosure_nonnegative':before,'postclosure_nonnegative':n,
            'raw_rows_restored_to_zero':zero,'raw_rows_restored_to_final_residuals':restored,
            'raw_polynomial_restorations':len(names),'pre_rules':len(cert['pre_steps']),
            'raw_gate_metadata_identities':len(gates),
            'frame_moduli_proved_positive':len(f['bases']),
            'frame_abscissae_proved_nonnegative':len(x_targets),
            'checked_power_identities':len(raw['powers']),'post_rules':len(cert['post_steps']),
            'optimized_python':not __debug__,
            'scope':'Exact finite certificate with ordinary ordered-ring frame lemma; no consistency decision.'}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
