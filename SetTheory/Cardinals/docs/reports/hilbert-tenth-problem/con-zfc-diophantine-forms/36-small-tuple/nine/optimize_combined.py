"""Exact Jones evaluator synthesis: package 30 polynomial and package 27 coding.

Reads upstream JSON as inert data. No upstream code is executed.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter, defaultdict
from math import comb, prod, gcd
from functools import reduce
import json, random, hashlib
from circuit_tools import Circuit, evaluate, audit_body

if not __debug__:
    raise SystemExit('Run without -O: assertions are exact audit checks.')

HERE=Path(__file__).resolve().parent
UP=HERE/'source'

def canonical_records(constants):
    signatures={};out=[];aliases={}
    for row in constants['coefficient_records']:
        recipe=row['coefficient_polynomial_in_fixed_ports']
        signature=json.dumps(recipe,sort_keys=True,separators=(',',':'))
        if len(recipe)==1 and not any(recipe[0]['powers']):
            leaf=recipe[0]['coefficient']
        else:
            leaf=signatures.setdefault(signature,row['name'])
        aliases[row['name']]=leaf
        out.append((tuple([4-sum(row['alpha'])]+row['alpha']),leaf))
    return out,aliases

def moment_records():
    parent=json.loads((UP/'quartic31.json').read_text())
    equations=[]
    for row in parent['equations']:
        coeffs=defaultdict(lambda:defaultdict(int))
        for term in row['terms']:
            powers=term['powers'];wp=powers[:31];cp=tuple(powers[31:]);mult=term['coefficient']
            out=[((0,)*32,1)]
            for j,p in enumerate(wp):
                if p:
                    new=[]
                    for ex,c in out:
                        for a in range(p+1):
                            e=list(ex);e[j+1]+=a;new.append((tuple(e),c*comb(p,a)))
                    out=new
            for ex,c in out:
                e=list(ex);e[0]=2-sum(e)
                coeffs[tuple(e)][cp]+=mult*c
        equations.append({e:{p:c for p,c in poly.items() if c} for e,poly in coeffs.items() if any(poly.values())})
    return equations

def build(old,constants,positive=False,strategy=0,moments=False,factor=False):
    d=Circuit();nodes=old['nodes'];mapping={};special={};nu=constants['nu'];one=d.const(1);zero=d.const(0)
    terms,aliases=canonical_records(constants)
    leaves={x['name']:i for i,x in enumerate(nodes) if x['kind'] in ('variable','fixed')}
    @lru_cache(None)
    def clone(i):
        if i in special:return special[i]
        n=nodes[i];k=n['kind']
        if k in ('add','sub','mul'):return d.op(k,clone(n['left']),clone(n['right']))
        if k=='fixed' and n['name'] in aliases:
            v=aliases[n['name']]
            return d.const(v) if isinstance(v,int) else d.leaf('fixed',name=v)
        if positive and k=='variable':return d.op('sub',d.leaf('variable',name=n['name']+'_plus'),one)
        return d.intern(n.copy())
    if positive:
        # Exact affine change from N to positive coordinates; cancel old +1 shifts.
        y=d.leaf('fixed',name='y_index');eps=d.leaf('variable',name='epsilon_plus')
        special[old['named_nodes']['b']]=d.add(y,eps)
        for i,node in enumerate(nodes):
            if node['kind']=='add':
                for a,b in ((node['left'],node['right']),(node['right'],node['left'])):
                    if nodes[a]['kind']=='variable' and nodes[a]['name'] in ('g0','h0','s0','w0','i0','j0') and nodes[b].get('value')==1:
                        special[i]=d.leaf('variable',name=nodes[a]['name']+'_plus')
    B=clone(old['named_nodes']['B']);z=clone(leaves['z_index'])
    power5=[B];fourth=[]
    for _ in range(nu+1):
        s=d.mul(power5[-1],power5[-1]);s4=d.mul(s,s);fourth.append(s4);power5.append(d.mul(s4,power5[-1]))
    v=[one]*(nu+1)
    for j in reversed(range(nu)):v[j]=d.mul(fourth[j],v[j+1])
    w=[power5[nu]]+v
    hs=[one,zero,zero,zero,zero]
    for x in w:
        for r in range(1,5):hs[r]=d.add(hs[r],d.mul(x,hs[r-1]))
    @lru_cache(None)
    def horner(ts):
        if not ts:return zero
        cnt=[sum(e[j]>0 for e,c in ts) for j in range(len(w))]
        if not max(cnt):
            acc=zero
            for e,c in ts:acc=d.add(acc,c)
            return acc
        if strategy==0:
            j=max(range(len(w)),key=lambda j:(cnt[j],sum(e[j] for e,c in ts),j))
        elif strategy==1:
            j=max(range(len(w)),key=lambda j:(cnt[j],sum(e[j] for e,c in ts),-j))
        elif strategy==2:
            j=max(range(len(w)),key=lambda j:(sum(e[j] for e,c in ts),cnt[j],j))
        else:
            j=max(range(len(w)),key=lambda j:(cnt[j]-(0.2*sum(e[j] for e,c in ts)),j))
        yes=[];no=[]
        for e,c in ts:
            if e[j]:
                en=list(e);en[j]-=1;yes.append((tuple(en),c))
            else:no.append((e,c))
        return d.add(horner(tuple(no)),d.mul(w[j],horner(tuple(yes))))
    ts=tuple((e,d.const(c) if isinstance(c,int) else d.leaf('fixed',name=c)) for e,c in terms)
    extra_recipes={}
    if moments:
        # Weighted homogeneous transform of a sum of quadratic squares:
        # E[r(w_i E_i)^2] for independent Exp(1) variables E_i.
        coeff_names={}
        def cf(poly):
            sig=tuple(sorted(poly.items()))
            if len(sig)==1 and not any(sig[0][0]):return d.const(sig[0][1])
            if sig not in coeff_names:
                nm='rcoef'+str(len(coeff_names));coeff_names[sig]=nm
                extra_recipes[nm]=[{'powers':list(p),'coefficient':c} for p,c in sig]
            return d.leaf('fixed',name=coeff_names[sig])
        def plus(xs):
            a=zero
            for x in xs:a=d.add(a,x)
            return a
        def sq(x):return d.mul(x,x)
        # Parent ignores dummy x: w = (t,v_dummy,v_J,...,v_Delta).
        ww=[w[0]]+w[2:]
        vals=[]
        for eq in moment_records():
            diag={};cross=[];rows=defaultdict(list)
            for ex,poly in eq.items():
                support=[i for i,e in enumerate(ex) if e]
                if len(support)==1:
                    i=support[0];diag[i]=d.mul(cf(poly),sq(ww[i]))
                else:
                    i,j=support;v=d.mul(cf(poly),d.mul(ww[i],ww[j]));cross.append(v);rows[i].append(v);rows[j].append(v)
            mu=d.add(d.mul(d.const(2),plus(diag.values())),plus(cross))
            part=[sq(mu)]
            for i in set(rows)|set(diag):
                r=plus(rows[i])
                if i in diag:r=d.add(r,d.mul(d.const(4),diag[i]))
                part.append(sq(r))
            part.append(d.mul(d.const(4),plus(sq(x) for x in diag.values())))
            part.extend(sq(x) for x in cross)
            vals.append(plus(part))
        corr=plus(vals)
    elif factor:
        coeff_names={}
        def leaf_poly(poly):
            if len(poly)==1 and not any(poly[0][0]):return d.const(poly[0][1])
            if poly not in coeff_names:
                name='hcoef'+str(len(coeff_names));coeff_names[poly]=name
                extra_recipes[name]=[{'powers':list(p),'coefficient':c} for p,c in poly]
            return d.leaf('fixed',name=coeff_names[poly])
        def choose(ts):
            cnt=[sum(e[j]>0 for e,p in ts) for j in range(len(w))]
            if strategy%4==0:return max(range(len(w)),key=lambda j:(cnt[j],sum(e[j] for e,p in ts),j))
            if strategy%4==1:return max(range(len(w)),key=lambda j:(cnt[j],sum(e[j] for e,p in ts),-j))
            if strategy%4==2:return max(range(len(w)),key=lambda j:(sum(e[j] for e,p in ts),cnt[j],j))
            return max(range(len(w)),key=lambda j:(cnt[j]-0.2*sum(e[j] for e,p in ts),j))
        @lru_cache(None)
        def horner_fact(ts):
            if not ts:return zero
            g=reduce(gcd,(c for e,p in ts for ex,c in p))
            if ts[0][1][0][1]<0:g=-g
            if g!=1:
                slim=tuple((e,tuple((ex,c//g) for ex,c in p)) for e,p in ts)
                return d.mul(d.const(g),horner_fact(slim))
            if not any(any(e) for e,p in ts):
                pol=defaultdict(int)
                for e,p in ts:
                    for ex,c in p:pol[ex]+=c
                pol=tuple(sorted((ex,c) for ex,c in pol.items() if c))
                return leaf_poly(pol) if pol else zero
            j=choose(ts);yes=[];no=[]
            for e,p in ts:
                if e[j]:
                    ee=list(e);ee[j]-=1;yes.append((tuple(ee),p))
                else:no.append((e,p))
            return d.add(horner_fact(tuple(no)),d.mul(w[j],horner_fact(tuple(yes))))
        actual=[]
        for row in constants['coefficient_records']:
            actual.append((tuple([4-sum(row['alpha'])]+row['alpha']),tuple(sorted((tuple(r['powers']),r['coefficient']) for r in row['coefficient_polynomial_in_fixed_ports']))))
        corr=horner_fact(tuple(actual))
    else:
        corr=horner(ts)
    # Exact sparse polynomial audit of the correction term in B and fixed ports.
    rec={r['name']:{tuple(t['powers']):t['coefficient'] for t in r['coefficient_polynomial_in_fixed_ports']} for r in constants['coefficient_records']}
    rec.update({nm:{tuple(t['powers']):t['coefficient'] for t in terms} for nm,terms in extra_recipes.items()})
    zz=(0,0,0,0)
    @lru_cache(None)
    def sparse(i):
        if i==B:return {(1,zz):1}
        node=d.nodes[i];kind=node['kind']
        if kind=='literal':return {(0,zz):node['value']} if node['value'] else {}
        if kind=='fixed':return {(0,p):c for p,c in rec[node['name']].items()}
        assert kind in ('add','sub','mul'),node
        a=sparse(node['left']);b=sparse(node['right']);out=defaultdict(int)
        if kind=='mul':
            for (ea,pa),ca in a.items():
                for (eb,pb),cb in b.items():out[(ea+eb,tuple(x+y for x,y in zip(pa,pb)))]+=ca*cb
        else:
            for k,c in a.items():out[k]+=c
            for k,c in b.items():out[k]+=(-1 if kind=='sub' else 1)*c
        return {k:c for k,c in out.items() if c}
    expected=defaultdict(int)
    for row in constants['coefficient_records']:
        for term in row['coefficient_polynomial_in_fixed_ports']:
            expected[(4*5**nu-row['expo'],tuple(term['powers']))]+=term['coefficient']
    expected={k:c for k,c in expected.items() if c}
    assert sparse(corr)==expected,'exact polynomial correction identity failed'
    special[old['named_nodes']['e']]=d.mul(power5[nu],d.add(d.mul(z,hs[4]),corr))
    special[old['named_nodes']['q']]=power5[nu+1]
    ell=zero
    for j in range(1,nu+1):ell=d.add(ell,power5[j])
    special[old['named_nodes']['ell']]=ell
    lam=one
    for j in range(nu+1):
        x=power5[j];x2=d.mul(x,x)
        f=d.add(one,d.mul(x,d.mul(d.add(one,x),d.add(one,x2))))
        lam=d.mul(lam,f)
    q=power5[nu+1]
    lam=d.mul(lam,d.mul(d.add(one,q),d.add(one,d.mul(q,q))))
    special[old['named_nodes']['lambda']]=lam
    out=clone(old['output'])
    names={k:clone(i) for k,i in old['named_nodes'].items()}
    body=d.pack(out,names)
    body.update(nu=nu,L=constants['L'],domain='positive' if positive else 'nonnegative',source_polynomial='package30 nine_compact_magnitude_tight',coefficient_binding={'instance':'package30 compact943','constants':'source/COMPACT_CONSTANTS.json','binding':'source/UPSTREAM_COEFFICIENT_BINDING.json','port_bytes':'source/coefficients/','aliases':'coefficient_aliases.json','warning':'All four ports, z_index, y_index and all coefficient leaves are fixed together; no existential parameters.'},model=old['model'])
    body['extra_coefficient_recipes']=extra_recipes
    body['exact_correction_identity']={'status':'PASS','symbolic_terms':len(expected),'ring':'Z[B,beta,K,MC,MF_source]'}
    return body,aliases

def main():
    old=json.loads((UP/'nine_compact_magnitude_tight.json').read_text());constants=json.loads((UP/'COMPACT_CONSTANTS.json').read_text())
    best=None
    for strategy in range(9):
        new,aliases=build(old,constants,strategy=strategy,moments=(strategy==4),factor=(strategy>4))
        ledger=audit_body(new)
        print(strategy,ledger)
        if best is None or ledger['live_operations']<best[0]:best=(ledger['live_operations'],new,aliases,strategy)
    _,new,aliases,strategy=best
    recipes={r['name']:r['coefficient_polynomial_in_fixed_ports'] for r in constants['coefficient_records']}
    rng=random.Random(20261023);checks=0
    for prime in (101,1009,65537,1000000007):
        for trial in range(64):
            ports=[rng.randrange(prime) for _ in range(4)]
            fixed={'z_index':rng.randrange(prime),'y_index':rng.randrange(prime)}
            allrecipes=dict(recipes);allrecipes.update(new.get('extra_coefficient_recipes',{}))
            for k,recipe in allrecipes.items():
                fixed[k]=sum(r['coefficient']*__import__('math').prod(pow(x,e,prime) for x,e in zip(ports,r['powers'])) for r in recipe)%prime
            variables={k:rng.randrange(prime) for k in old['variables']}
            a=evaluate(old,fixed,variables,prime);b=evaluate(new,fixed,variables,prime)
            for name in old['named_nodes']:
                assert a[old['named_nodes'][name]]==b[new['named_nodes'][name]],(prime,trial,name)
                checks+=1
    (HERE/'nine31_folded_natural.json').write_text(json.dumps(new,separators=(',',':'))+'\n')
    (HERE/'coefficient_aliases.json').write_text(json.dumps(aliases,indent=2)+'\n')
    ledger=audit_body(new);ledger.update(modular_named_checks=checks,exact_degree='120724*5^32+366',strategy=strategy,alias_count=len(aliases),source_sha256=hashlib.sha256((UP/'nine_compact_magnitude_tight.json').read_bytes()).hexdigest(),identity_proof='Exact radix-five exponent identity; complete-homogeneous recurrence; Horner distributivity; identical fixed coefficient recipes.')
    positive,_=build(old,constants,positive=True,strategy=strategy)
    pchecks=0
    for prime in (101,1009,65537,1000000007):
        for trial in range(32):
            ports=[rng.randrange(prime) for _ in range(4)]
            fixed={'z_index':rng.randrange(prime),'y_index':rng.randrange(prime)}
            for k,recipe in recipes.items():
                fixed[k]=sum(r['coefficient']*prod(pow(x,e,prime) for x,e in zip(ports,r['powers'])) for r in recipe)%prime
            variables={k:rng.randrange(prime) for k in old['variables']}
            shifted={k+'_plus':x+1 for k,x in variables.items()}
            aa=evaluate(new,fixed,variables,prime);bb=evaluate(positive,fixed,shifted,prime)
            assert aa[new['output']]==bb[positive['output']]
            pchecks+=1
    (HERE/'nine31_folded_positive.json').write_text(json.dumps(positive,separators=(',',':'))+'\n')
    ledger.update(exact_correction_identity=new['exact_correction_identity'],positive=audit_body(positive),positive_affine_shift_checks=pchecks)
    (HERE/'nine31_folded_checks.json').write_text(json.dumps(ledger,indent=2)+'\n')
    print('positive',audit_body(positive))
    print(json.dumps(ledger,indent=2))

if __name__=='__main__':main()
