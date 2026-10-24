#!/usr/bin/env python3
"""Independent finite audit for the delayed-power-sign quartic.

No generator, source compiler, or elimination module is imported.  This checks
literal identities and the premises of the unbounded lemma in PROOF.md; it is
not a proof of that lemma by finite testing and does not decide consistency.
"""
from pathlib import Path
from collections import Counter,defaultdict
from functools import lru_cache
import argparse,hashlib,json,zipfile
ROOT=Path(__file__).resolve().parent
def need(ok,msg):
    if not ok:raise ValueError(msg)
def canonical(o):return (json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode()
def sha(o):return hashlib.sha256(canonical(o)).hexdigest()
def collect(terms):
    out=defaultdict(int)
    for c,m in terms:out[tuple(sorted(m))]+=c
    return {m:c for m,c in out.items() if c}
def add(*ps):return collect((c,m) for p in ps for m,c in p.items())
def scale(p,c):return {m:v*c for m,v in p.items() if v*c}
def mul(p,q):return collect((c*d,m+n) for m,c in p.items() for n,d in q.items())
def cst(c):return {():c} if c else {}
def var(v):return {(v,):1}
def power(p,n):
    out=cst(1)
    for _ in range(n):out=mul(out,p)
    return out
def evaluate(p,read):
    out=[]
    for m,c in p.items():
        term=cst(c)
        for v in m:term=mul(term,read(v))
        out.append(term)
    return add(*out)
def sign_bound(p,known,strict=False):
    lower=p.get((),0)
    for m,c in p.items():
        if not m:continue
        if c<0:return False
        exps=Counter(m)
        if any(k%2 and (v,0) not in known for v,k in exps.items()):return False
        if all((v,1) in known for v in exps):lower+=c
    return lower>=int(strict)
def load(path):return json.loads(path.read_text())

def provenance():
    pins=load(ROOT/'SOURCE_PINS.json')
    zp=ROOT/'upstream/ConZFC_407_888_Quartics_2026-10-24.zip';data=zp.read_bytes()
    need(hashlib.sha256(data).hexdigest()==pins['archive_sha256'],'source archive SHA256')
    need(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==pins['archive_git_blob'],'source archive Git blob')
    with zipfile.ZipFile(zp) as z:
        for path,item in pins['source_members'].items():
            b=(ROOT/path).read_bytes()
            need(hashlib.sha256(b).hexdigest()==item['sha256'],'source member hash '+path)
            need(z.read(item['member'])==b,'source member byte match '+path)
    return len(pins['source_members'])

def check_domain(eq,cert,raw,interface,macros):
    n=len(eq['variables']);rows=[collect(r['terms']) for r in eq['residuals']]
    need(sha(eq)==cert['source_sha256'],'source canonical hash')
    names=[v['name'] for v in raw['all_variables']]
    need(len(set(names))==len(names),'unique raw names')
    rawindex={name:i for i,name in enumerate(names)}
    retained={rawindex[v['name']]:i for i,v in enumerate(eq['variables'])}
    rawrows=[collect(r['terms']) for r in raw['all_rows']]
    gates={int(v):rid for v,rid in raw['gates'].items()}
    need(len(set(gates.values()))==len(gates),'duplicate defining rows')
    definitions={}
    for v,rid in gates.items():
        p=rawrows[rid];c=p.get((v,),0)
        need(c in (-1,1) and all(v not in m for m in p if m!=(v,)),'nonmonic raw gate')
        definitions[v]={m:-c*a for m,a in p.items() if m!=(v,)}
    active=set()
    @lru_cache(None)
    def translate(v):
        if v in retained:return var(retained[v])
        need(v not in active and v in definitions,'raw restoration gap/cycle')
        active.add(v);out=evaluate(definitions[v],translate);active.remove(v)
        need(all(c>=0 for c in out.values()),'inlined raw gate is not monotone')
        return out
    def read(a):
        need(a[0] in ('c','v'),'bad atom')
        return cst(a[1]) if a[0]=='c' else translate(a[1])
    def symbolic(a):return cst(a[1]) if a[0]=='c' else var(a[1])
    actual_rows={tuple(sorted(p.items())) for p in rows}
    restored=zero=0
    for p in rawrows:
        q=evaluate(p,translate)
        if not q:zero+=1
        else:
            need(tuple(sorted(q.items())) in actual_rows,'raw row not implied by actual rows')
            restored+=1
    def cut_value(a,cuts):
        cuts={tuple(t) for t in cuts if t[0]=='v'}
        busy=set()
        @lru_cache(None)
        def rec(v):
            if ('v',v) in cuts or v not in definitions:return var(v)
            need(v not in busy,'cut gate cycle');busy.add(v)
            out=evaluate(definitions[v],rec);busy.remove(v);return out
        return cst(a[1]) if a[0]=='c' else rec(a[1])
    def cut_row(rid,cuts):
        return evaluate(rawrows[rid],lambda v:cut_value(['v',v],cuts))
    def equal_mod_gates(actual,expected):
        """Exact polynomial identity using already authenticated raw gate rows.

        A cut may name two related atoms (for example t and t+2).  The
        difference is reduced, never either full side, to avoid unnecessary
        expansion of the complete arithmetic circuit.
        """
        difference=add(actual,scale(expected,-1))
        while difference:
            candidates={v for m in difference for v in m if v in definitions}
            if not candidates:return False
            v=max(candidates)
            need(all(w<v for m in definitions[v] for w in m),'raw gates not topological')
            difference=evaluate(difference,lambda w:definitions[v] if w==v else var(w))
            need(len(difference)<200000,'identity reduction resource bound')
        return True
    def mapped(a):
        need(a[0]=='v' and a[1] in retained,'fact target not retained')
        return retained[a[1]]
    known={(v,0) for v in cert['guards']}
    need(len(known)==len(cert['guards']) and all(0<=v<n for v,_ in known),'guard inventory')
    def steps(items):
        for step in items:
            v,s=step['target'];need(0<=v<n and s in (0,1),'bad sign target')
            need((v,s) not in known,'duplicate sign target')
            kind=step['kind']
            if kind=='strict_to_weak':
                need(s==0 and (v,1) in known and step['row'] is None,'invalid weakening')
            else:
                p=rows[step['row']];eps=step['sign'];need(eps in (-1,1),'bad row orientation')
                need(all(m.count(v)<=1 for m in p),'nonlinear factor pivot')
                a=collect((eps*c,[w for w in m if w!=v]) for m,c in p.items() if v in m)
                b=collect((-eps*c,m) for m,c in p.items() if v not in m)
                if kind=='positive_factor':
                    need(sign_bound(a,known,True) and sign_bound(b,known,bool(s)),'unproved factor or numerator sign')
                elif kind=='affine_square':
                    root=collect(step['square_root'])
                    need(s==0 and len(a)==1 and a.get((),0)>0 and mul(root,root)==b,'invalid affine square')
                    need(all(len(m)<=1 for m in root),'root not affine')
                else:raise ValueError('unknown sign rule')
            known.add((v,s))
    steps(cert['pre_steps'])
    pre_count=sum((i,0) in known for i in range(n))
    f=interface['frame'];W,A,Z,D=[f[k] for k in ('W','A','Z','D')]
    ww,aa,zz,dd=map(symbolic,(W,A,Z,D))
    pp=interface['powers']
    requests={tuple(p[k]) for p in pp for k in ('n','k','m')}
    macro_requests={(tuple(m['base']),tuple(m['exponent']),tuple(m['output'])) for m in macros if m['macro']=='power'}
    need({(tuple(p['n']),tuple(p['k']),tuple(p['m'])) for p in pp}==macro_requests,'power inventory mismatch')
    need(len(pp)==len(macro_requests),'duplicate power interface')
    need(equal_mod_gates(cut_row(f['sum_row'],[W]+list(requests)),add(ww,cst(-2),*(scale(symbolic(a),-1) for a in requests))),'frame sum identity')
    need(all(sign_bound(read(a),known) for a in requests),'frame atoms not nonnegative before frame')
    need(sign_bound(read(A),known) and sign_bound(read(Z),known,True),'frame orientation missing')
    norm=add(power(aa,2),cst(-1),scale(mul(mul(power(ww,3),add(ww,cst(2))),power(zz,2)),-1))
    need(cut_row(f['norm_row'],(W,A,Z))==norm,'frame Pell identity')
    need(cut_row(f['D_row'],(A,D))==add(power(aa,2),scale(dd,-1),cst(-1)),'discriminant identity')
    expected_frame={(mapped(D),1)};base_map={}
    for b in interface['bases']:
        nn,T=b['n'],b['T'];ns,ts=map(symbolic,(nn,T))
        need(tuple(nn) in requests and sign_bound(read(nn),known,True),'base positivity must precede frame')
        expected=add(scale(mul(aa,ns),2),scale(ts,-1),scale(power(ns,2),-1),cst(-1))
        need(cut_row(b['row'],(A,nn,T))==expected,'base modulus identity')
        need(tuple(nn) not in base_map,'duplicate base');base_map[tuple(nn)]=T
        expected_frame.add((mapped(T),1))
    need(set(map(tuple,cert['frame_facts']))==expected_frame,'frame facts mismatch')
    known|=expected_frame
    steps(cert['middle_steps'])
    mid_count=sum((i,0) in known for i in range(n))

    # The following literal checks bind every hypothesis of the inherited
    # Matiyasevich index criterion, including the common divisibility product.
    aux=interface['auxiliary'];U,V,B,q4,bq,vm=[aux[k] for k in ('U','V','B','q4minus1','Bquotient','Vquotient_minus1')]
    uu,vv,bb,q4s,bqs,vms=map(symbolic,(U,V,B,q4,bq,vm))
    for a in (U,V,B,q4,bq,vm):need(sign_bound(read(a),known),'auxiliary index sign')
    need(cut_row(aux['norm_row'],(A,U,V))==add(power(uu,2),power(vv,2),scale(mul(power(aa,2),power(vv,2)),-1),cst(-1)),'auxiliary norm')
    need(cut_value(B,(V,q4))==add(cst(1),scale(mul(vv,add(q4s,cst(1))),4)),'auxiliary B definition')
    need(cut_row(aux['B_row'],(B,A,U,bq))==add(bb,scale(aa,-1),scale(mul(uu,bqs),-1)),'auxiliary B congruence')
    ys=[s['Y'] for s in interface['seeds']];prod=cst(1)
    for y in ys:prod=mul(prod,power(symbolic(y),2))
    need(cut_row(aux['product_row'],[V,vm]+ys)==add(vv,scale(mul(prod,add(vms,cst(1))),-1)),'positive common product')
    pairs={}
    for s in interface['seeds']:
        k,X,Y,S,R,e,sq,rq=[s[z] for z in ('k','X','Y','S','R','e','sq','rq')]
        ks,xs,yys,ss,rr,es,sqs,rqs=map(symbolic,(k,X,Y,S,R,e,sq,rq));rrs=s['rows']
        need(sign_bound(read(k),known,True),'seed exponent positivity')
        for t in (X,Y,S,R,e,sq,rq):need(sign_bound(read(t),known),'seed witness not natural before power recovery')
        need(cut_row(rrs['index_at_most_Y'],(Y,k,e))==add(yys,scale(ks,-1),scale(es,-1)),'index bound')
        need(cut_row(rrs['norm1'],(A,X,Y))==add(power(xs,2),power(yys,2),scale(mul(power(aa,2),power(yys,2)),-1),cst(-1)),'index first norm')
        need(cut_row(rrs['norm3'],(B,S,R))==add(power(ss,2),power(rr,2),scale(mul(power(bb,2),power(rr,2)),-1),cst(-1)),'index third norm')
        need(cut_row(rrs['S_mod_U'],(S,X,U,sq))==add(ss,scale(xs,-1),scale(mul(uu,sqs),-1)),'index S congruence')
        need(cut_row(rrs['R_mod_4Y'],(R,k,Y,rq))==add(rr,scale(ks,-1),scale(mul(yys,rqs),-4)),'index R congruence')
        need(tuple(k) not in pairs,'duplicate seed');pairs[tuple(k)]=(X,Y)
    for d in interface['derived']:
        need(d['kind']=='shift' and d['shift'] in (1,2),'unsupported index derivation')
        need(tuple(d['source']) in pairs and tuple(d['target']) not in pairs,'derived index order')
        X,Y=pairs[tuple(d['source'])];xx,yy=map(symbolic,(X,Y))
        shift=d['shift'];sx,sy=(aa,cst(1)) if shift==1 else (add(scale(dd,2),cst(1)),scale(aa,2))
        need(cut_value(d['target'],(d['source'],))==add(symbolic(d['source']),cst(shift)),'shifted exponent identity')
        Xn,Yn=d['pair'];cuts=(A,D,X,Y)
        need(cut_value(Xn,cuts)==add(mul(xx,sx),mul(dd,mul(yy,sy))),'derived X addition')
        need(cut_value(Yn,cuts)==add(mul(xx,sy),mul(yy,sx)),'derived Y addition')
        need(sign_bound(read(Xn),known) and sign_bound(read(Yn),known),'derived index sign')
        pairs[tuple(d['target'])]=(Xn,Yn)
    expected_power=set()
    for p in pp:
        nn,k,m,X,Y,T,h=[p[z] for z in ('n','k','m','X','Y','T','h')]
        need(tuple(k) in pairs and tuple(map(tuple,pairs[tuple(k)]))==(tuple(X),tuple(Y)),'power index pair')
        need(base_map[tuple(nn)]==T,'power base modulus')
        for a,strict in ((nn,True),(k,True),(m,False)):
            need(sign_bound(read(a),known,strict),'power input sign')
        ns,ms,xs,yys,ts,hs=map(symbolic,(nn,m,X,Y,T,h))
        expected=add(xs,mul(ns,yys),scale(mul(aa,yys),-1),scale(ms,-1),scale(mul(ts,hs),-1))
        need(cut_row(p['row'],(X,Y,nn,A,m,T,h))==expected,'literal signed power congruence')
        expected_power.add((mapped(h),0))
    need(set(map(tuple,cert['power_facts']))==expected_power,'power sign facts mismatch')
    known|=expected_power
    steps(cert['post_steps'])
    need(all((i,0) in known for i in range(n)),'incomplete final nonnegativity')
    return {'guards':len(cert['guards']),'source_variables':n,'pre_nonnegative':pre_count,
            'middle_nonnegative':mid_count,'final_nonnegative':n,'raw_rows_zero':zero,
            'raw_rows_restored':restored,'raw_variables':len(names),'seed_indices':len(interface['seeds']),
            'derived_indices':len(interface['derived']),'powers':len(pp),'bases':len(base_map)}

def check_projection(source,signed,cert,output,expanded,domain):
    expected_variables=list(source['variables']);expected_rows=list(source['residuals'])
    for v in domain['guards']:
        a,b,c=range(len(expected_variables),len(expected_variables)+3)
        expected_variables += [{'name':f'nonnegative.{v}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
        expected_rows.append({'label':f'nonnegative.{v}','terms':[[z,list(m)] for m,z in sorted({(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}.items())]})
    need(signed['domain']==output['domain']==expanded['domain']=='unrestricted integers','final domain')
    need(signed['variables']==expected_variables and signed['residuals']==expected_rows,'literal guard lift')
    need(sha(signed)==cert['input_sha256'] and sha(output)==cert['output_sha256'],'projection hashes')
    rows={i:collect(r['terms']) for i,r in enumerate(signed['residuals'])};deleted=set()
    for step in cert['steps']:
        rid,v=step['row_id'],step['variable'];restore=collect(step['restoration'])
        need(rid in rows and v not in deleted and all(v not in m for m in restore),'bad pivot')
        need(all(w not in deleted for m in restore for w in m),'reverse restoration uses deleted coordinate')
        defining=add(var(v),scale(restore,-1))
        need(rows[rid] in (defining,scale(defining,-1)),'pivot identity')
        nextrows={}
        for j,p in rows.items():
            if j==rid:continue
            new=evaluate(p,lambda w:restore if w==v else var(w))
            need(all(len(m)<=2 for m in new),'degree above two after projection')
            if new:nextrows[j]=new
        rows=nextrows;deleted.add(v)
    retained=cert['retained_original_variables'];need(retained==sorted({v for p in rows.values() for m in p for v in m}),'retained variable map')
    remap={v:i for i,v in enumerate(retained)}
    expected=[{'label':signed['residuals'][i]['label'],'terms':[[c,[remap[v] for v in m]] for m,c in sorted(p.items())]} for i,p in sorted(rows.items())]
    need(output['residuals']==expected,'target residual identities')
    need(output['variables']==[signed['variables'][v] for v in retained],'target names')
    need(cert['retained_original_rows']==sorted(rows),'retained rows')
    unused=sorted(set(range(len(signed['variables'])))-deleted-set(retained))
    need(unused==cert['unconstrained_removed'],'unused coordinates')
    total=add(*(mul(collect(r['terms']),collect(r['terms'])) for r in output['residuals']))
    need(collect(expanded['terms'])==total and len(expanded['terms'])==len(total),'complete collected polynomial')
    need(expanded['variables']==len(retained),'expanded dimension')
    degree=max(map(len,total));height=max(map(abs,total.values()))
    leading=next((m,c) for m,c in sorted(total.items()) if len(m)==degree)
    return {'variables':len(retained),'residuals':len(rows),'degree':degree,'monomials':len(total),
            'coefficient_height':height,'exact_degree_witness':{'monomial':list(leading[0]),'coefficient':leading[1]},'eliminations':len(deleted)}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--equations',type=Path,default=ROOT/'equations');ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    provenance_count=provenance();p=args.equations
    eq=load(ROOT/'upstream/source690/equation.json');domain=load(p/'domain_certificate.json')
    receipt=check_domain(eq,domain,load(ROOT/'upstream/source690/gate_ledger.json'),load(ROOT/'upstream/source690/interface.json'),load(ROOT/'upstream/source690/macro_inventory.json'))
    result=check_projection(eq,load(p/'signed_source.json'),load(p/'projection.json'),load(p/'equation.json'),load(p/'expanded_polynomial.json'),domain)
    receipt={'status':'PASS','domain':receipt,'polynomial':result,'authenticated_source_members':provenance_count,'optimized_python':not __debug__,
             'scope':'Exact finite identities and hypotheses of the ordinary delayed-power-sign proof; no consistency decision.'}
    if args.receipt:args.receipt.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))
if __name__=='__main__':main()
