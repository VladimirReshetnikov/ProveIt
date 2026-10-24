#!/usr/bin/env python3
"""Independent verification of selected guards and signed monic projection.

No builder, optimizer, supplied expansion routine, or candidate module is
imported. Python standard library only. The upstream natural polynomial is
authenticated to its frozen literal bytes.
"""
from collections import Counter, defaultdict
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
import argparse, json

PARENT_SHA='8b983a7357d16201ac5b7dfa6e12e809692ee26a29383ae84e2af2b891994f48'

def need(ok,why):
    if not ok: raise ValueError(why)

def canonical(obj):
    return (json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()

def poly(terms):
    out=defaultdict(int)
    for c,m in terms:
        need(type(c) is int,'coefficient is not a literal integer')
        need(all(type(i) is int and i>=0 for i in m),'invalid monomial index')
        out[tuple(sorted(m))]+=c
    return {m:c for m,c in out.items() if c}

def terms(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]

def minus(p):return {m:-c for m,c in p.items()}

def multiply(p,q):
    out=defaultdict(int)
    for a,c in p.items():
        for b,d in q.items():out[tuple(sorted(a+b))]+=c*d
    return {m:c for m,c in out.items() if c}

def substitute(p,x,value):
    out=defaultdict(int)
    for m,c in p.items():
        part={():c}
        for y in m: part=multiply(part,value if x==y else {(y,):1})
        for n,d in part.items():out[n]+=d
    return {m:c for m,c in out.items() if c}

def expansion(rows):
    # Symmetric square expansion, distinct from the supplied ordered-pair builder.
    out=defaultdict(int)
    for row in rows:
        ps=sorted(poly(row['terms']).items())
        for j,(m,c) in enumerate(ps):
            out[tuple(sorted(m+m))]+=c*c
            for n,d in ps[:j]:out[tuple(sorted(m+n))]+=2*c*d
    return {m:c for m,c in out.items() if c}

def domain_check(parent,eq,cert,hashes=True):
    n=len(parent['variables']);nr=len(parent['residuals'])
    need(parent['domain']=='nonnegative integers','parent domain')
    need(eq['domain']=='unrestricted integers','integer target domain')
    if hashes:
        need(sha256(canonical(parent)).hexdigest()==cert['natural_parent_sha256'],'parent certificate hash')
        need(sha256(canonical(eq)).hexdigest()==cert['integer_equation_sha256'],'integer certificate hash')
    need(cert['original_variables']==n and cert['original_rows']==nr,'source dimensions')
    need(eq['variables'][:n]==parent['variables'],'source coordinates changed')
    need(eq['residuals'][:nr]==parent['residuals'],'source rows changed')
    guards=cert['guards'];known=set();used=set();seenrows=set()
    need(len(eq['variables'])==n+3*len(guards),'guard variable count')
    need(len(eq['residuals'])==nr+len(guards),'guard row count')
    for g in guards:
        x=g['input'];abc=g['auxiliaries'];ri=g['row']
        need(0<=x<n and x not in known,'duplicate or invalid guarded source coordinate')
        need(len(abc)==3 and len(set(abc))==3,'guard auxiliary triple')
        need(all(n<=j<len(eq['variables']) and j not in used for j in abc),'nonfresh guard auxiliary')
        need(nr<=ri<len(eq['residuals']) and ri not in seenrows,'guard row allocation')
        a,b,c=abc;expected={(x,):1,(a,a):-1,(b,b):-1,(c,):-1,(c,c):-1}
        need(poly(eq['residuals'][ri]['terms'])==expected,'literal three-coordinate guard')
        known.add(x);used.update(abc);seenrows.add(ri)
    need(used==set(range(n,len(eq['variables']))),'unguarded extra coordinate')
    need(seenrows==set(range(nr,len(eq['residuals']))),'unaccounted extra row')
    for k,r in enumerate(cert['inference']):
        x=r['target'];ri=r['row'];D=r['positive_multiplier'];P=poly(r['scaled_definition'])
        need(0<=x<n and x not in known,'duplicate or invalid inference target')
        need(0<=ri<nr,'inference source row')
        row=poly(parent['residuals'][ri]['terms']);pivot=row.get((x,),0)
        need(pivot!=0 and D==pivot*pivot,'strictly positive constant multiplier')
        need(all(x not in m and all(0<=i<n for i in m) for m in P),'inference target recursion')
        need(all(c>=0 for c in P.values()),'negative inference coefficient')
        expect={m:-pivot*c for m,c in row.items() if m!=(x,)}
        need(P==expect,'exact scaled row identity')
        odd={i for m in P for i,k in Counter(m).items() if k%2}
        need(r['dependencies']==sorted(odd),'incorrect odd-power dependency list')
        need(odd<=known,'inference depends on unproved nonnegative coordinate')
        known.add(x)
    need(known==set(range(n)),'not every original coordinate is proved nonnegative')
    # Optional optimality claim is strictly relative to this literal-row rule
    # family. Enumerate every possible head, without using candidate metadata.
    eligible_heads=set()
    for literal in parent['residuals']:
        row=poly(literal['terms'])
        for monomial,pivot in row.items():
            if len(monomial)!=1:continue
            x=monomial[0];tail={m:c for m,c in row.items() if m!=(x,)}
            if any(x in m for m in tail):continue
            if all(-pivot*c>=0 for c in tail.values()):eligible_heads.add(x)
    required=set(range(n))-eligible_heads
    need({g['input'] for g in guards}==required,
         'guard set does not attain literal-row-rule lower bound')
    return {'guarded':len(guards),'inferred':len(cert['inference']),'natural_coordinates':n,
            'minimum_guards_within_scaled_literal_row_rule_family':len(required)}

def projection_check(parent,target,cert,hashes=True):
    need(parent['domain']==target['domain']=='unrestricted integers','projection domain')
    if hashes:
        need(sha256(canonical(parent)).hexdigest()==cert['input_sha256'],'projection input hash')
        need(sha256(canonical(target)).hexdigest()==cert['output_sha256'],'projection output hash')
    rows={i:poly(r['terms']) for i,r in enumerate(parent['residuals'])}
    alive=set(range(len(parent['variables'])));degrees=Counter()
    for step in cert['steps']:
        x=step['variable'];ri=step['row_id'];P=poly(step['restoration'])
        need(x in alive and ri in rows,'deleted pivot no longer exists')
        need(all(i in alive and i!=x for m in P for i in m),'restoration uses invalid coordinate')
        degree=max(map(len,P),default=0)
        need(degree<=2,'restoration degree exceeds two')
        expected={(x,):1}
        for m,c in P.items():expected[m]=expected.get(m,0)-c
        expected={m:c for m,c in expected.items() if c}
        need(rows[ri] in (expected,minus(expected)),'pivot is not exact monic relation')
        new={}
        for j,row in rows.items():
            if j==ri:continue
            p=substitute(row,x,P)
            need(max(map(len,p),default=0)<=2,'substitution raises residual degree')
            if p:new[j]=p
        rows=new;alive.remove(x);degrees[degree]+=1
    used=sorted({i for row in rows.values() for m in row for i in m})
    need(used==cert['retained_original_variables'],'retained variable list')
    need(sorted(alive-set(used))==cert['unconstrained_removed'],'free-coordinate removal')
    need(sorted(rows)==cert['retained_original_rows'],'retained row list')
    remap={old:new for new,old in enumerate(used)}
    final=[{'label':parent['residuals'][i]['label'],
            'terms':[[c,[remap[j] for j in m]] for m,c in sorted(p.items())]}
           for i,p in sorted(rows.items())]
    need(target['residuals']==final,'projected residual list differs')
    need(target['variables']==[parent['variables'][i] for i in used],'projected variables differ')
    return {'eliminations':len(cert['steps']),'restoration_degrees':dict(sorted(degrees.items())),
            'free_coordinates_removed':len(cert['unconstrained_removed'])}

def polynomial_check(eq,expanded):
    p=expansion(eq['residuals']);n=len(eq['variables'])
    need(eq['domain'] in ('nonnegative integers','unrestricted integers'),'unknown polynomial domain')
    need(expanded['domain']==eq['domain'],'expanded polynomial domain differs')
    need(eq['polynomial']=='sum(square(row) for row in residuals)','sum-of-squares declaration differs')
    need(all(len(m)<=2 for r in eq['residuals'] for c,m in r['terms']),'nonquadratic residual')
    need(all(all(i<n for i in m) for m in p),'expanded variable range')
    need({i for r in eq['residuals'] for c,m in r['terms'] if c for i in m}==set(range(n)),
         'declared coordinate absent from residuals')
    need({i for m in p for i in m}==set(range(n)),'declared coordinate absent from polynomial')
    need(expanded['variables']==n,'expanded variable count')
    need(expanded['terms']==terms(p),'full expanded coefficient list differs')
    metrics={'variables':n,'quadratic_rows':len(eq['residuals']),
             'exact_degree':max(map(len,p),default=0),'expanded_monomials':len(p),
             'max_abs_expanded_coefficient':max(map(abs,p.values()),default=0),
             'max_abs_row_coefficient':max(abs(c) for r in eq['residuals'] for c,m in r['terms'])}
    for k,v in metrics.items():need(eq['metrics'][k]==v,'metric mismatch '+k)
    need(metrics['exact_degree']==4,'not quartic')
    return metrics

def rejected(fn,label):
    try:fn()
    except ValueError:return True
    raise ValueError('Corruption control accepted: '+label)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path)
    ap.add_argument('--receipt',type=Path);args=ap.parse_args();root=args.directory
    def read(p):return json.loads((root/p).read_text())
    raw=(root/'source/parent_natural.json').read_bytes()
    need(sha256(raw).hexdigest()==PARENT_SHA,'frozen synchronized522 parent bytes changed')
    parent=json.loads(raw);inp=read('input/equation.json');dc=read('input/domain_conversion_certificate.json')
    out=read('output/equation.json');pc=read('output/terminal_elimination_certificate.json')
    ie=read('input/expanded_polynomial.json');oe=read('output/expanded_polynomial.json')
    guard=domain_check(parent,inp,dc);projection=projection_check(inp,out,pc)
    input_metrics=polynomial_check(inp,ie);output_metrics=polynomial_check(out,oe)
    bad=deepcopy(dc);bad['inference'][0]['scaled_definition'][0][0]+=-2
    rejected(lambda:domain_check(parent,inp,bad,False),'negative inference coefficient')
    bad=deepcopy(inp);bad['residuals'][dc['guards'][0]['row']]['terms'][1][0]=1
    rejected(lambda:domain_check(parent,bad,dc,False),'wrong guard sign')
    bad=deepcopy(pc);bad['steps'][0]['restoration'][0][0]+=1
    rejected(lambda:projection_check(inp,out,bad,False),'changed monic restoration')
    bad=deepcopy(oe);bad['terms'][0][0]+=1
    rejected(lambda:polynomial_check(out,bad),'expanded coefficient mutation')
    receipt={'status':'PASS','independent_authorship':'separate assistant reviewer',
             'scope':'Exact finite arithmetic, ordered nonnegativity and inverse polynomial substitution; inherited calculus theorem not re-proved',
             'frozen_parent_sha256':PARENT_SHA,'domain_inference':guard,'projection':projection,
             'input_metrics':input_metrics,'output_metrics':output_metrics,'corruption_controls_rejected':4,
             'file_sha256':{p:sha256((root/p).read_bytes()).hexdigest() for p in
                ('input/equation.json','input/domain_conversion_certificate.json','output/equation.json',
                 'output/terminal_elimination_certificate.json','output/expanded_polynomial.json')}}
    result=json.dumps(receipt,indent=2,sort_keys=True)+'\n'
    if args.receipt:args.receipt.write_text(result)
    print(result)

if __name__=='__main__':main()
