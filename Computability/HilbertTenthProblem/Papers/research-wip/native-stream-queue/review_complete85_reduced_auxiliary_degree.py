"""Independent 85-gate deformation/source/degree review; predecessors remain inert."""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

AUTHOR = {
 'complete85_reduced_auxiliary_degree.py':'2d3348d2148ad7bd9c95129bf197dbba2033f2bc735c5d2691473ca6c4aea7a1',
 'complete85_reduced_auxiliary_degree.json':'eac8cfd977ac4d932b38aa5ecdfe0d52b6adf72f52a0d63d856589f62012f8c9',
 'complete85_reduced_auxiliary_degree.md':'b86b6058d06b1c7b3c99c270146340c3166c771ea23f5366ac78d9de21532b24',
}
PARENT = {
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
}
FACTORS = ['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']

def check(ok, label):
    if not ok: raise ValueError(label)
def sha(b): return hashlib.sha256(b).hexdigest()
def canonical(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(path):
    def unique(items):
        d={}
        for k,v in items:
            check(k not in d,'duplicate JSON key');d[k]=v
        return d
    def reject(x): raise ValueError('noninteger JSON '+x)
    return json.loads(path.read_text(),object_pairs_hook=unique,parse_float=reject,parse_constant=reject)
def const(n): return {():n} if n else {}
def var(n): return {(n,):1}
def add(a,b,sign=1):
    d=dict(a)
    for m,c in b.items(): d[m]=d.get(m,0)+sign*c
    return {m:c for m,c in d.items() if c}
def mul(a,b):
    d={}
    for m,c in a.items():
        for n,v in b.items():
            key=tuple(sorted(m+n));d[key]=d.get(key,0)+c*v
    return {m:c for m,c in d.items() if c}
def prod(*xs):
    r=const(1)
    for x in xs:r=mul(r,x)
    return r
def power(x,n):return prod(*[x for _ in range(n)])
def rec(p):return [[list(m),c] for m,c in sorted(p.items())]
def subst(p,images):
    r={}
    for m,c in p.items():r=add(r,prod(const(c),*(images.get(n,var(n)) for n in m)))
    return r
def symbolic(rows,free,cuts):
    definitions={r[0]:r for r in rows};memo={n:var(n) for n in free};memo.update(cuts);visited=set()
    def at(n):
        if type(n)is int:return const(n)
        if n not in memo:
            visited.add(n);_,op,a,b=definitions[n];x,y=at(a),at(b)
            memo[n]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
        return memo[n]
    return at,visited
def graph(rows,free,output,fixed):
    degrees={n:int(n not in fixed) for n in free};d={}
    for r in rows:
        check(type(r)is list and len(r)==4,'binary source row');n,o,a,b=r
        check(type(n)is str and n not in degrees and o in ['+','-','*'],'SSA opcode')
        check(all(type(v)is int or type(v)is str and v in degrees for v in [a,b]),'topology')
        da,db=(0 if type(v)is int else degrees[v] for v in [a,b]);degrees[n]=da+db if o=='*' else max(da,db);d[n]=r
    live=set()
    def walk(n):
        if type(n)is int or n in live:return
        live.add(n)
        if n in d:walk(d[n][2]);walk(d[n][3])
    walk(output);check(live==set(degrees),'every source row and supplied port live')
    return d,degrees

def source_identities(old,rows):
    factors=[n for n in FACTORS if n not in ['norm_aux','norm_strong']]
    cuts=['A','R10a','r_lhs']+factors
    maps={n:var(n) for n in cuts}
    old_at,old_seen=symbolic(old['source'],old['free'],maps)
    new_at,new_seen=symbolic(rows,old['free'],maps)
    before,after=old_at(old['output']),new_at(old['output'])
    A,c,R,i,f,T,y=[var(n) for n in ['A','R10a','r_lhs','i','f','auxiliary_quotient','y_aux']]
    Q=prod(power(A,2),power(i,2),power(c,4))
    V=add(add(prod(c,T,f),c,-1),prod(R,f,f),-1)
    gap=add(power(V,2),power(y,2),-1)
    oldNa=add(prod(Q,gap),power(y,2));newNa=add(prod(A,add(power(f,2),const(1),-1),gap),power(y,2))
    Ns=add(prod(A,f,f),Q,-1);P5=prod(*(var(n) for n in factors))
    check(before==add(prod(P5,oldNa,Ns),A,-1),'literal old full polynomial')
    check(after==add(prod(P5,newNa,Ns),A,-1),'literal new full polynomial')
    correction=prod(P5,Ns,add(Ns,A,-1),gap)
    check(add(after,before,-1)==correction and correction,'exact nonzero full correction')
    check(add(newNa,oldNa,-1)==prod(add(Ns,A,-1),gap),'auxiliary correction')
    check(new_at('auxiliary_reduced_coefficient')==prod(A,add(power(f,2),const(1),-1)),'actual new coefficient binding')
    check(not subst(before,{'A':{}}) and not subst(after,{'A':{}}),'both outputs vanish on Delta=0')
    return dict(cuts=cuts,old_expanded_ancestors=sorted(old_seen),new_expanded_ancestors=sorted(new_seen),
                full_old=rec(before),full_new=rec(after),difference=rec(correction),both_outputs_zero_at_Delta_zero=True)

def leading_forms(packet,rows):
    fixed=set(packet['fixed_numerals']);free=packet['free']
    cut_weights=[
        {'UM':6,'ksn2':5,'R10b':1},
        {'R12':6,'R10a':5,'wn2':2,'gamma_sum':1},
        {'R12':6,'odd_index':1,'W':1},
        {'A':12,'R10a':5,'r_lhs':4},
        {'R10b':1,'UM':6,'r_lhs':4},
        {'marked_rhs':1,'repunit':1,'q_minus_F':1},
        {'A':12,'R10a':5},
    ]
    Q,k,gamma,w,s=map(var,['Q0','k0','gamma0','w','s'])
    C1=var('Q0')
    for n in ['F','Z','alpha']:C1=add(C1,var(n),-1)
    C1=add(C1,prod(var('twice_cell_bits'),var('x')),-1)
    images={'UM':prod(w,s,power(Q,4)),'ksn2':prod(k,s,power(Q,3)),
            'R10b':k,'R12':prod(w,s,power(Q,4)),'R10a':prod(k,s,power(Q,3)),
            'wn2':prod(w,Q),'gamma_sum':gamma,'A':prod(power(w,2),power(s,2),power(Q,8)),
            'marked_rhs':C1,'repunit':Q}
    expand_macros={'Q0':prod(var('Bm1'),var('Jrep')),
                   'k0':add(var('eta'),var('zeta')),'gamma0':add(var('rho'),var('sigma'))}
    prefix_at,_=symbolic(rows,free,{})
    all_weights={n:e for weights in cut_weights for n,e in weights.items()}
    prefix_records=[]
    for name,expected_degree in all_weights.items():
        actual=prefix_at(name)
        degree=lambda m:sum(n not in fixed for n in m)
        top_degree=max(degree(m) for m in actual)
        top={m:c for m,c in actual.items() if degree(m)==top_degree}
        check(top_degree==expected_degree,'actual full-prefix cut degree '+name)
        if name in images:check(top==subst(images[name],expand_macros),'actual prefix leader substitution '+name)
        prefix_records.append(dict(name=name,degree=top_degree,leader=rec(top)))
    expected=[
        prod(const(-1),power(w,2),power(s,4),power(Q,14),power(k,2)),
        prod(const(8),power(w,2),power(s,3),power(Q,11),k,gamma),
        prod(const(-4),power(var('delta'),2),power(w,5),power(s,5),power(Q,20)),
        prod(power(w,2),power(s,4),power(Q,14),power(k,2),power(var('auxiliary_quotient'),2),power(var('f'),4)),
        prod(const(-1),var('h'),w,s,power(Q,4)),
        add(prod(w,C1),prod(var('transport_quotient'),Q),-1),
        prod(const(-1),power(var('i'),2),power(w,4),power(s,8),power(Q,28),power(k,4)),
    ]
    exact=[22,18,32,28,7,2,46];records=[];tops=[]
    for name,weights,want,want_degree in zip(FACTORS,cut_weights,expected,exact):
        at,seen=symbolic(rows,free,{n:var(n) for n in weights})
        poly=at(name);degree_weights={n:int(n not in fixed) for n in free};degree_weights.update(weights)
        degree=lambda m:sum(degree_weights[n] for n in m)
        top_degree=max(degree(m) for m in poly);top={m:a for m,a in poly.items() if degree(m)==top_degree}
        substituted=subst(top,images)
        check(top_degree==want_degree and substituted==want,'source-expanded factor leader '+name)
        tops.append(substituted);records.append(dict(name=name,cut_weights=weights,expanded_ancestors=sorted(seen),
                  full_cut_polynomial=rec(poly),cut_leader=rec(top),actual_leader=rec(substituted),degree=top_degree))
    combined=prod(*tops)
    expected_full=prod(const(32),power(Q,91),var('h'),gamma,power(var('delta'),2),power(var('i'),2),power(k,9),
        power(w,16),power(s,25),expected[5],power(var('auxiliary_quotient'),2),power(var('f'),4))
    check(combined==expected_full and sum(exact)==155,'complete uniform leader product')
    expanded=subst(combined,{'Q0':prod(var('Bm1'),var('Jrep')),
                            'k0':add(var('eta'),var('zeta')),
                            'gamma0':add(var('rho'),var('sigma'))})
    target={ 'Bm1':92,'Jrep':92,'h':1,'rho':1,'delta':2,'i':2,'eta':9,'w':16,'s':25,
             'transport_quotient':1,'auxiliary_quotient':2,'f':4 }
    monomial=tuple(sorted(n for n,e in target.items() for _ in range(e)))
    check(expanded.get(monomial)==-32,'distinguished coefficient -32 Bm1^92')
    dynamic=tuple(n for n in monomial if n not in fixed)
    check([(m,c) for m,c in expanded.items() if tuple(n for n in m if n not in fixed)==dynamic]==[(monomial,-32)],
          'no other fixed-numeral coefficient on the distinguished dynamic monomial')
    check(all(sum(n not in fixed for n in m)==155 for m in expanded),'all expanded leading terms degree155')
    return dict(actual_prefix_cuts=prefix_records,factors=records,uniform_leader=rec(combined),expanded_leader=rec(expanded),
                distinguished_monomial=target,distinguished_integer_coefficient=-32,exact_degree=155)

def dense_checks(packet,rows,uniform):
    fixed=packet['fixed_numerals'];all_rows=packet['source'];out=[]
    for prime,shift in [(1000000007,11),(1000000009,37)]:
        values={n:((j+shift)*17+3)%prime for j,n in enumerate(packet['free'])}
        def operate(rows):
            polynomials={n:[values[n]] if n in fixed else [0,values[n]] for n in packet['free']}
            for name,op,a,b in rows:
                x,y=([v%prime] if type(v)is int else polynomials[v] for v in [a,b])
                if op=='*':
                    z=[0]*(len(x)+len(y)-1)
                    for j,u in enumerate(x):
                        for k,v in enumerate(y):z[j+k]=(z[j+k]+u*v)%prime
                else:
                    z=[((x[j] if j<len(x) else 0)+(1 if op=='+' else -1)*(y[j] if j<len(y) else 0))%prime for j in range(max(len(x),len(y)))]
                while len(z)>1 and not z[-1]:z.pop()
                polynomials[name]=z
            return polynomials
        old,new=operate(all_rows),operate(rows)
        check([len(new[n])-1 for n in FACTORS]==[22,18,32,28,7,2,46],'dense seven factor degrees')
        check(len(old[packet['output']])-1==187 and len(new[packet['output']])-1==155,'dense full polynomial degrees')
        leader={tuple(m):c for m,c in uniform['expanded_leader']}
        expected=0
        for m,c in leader.items():
            v=c
            for n in m:v=v*values[n]%prime
            expected=(expected+v)%prime
        check(new[packet['output']][-1]==expected and expected!=0,'dense full leading coefficient')
        out.append(dict(prime=prime,assignment=values,parent_degree=187,child_degree=155,
                        factor_degrees=[len(new[n])-1 for n in FACTORS],leading_coefficient=expected))
    return out

def full_value_checks(parent,rows):
    changed={'L17','norm_aux','norm_four','norm_product','all_units','seven_units','polynomial'}
    retained=[r[0] for r in parent['source'] if r[0] not in changed]
    check(len(retained)==77,'all77 unaffected parent registers')
    records=[]
    def evaluate(source,values):
        e=dict(values)
        for n,o,a,b in source:
            a,b=(v if type(v)is int else e[v] for v in [a,b])
            e[n]=a*b if o=='*' else a+b if o=='+' else a-b
        return e
    for j in range(32):
        values={n:Fraction(((k+3)*(j+5))%11-5,1 if j<16 else (k+j)%3+1) for k,n in enumerate(parent['free'])}
        a,b=evaluate(parent['source'],values),evaluate(rows,values)
        check(all(a[n]==b[n] for n in retained),'retained value comparison')
        exterior=1
        for n in FACTORS:
            if n not in ['norm_aux','norm_strong']:exterior*=a[n]
        correction=exterior*a['norm_strong']*(a['norm_strong']-a['A'])*a['aux_square_gap']
        check(b['polynomial']-a['polynomial']==correction,'complete signed/rational correction')
        records.append(dict(case=j,rational=j>=16,nonzero_correction=bool(correction),
           old_output=[a['polynomial'].numerator,a['polynomial'].denominator],
           new_output=[b['polynomial'].numerator,b['polynomial'].denominator]))
    check(any(v['nonzero_correction'] for v in records),'whole polynomials are distinct')
    return records

def build(root,author):
    check(len(AUTHOR)==3,'final author pins required')
    for name,h in AUTHOR.items():check(sha((author/name).read_bytes())==h,'author pin '+name)
    for name,h in PARENT.items():check(sha((root/name).read_bytes())==h,'inert parent pin '+name)
    old=read(root/'complete84_scaled_strong_output.json')['packet']
    new_receipt=read(author/'complete85_reduced_auxiliary_degree.json')
    check(new_receipt['source_sha256']==AUTHOR['complete85_reduced_auxiliary_degree.py'],'author helper-byte binding')
    check(len(new_receipt['pins'])==6 and all(new_receipt['pins'][n]==h for n,h in PARENT.items()),'author dependency set')
    for n,h in new_receipt['pins'].items():check(sha((root/n).read_bytes())==h,'inert semantic/source dependency '+n)
    child=new_receipt['packet']
    rows=[]
    for row in old['source']:
        if row[0]=='L17':
            rows.extend([['auxiliary_reduced_coefficient','-','scaled_f_square','A'],['L17','*','auxiliary_reduced_coefficient','aux_square_gap']])
        else:rows.append(list(row))
    check(rows==child['source'],'complete reconstructed85 array')
    check(child['source_sha256']==sha(canonical(rows)) and new_receipt['parent_source_sha256']==sha(canonical(old['source'])),'whole source hashes')
    for key in ['free','fixed_numerals','ordinary_input','witnesses','output']:
        check(child[key]==old[key],'unchanged supplied/fixed/output interface '+key)
    check(child['ordinary_input']=='x' and len(child['witnesses'])==18 and len(child['fixed_numerals'])==6,'ordinary positive input/18 witnesses')
    check(child['same_positive_zero_tuples'] is True and child['unrestricted_signed_zero_equivalence'] is True and
          child['full_polynomial_identity'] is False and child['coordinate_map']=='identity','exact equivalence scopes')
    definitions,naive=graph(rows,old['free'],old['output'],set(old['fixed_numerals']))
    check(len(rows)==85 and sum(r[1]=='*' for r in rows)==47 and naive[old['output']]==165,'complete85 ledger and gate bound')
    old_definitions={r[0]:r for r in old['source']}
    check({n for n in old_definitions if old_definitions[n]!=definitions[n]}=={'L17'},'only one old definition changed')
    check(set(definitions)-set(old_definitions)=={'auxiliary_reduced_coefficient'} and not set(old_definitions)-set(definitions),'one addition no removed rows')
    check([r[0] for r in rows if 'R16' in r[2:]]==['norm_strong'],'R16 remains live/paid')
    final_names=['norm_pair','norm_triple','norm_four','norm_product','all_units','seven_units','polynomial']
    check(all(definitions[n]==old_definitions[n] for n in final_names),'all seven literal finalizer rows')
    check(child['ledger']==dict(total=85,M=47,A=38,core_M=41,core_A=37,core_total=78,finalizer_M=6,finalizer_A=1,finalizer_total=7),'full producer/finalizer accounting')
    exact=source_identities(old,rows);leaders=leading_forms(old,rows);dense=dense_checks(old,rows,leaders)
    check(child['exact_degree']==new_receipt['degree']['exact_degree']==155 and new_receipt['degree']['naive_degree_bound']==165,'degree contract')
    check(child['factor_exact_degrees']==new_receipt['degree']['factor_degrees']==[v['degree'] for v in leaders['factors']],'all7 exact factor degrees')
    def author_poly(items):
        out={}
        for item in items:
            monomial=tuple(sorted(n for n,e in item['powers'].items() for _ in range(e)))
            check(monomial not in out,'duplicate saved polynomial monomial');out[monomial]=item['coefficient']
        return out
    for factor in leaders['factors']:
        formal={tuple(m):c for m,c in factor['actual_leader']}
        expanded=subst(formal,{'Q0':prod(var('Bm1'),var('Jrep')),'k0':add(var('eta'),var('zeta')),'gamma0':add(var('rho'),var('sigma'))})
        check(expanded==author_poly(new_receipt['degree']['factor_leaders'][factor['name']]),'saved factor leader '+factor['name'])
    check({tuple(m):c for m,c in leaders['expanded_leader']}==author_poly(new_receipt['degree']['full_leader']),'full author symbolic leader')
    mod4=[]
    for a in range(4):
        for f in range(4):
            for i in range(4):
                for c in range(4):
                    Delta=((a+1)*(a+3))%4;residue=(f*f-Delta*i*i*c**4)%4
                    check(Delta in [0,3] and residue!=3,'strong negative-unit exclusion modulo4')
                    mod4.append([a,f,i,c,Delta,residue])
    check(mod4==new_receipt['polynomial_proof']['mod4_cases'],'all256 negative-unit residue cases')
    values=full_value_checks(old,rows)
    return dict(status='PASS_INDEPENDENT_REDUCED_AUXILIARY_DEGREE',source_sha256=sha(Path(__file__).read_bytes()),
                author_pins=AUTHOR,parent_pins=PARENT,inert_semantic_pins=new_receipt['pins'],source=rows,unchanged_interface=old['free'],
                counts=dict(total=85,M=47,A=38,witnesses=18),naive_degree=165,source_identities=exact,
                degree=leaders,dense_diagnostics=dense,full_value_checks=values,negative_unit_mod4=mod4,
                scope=dict(frozen_execution=False,diagnostic_numerals_are_compiler_recipes=False,all_ring_output_equality=False))

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--author-root',type=Path)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
    a=p.parse_args();result=build(a.root,a.author_root or a.root)
    if a.output:
        with a.output.open('x') as f:f.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
    else:check(canonical(result)==canonical(read(a.expect)),'exact independent receipt')
    print(result['status'],'85=47M38A; exact degree155; same positive zero set')
if __name__=='__main__':main()
