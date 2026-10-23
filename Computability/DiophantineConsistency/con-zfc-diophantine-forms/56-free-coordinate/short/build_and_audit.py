#!/usr/bin/env python3
"""Compose the minimum-norm and squared-modulus reductions; audit the DAGs.

Standard library only.  These finite checks concern literal arithmetic, not
the inherited semantic compiler or a new formal verification of ZFC.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import gzip

ROOT = Path(__file__).resolve().parent


def check(b, message):
    if not b:
        raise ValueError(message)


def add(p, q, sign=1):
    r = dict(p)
    for mon, c in q.items():
        r[mon] = r.get(mon, 0) + sign*c
        if not r[mon]:
            del r[mon]
    return r


def mul(p, q):
    r = {}
    for a, c in p.items():
        for b, d in q.items():
            mon = tuple(x+y for x, y in zip(a, b))
            r[mon] = r.get(mon, 0) + c*d
    return {a:c for a,c in r.items() if c}


def quotient_replace(circuit, T):
    old = [
        ['auxiliary_Tf', '*', T, 'f'],
        ['auxiliary_Tf_minus_one', '-', 'auxiliary_Tf', 1],
        ['auxiliary_c_Tf', '*', 'R10a', 'auxiliary_Tf_minus_one'],
        ['auxiliary_R_f2', '*', 'r_lhs', 'L16'],
        ['aux_u_rhs', '-', 'auxiliary_c_Tf', 'auxiliary_R_f2'],
    ]
    rows = circuit['source']
    start = next(i for i, row in enumerate(rows) if row[0] == old[0][0])
    check(rows[start:start+5] == old, 'parent auxiliary matrix differs')
    new = [
        ['auxiliary_cT', '*', 'R10a', T],
        ['auxiliary_inner', '-', 'auxiliary_cT', 'r_lhs'],
        ['auxiliary_scaled', '*', 'L16', 'auxiliary_inner'],
        ['aux_u_rhs', '-', 'auxiliary_scaled', 'R10a'],
    ]
    return rows[:start] + new + rows[start+5:]


def build():
    old_gap = json.loads((ROOT/'upstream/gap_minima75.json').read_text())
    gap = dict(old_gap)
    rows = quotient_replace(old_gap, 'auxiliary_quotient')
    # Exactly the same auxiliary norm, factored to expose its degree23.
    # Both old and new suffixes cost six operations.
    start = next(i for i,r in enumerate(rows) if r[0]=='gap_y')
    end = next(i for i,r in enumerate(rows) if r[0]=='norm_aux')+1
    middle = rows[start:end]
    removed={'gap_y','aux_y2','H2','aux_square_gap','L17','norm_aux'}
    retained=[r for r in middle if r[0] not in removed]
    factored=[
        ['gap_y','+','aux_u_rhs','auxiliary_gap'],
        ['aux_y2','*','gap_y','gap_y'],
        ['twice_V_gap','+','aux_u_rhs','gap_y'],
        ['gap_product_aux','*','auxiliary_gap','twice_V_gap'],
        ['L17','*','R16','gap_product_aux'],
        ['norm_aux','-','aux_y2','L17'],
    ]
    rows=rows[:start]+retained+factored+rows[end:]
    gap.update(name='gap_minima74_squared_modulus_degree46',source=rows,
               coefficient_binding={'file':'../coefficients31/COEFFICIENT_BINDING.json',
                                    'aliases':{'Bm1':'beta','Kconstant':'K','MC':'MC','MF':'MF_source'}},
               provenance={'source':'upstream/gap_minima75.json',
                           'change':'Squared-modulus auxiliary quotient and an identical factored gap norm.'},
               operations=74,exact_degree=46,
               proof_scope='Ordinary mathematical existence equivalence, importing minimum norms, signed index/transport recovery, positive gap completeness, squared-modulus reconstruction and authentic whole package31 compiler tuple. No new formal proof.')
    gap.pop('ledger',None)
    grouped=dict(gap)
    g=[]
    for row in gap['source']:
        name,op,a,b=row
        if name in {'norm_main_sq','total1'}: continue
        if name=='index_transport':
            g.append(row)
            g.append(['main_index_transport','*','norm_main','index_transport'])
        elif name=='unit_error':
            g.append([name,'-','main_index_transport',1])
        elif name=='total2':
            g.append([name,'+','norm_first_sq','norm_aux_sq'])
        elif name=='polynomial':
            g.append([name,'-','total4',2])
        else: g.append(row)
    grouped.update(name='ordinary_gap_minima73_squared_modulus_degree54',source=g,
                   operations=73,exact_degree=54,
                   provenance={'source':'upstream/gap_minima75.json',
                               'change':'Squared-modulus quotient; move N1 from the nonzero norm square into the index/transport unit residual.'})
    return [grouped,gap]


def audit(circuit):
    witnesses=circuit['witnesses']; ports=circuit['fixed_numerals']
    names=witnesses+ports
    check(len(witnesses)==15 and len(ports)==4 and len(set(names))==19,'ports')
    zero=(0,)*19
    def constant(n): return {zero:n} if n else {}
    def variable(n):
        a=list(zero); a[names.index(n)]=1
        return {tuple(a):1}
    def power(p,n):
        r=constant(1)
        for _ in range(n): r=mul(r,p)
        return r
    state={n:(1 if n in witnesses else 0,variable(n)) for n in names}
    gate_map={r[0]:r for r in circuit['source']}
    exact={n:variable(n) for n in names}
    def expand(n):
        if type(n) is int: return constant(n)
        if n not in exact:
            _,op,a,b=gate_map[n]
            pa,pb=expand(a),expand(b)
            exact[n]=mul(pa,pb) if op=='*' else add(pa,pb,1 if op=='+' else -1)
        return exact[n]
    dep={}; count=Counter()
    def operand(a): return (0,constant(a)) if type(a) is int else state[a]
    for row in circuit['source']:
        check(len(row)==4,'row length')
        name,op,a,b=row
        check(name not in state and op in ('+','-','*'),'producer')
        da,pa=operand(a); db,pb=operand(b)
        if op=='*': deg,top=da+db,mul(pa,pb)
        else:
            deg=max(da,db)
            top=add(pa if da==deg else {},pb if db==deg else {},1 if op=='+' else -1)
        if name=='norm_main':
            p=expand(name)
            deg=max(sum(mon[:15]) for mon in p)
            top={mon:c for mon,c in p.items() if sum(mon[:15])==deg}
            check(deg==18,'main norm cancellation')
        check(all(sum(mon[:15])==deg for mon in top),'homogeneity')
        state[name]=(deg,top); dep[name]=(a,b); count[op]+=1
    live=set(); todo=[circuit['output']]
    while todo:
        n=todo.pop()
        if type(n) is not str or n in live: continue
        live.add(n); todo.extend(dep.get(n,()))
    check(live==set(state),'dead arithmetic or ports')
    degree,top=state[circuit['output']]
    grouped=circuit['name'].startswith('ordinary_')
    if grouped:
        Q=mul(variable('Bm1'),variable('Jrep'))
        C1=add(add(Q,variable('F'),-1),variable('alpha'),-1)
        transport=add(mul(variable('w'),C1),mul(variable('transport_quotient'),Q),-1)
        expected=constant(64)
        for n,e in [('gamma',2),('h',2),('w',6),('s',8)]:
            expected=mul(expected,power(variable(n),e))
        expected=mul(expected,power(Q,30))
        expected=mul(expected,power(add(variable('eta'),variable('zeta')),2))
        expected=mul(expected,power(transport,2))
        check(degree==54 and len(circuit['source'])==73,'grouped ordinary metrics')
    else:
        expected=constant(4)
        factors=[('i',0),('w',4),('s',6),('f',8),('auxiliary_quotient',2),('auxiliary_gap',2)]
        Q=mul(variable('Bm1'),variable('Jrep'))
        for n,e in factors: expected=mul(expected,power(variable(n),e))
        expected=mul(expected,power(Q,22))
        expected=mul(expected,power(add(variable('eta'),variable('zeta')),2))
        check(degree==46 and len(circuit['source'])==74,'gap metrics')
    check(top==expected,'leading homogeneous polynomial')
    check((ROOT/'generated'/circuit['coefficient_binding']['file']).is_file(),'coefficient binding')
    return {'name':circuit['name'],'positive_witnesses':15,'degree':degree,
            'operations':len(circuit['source']),'operation_counts':dict(sorted(count.items())),
            'all_gates_and_ports_live':True,'top_terms':len(top),
            'exact_degree_hypothesis':'beta != 0; the bound is attained by the displayed nonzero leading form',
            'local_auxiliary_pullback':'V_new(f,T)=V_old(f,f*T)',
            'proof_boundary':'The finite audit does not establish the inherited unbounded compiler or Con(ZFC).'}


def identity_check():
    # Independently expand the two local transformations as polynomials
    # in abstract c,T,R,f,V,e,U, keeping all exponents integral.
    names=['c','T','R','f','V','e','U']; zero=(0,)*len(names)
    def var(n):
        a=list(zero); a[names.index(n)]=1; return {tuple(a):1}
    c,T,R,f,V,e,U=map(var,names)
    one={zero:1}; f2=mul(f,f)
    old=add(mul(c,add(mul(mul(f,T),f),one,-1)),mul(R,f2),-1)
    new=add(mul(f2,add(mul(c,T),R,-1)),c,-1)
    check(old==new,'squared-modulus local identity')
    y=add(V,e)
    left=add(mul(U,add(mul(V,V),mul(y,y),-1)),mul(y,y))
    right=add(mul(y,y),mul(mul(U,e),add(V,y)),-1)
    check(left==right,'gap identity')


def coefficient_check(dirname):
    directory=ROOT/dirname
    binding=json.loads((directory/'COEFFICIENT_BINDING.json').read_text())
    rows=binding.get('files') or binding['materialization']['files']
    values={}
    for row in rows:
        compressed=(directory/row['file']).read_bytes()
        raw=gzip.decompress(compressed)
        check(hashlib.sha256(compressed).hexdigest()==row['gzip_sha256'],'compressed coefficient hash')
        check(hashlib.sha256(raw).hexdigest()==row['sha256'],'coefficient hash')
        check(len(raw)==row['raw_bytes'],'coefficient byte count')
        value=int.from_bytes(raw,'little')
        check(value.bit_length()==row.get('bit_length',row.get('bits')),'coefficient bit length')
        values[row['port']]=value
    check(set(values)=={'beta','K','MC','MF_source'},'whole coefficient tuple')
    check(values['beta']==(1<<binding['d'])-1,'positive fixed beta')
    check(values['MC']%4==2,'low mask phase')
    check((values['MF_source']-values['beta'])%8==4,'already shifted high mask')
    return {'directory':dirname,'d':binding['d'],'payloads_authenticated':4,
            'beta_positive':True,'mask_phase_checked':True}


def main():
    manifest=json.loads((ROOT/'SOURCES.json').read_text())
    for item in manifest['sources']:
        check(hashlib.sha256((ROOT/item['target']).read_bytes()).hexdigest()==item['sha256'], 'upstream byte mismatch')
    identity_check()
    coefficients=[coefficient_check('coefficients31')]
    receipts=[]
    for circuit in build():
        receipt=audit(circuit)
        file=ROOT/'generated'/(circuit['name']+'.json')
        file.write_text(json.dumps(circuit,indent=2)+'\n')
        receipt['circuit_sha256']=hashlib.sha256(file.read_bytes()).hexdigest()
        receipts.append(receipt)
    (ROOT/'generated/AUDIT.json').write_text(json.dumps(receipts,indent=2)+'\n')
    (ROOT/'generated/COEFFICIENT_AUDIT.json').write_text(json.dumps(coefficients,indent=2)+'\n')
    print(json.dumps(receipts,indent=2))


if __name__=='__main__': main()
