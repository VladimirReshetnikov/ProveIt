#!/usr/bin/env python3
"""Independent exact audit of selective source encoding; no upstream code executed."""
import ast, collections, hashlib, itertools, json, math
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SOURCE_PIN='124c07c0b77a9e20e84676514d8b1ff78536ea3f'
CANONICAL_CODE_SHA256='53cfdccbb252fd3f6ebe87ae0bb9dad8b2fdfc8c6168f668029add30ed339e25'
EXPECTED_SOURCES={
    'upstream_parent_quartic31.json':('1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287','4115733a43df47eeefbde24dafbbd770a8eef773'),
    'upstream_QUADRATIC_TARGETS.json':('56de00c50e9ea1c213bd4c98ae744f82c497259cdd4409b0fdb1fd8f55c921a0','7a2133ea122cb3f06fcac8b891fc16a5fbefd368'),
}

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def verify_source_pins():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    require(pins['commit']==SOURCE_PIN,'wrong repository pin')
    require(pins['repository']=='VladimirReshetnikov/ProveIt','wrong repository')
    require(len(pins['files'])==len(EXPECTED_SOURCES),'wrong source pin count')
    require({r['local_path'] for r in pins['files']}==set(EXPECTED_SOURCES),'wrong source pin paths')
    for row in pins['files']:
        path=ROOT/row['local_path'];data=path.read_bytes()
        digest,blob=EXPECTED_SOURCES[row['local_path']]
        require(sha(path)==row['sha256']==digest,'source SHA256 mismatch: '+path.name)
        require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob_sha']==blob,'Git blob mismatch: '+path.name)
        require(len(data)==row['bytes'],'source byte count mismatch')

def require(ok,message):
    if not ok: raise ValueError(message)

def port_polynomial(text, names, aliases=None):
    zero=(0,)*len(names)
    def add(p,q,sign=1):
        z=dict(p)
        for a,c in q.items():z[a]=z.get(a,0)+sign*c
        return {a:c for a,c in z.items() if c}
    def mul(p,q):
        z=collections.defaultdict(int)
        for a,c in p.items():
            for b,d in q.items():z[tuple(x+y for x,y in zip(a,b))]+=c*d
        return {a:c for a,c in z.items() if c}
    def visit(t):
        if isinstance(t,ast.Constant) and type(t.value)==int:return {zero:t.value} if t.value else {}
        if isinstance(t,ast.Name):
            if aliases and t.id in aliases:
                return visit(ast.parse(aliases[t.id].replace('^','**'),mode='eval').body)
            a=list(zero);a[names.index(t.id)]=1;return {tuple(a):1}
        if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return {a:-c for a,c in visit(t.operand).items()}
        if isinstance(t,ast.BinOp):
            p=visit(t.left)
            if isinstance(t.op,ast.Pow):
                require(isinstance(t.right,ast.Constant) and type(t.right.value)==int and 0<=t.right.value<=4,'bad power')
                q={zero:1}
                for _ in range(t.right.value):q=mul(q,p)
                return q
            q=visit(t.right)
            if isinstance(t.op,ast.Add):return add(p,q)
            if isinstance(t.op,ast.Sub):return add(p,q,-1)
            if isinstance(t.op,ast.Mult):return mul(p,q)
        raise ValueError(ast.dump(t))
    return visit(ast.parse(text,mode='eval').body)

def shifted_source(source):
    n=len(source['variables']);blocks={}
    for eq in source['equations']:
        shifted=collections.defaultdict(int)
        for row in eq['terms']:
            powers=row['powers'];supp=[i for i,e in enumerate(powers[:n]) if e]
            for ks in itertools.product(*(range(powers[i]+1) for i in supp)):
                mon=[0]*n+powers[n:];c=row['coefficient']
                for i,k in zip(supp,ks):mon[i]=k;c*=math.comb(powers[i],k)
                shifted[tuple(mon)]+=c
        terms=collections.defaultdict(dict)
        for mon,c in shifted.items():
            if not c:continue
            alpha=mon[:n];require(sum(alpha)<=2,'not quadratic')
            padded=[0]*(2-sum(alpha))+[i+1 for i,e in enumerate(alpha) for _ in range(e)]
            fac=math.factorial(2-sum(alpha))*math.prod(math.factorial(e) for e in alpha)
            terms[tuple(padded)][mon[n:]]=c*fac
        blocks[eq['number']]=dict(terms)
    return blocks

def check_source_representations(source):
    """Check the parent sparse data against its independently parsed residuals."""
    names=source['variables']+source['constants'];n=len(source['variables'])
    require(source['sparse_term_coordinate_order']==names,'source coordinate order')
    require(len(set(names))==len(names),'duplicate source variable or port')
    require(source['constants']==['beta','K0','MC','MF'],'port order mismatch')
    require(source['domain']=='strictly positive integers','wrong original domain')
    rows=source['equations']
    require(len(rows)==22 and {r['number'] for r in rows}==set(range(1,23)),'wrong source rows')
    for row in rows:
        sparse={}
        for term in row['terms']:
            alpha=tuple(term['powers']);co=term['coefficient']
            require(len(alpha)==len(names) and all(type(x)==int and x>=0 for x in alpha),'bad source exponent')
            require(sum(alpha[:n])<=2 and type(co)==int and co!=0,'bad source term')
            require(alpha not in sparse,'duplicate source monomial')
            sparse[alpha]=co
        require(port_polynomial(row['residual'].replace('^','**'),names,source['affine_abbreviations'])==sparse,'residual/sparse coefficient disagreement in row '+str(row['number']))

def check_support_record(blocks,source):
    """Check the supplemental support certificate, never trust it as an input."""
    data=json.loads((ROOT/'source_support.json').read_text())
    require(data['parent_sha256']==EXPECTED_SOURCES['upstream_parent_quartic31.json'][0],'support source hash')
    require(data['variables']==['1']+source['variables'],'support variable order')
    require(len(data['blocks'])==len(blocks),'support block count')
    require({b['equation'] for b in data['blocks']}==set(blocks),'support row labels')
    for row in data['blocks']:
        got={}
        for term in row['terms']:
            pair=tuple(term['pair']);require(pair not in got,'duplicate support pair')
            got[pair]={tuple(c['powers']):c['coefficient'] for c in term['coefficient']}
        require(got==blocks[row['equation']],'support coefficient mismatch')
        require(sorted(map(tuple,row['pairs']))==sorted(got),'support pair list mismatch')
    marked={pair for block in blocks.values() for pair in block}
    require(list(map(tuple,data['marked_pairs']))==sorted(marked),'marked pair list mismatch')

def audit(path=None):
    verify_source_pins()
    path=Path(path) if path else ROOT/'code_v1.json'
    if path.resolve()==(ROOT/'code_v1.json').resolve():
        require(sha(path)==CANONICAL_CODE_SHA256,'canonical code bytes changed')
    code=json.loads(path.read_text());source=json.loads((ROOT/'upstream_parent_quartic31.json').read_text())
    pinned=json.loads((ROOT/'upstream_QUADRATIC_TARGETS.json').read_text())
    check_source_representations(source)
    require(source['variables']==pinned['variables'],'variable order differs from pinned45')
    require(source['constants']==pinned['ports'],'port order differs from pinned45')
    blocks=shifted_source(source)
    check_support_record(blocks,source)
    require(len(pinned['rows'])==len(blocks) and {r['original_row_one_based'] for r in pinned['rows']}==set(blocks),'pinned45 rows missing or repeated')
    # Independently compare every coefficient with the fetched pinned45 record.
    for row in pinned['rows']:
        got={}
        for term in row['terms']:
            a=term['alpha'];pair=tuple([0]*(2-sum(a))+[i+1 for i,e in enumerate(a) for _ in range(e)])
            require(len(a)==len(source['variables']) and all(type(x)==int and x>=0 for x in a) and sum(a)<=2,'bad pinned45 multi-index')
            require(pair not in got,'duplicate pinned45 pair')
            factor=math.factorial(2-sum(a))*math.prod(math.factorial(e) for e in a)
            raw=port_polynomial(term['coefficient'],source['constants'])
            got[pair]=port_polynomial(term['weighted_coefficient'],source['constants'])
            require(term['multinomial_inverse_weight']==factor and got[pair]=={a:c*factor for a,c in raw.items()},'pinned45 factorial weighting mismatch')
        old=blocks[row['original_row_one_based']]
        require(set(got)==set(old),'pinned45 support mismatch')
        expected={pair:dict(coef) for pair,coef in old.items()}
        if row['original_row_one_based']==15:
            # Package45 uses old z=new z+1, subtracting beta*(n_J+1).
            for pair,amount in [((0,1),1),((0,0),2)]:
                mon=(1,0,0,0);expected[pair][mon]=expected[pair].get(mon,0)-amount
                if not expected[pair][mon]:del expected[pair][mon]
        require(got==expected,'pinned45 coefficient/transport mismatch')
    n=len(source['variables']);w=code['weights'];order=code['order'];q=code['targets']
    require(len(w)==n+1 and w[0]==0 and all(type(x)==int and x>0 for x in w[1:]),'invalid weights')
    require(len(set(w))==n+1,'input positions repeat')
    require(sorted(order)==sorted(blocks),'rows missing or duplicate')
    require(len(q)==len(order) and len(set(q))==len(q),'invalid targets')
    require(all(type(x)==int and x>=0 for x in q),'negative target')
    allpairs=list(itertools.combinations_with_replacement(range(n+1),2))
    sum_pairs=collections.defaultdict(list)
    for pair in allpairs:sum_pairs[sum(w[i] for i in pair)].append(pair)
    marked=set(pair for block in blocks.values() for pair in block)
    for pair in marked:require(sum_pairs[sum(w[i] for i in pair)]==[pair],'marked sum collision')
    target_to_row=dict(zip(q,order));D={};checks=matches=0
    extracted={row:collections.defaultdict(lambda:collections.defaultdict(int)) for row in order}
    for row,target in zip(order,q):
        for alpha,coef in blocks[row].items():
            exponent=target-sum(w[i] for i in alpha)
            require(exponent>=0,'negative D exponent')
            require(exponent not in D,'D coefficients overlap')
            D[exponent]=coef
            for beta in allpairs:
                checks+=1;land=exponent+sum(w[i] for i in beta)
                if land in target_to_row:
                    require(target_to_row[land]==row and beta==alpha,'cross-target contamination')
                    matches+=1
                    multiplicity=1 if beta[0]==beta[1] else 2
                    for port_power,c in coef.items():
                        extracted[row][beta][port_power]+=multiplicity*c
    require(matches==len(D),'missing target contribution')
    require(len(D)==136 and checks==71808,'wrong certificate cardinalities')
    for row,block in blocks.items():
        expected={}
        for pair,coefficients in block.items():
            # Padded repeated pairs have factorial factor 2; all others 1.
            fac=2 if pair[0]==pair[1] else 1
            require(all(c%fac==0 for c in coefficients.values()),'nonintegral residual coefficient')
            expected[pair]={a:2*c//fac for a,c in coefficients.items()}
        require(dict(extracted[row])==expected,'formal extraction is not twice residual')
    require(max(q)==max(D),'wrong D degree')
    require(D[max(D)]=={(0,)*len(source['constants']):2},'leading coefficient is not2')
    M=max(w);Q=max(q);H=Q+2*M
    require(code['max_weight']==M and code['maximum_target']==Q and code['convolution_height']==H,'stale code summary')
    # This is genuinely weaker than a full B2 code: absent monomials may collide.
    collision=next((ps for ps in sum_pairs.values() if len(ps)>1),None)
    require(collision is not None and all(p not in marked for p in collision),'not a strictly selective example')
    example={'pairs':[list(p) for p in collision[:2]],'sum':sum(w[i] for i in collision[0])}
    result={'status':'PASS','source_pin':SOURCE_PIN,'source_pins_verified':True,'code_file':path.name,'code_sha256':sha(path),'variables':n,'residuals':len(order),'input_positions':n+1,'all_pairs':len(allpairs),'distinct_pair_sums':len(sum_pairs),'full_B2':False,'allowed_absent_pair_collision':example,'marked_pairs':len(marked),'marked_quadratic_pairs':sum(a!=0 for a,b in marked),'source_terms':len(D),'source_row_term_counts':[len(blocks[i]) for i in sorted(blocks)],'independently_parsed_parent_residuals':22,'finite_interactions_checked':checks,'target_contributions':matches,'formal_target_polynomial_identities':22,'D_coefficients_injective':True,'leading_D_coefficient':2,'max_weight':M,'max_target':Q,'convolution_height':H,'N0_exponent':M+1,'N1_exponent':H+1,'N_exponent':H+M+2,'parent_sha256':sha(ROOT/'upstream_parent_quartic31.json'),'pinned45_sha256':sha(ROOT/'upstream_QUADRATIC_TARGETS.json'),'comparison':'All 136 supports agree with package45 at the stated pin. Coefficients agree after precisely the row15 transport correction: package45 residual = original shifted residual minus beta*(n_J+1). The final selected source is original package31 with every positive variable replaced by n_i+1. This finite result verifies source extraction, not inherited compiler/finalizer theorems.'}
    return result

if __name__=='__main__':
    import sys
    result=audit(sys.argv[1] if len(sys.argv)>1 else None)
    print(json.dumps(result,indent=2))
