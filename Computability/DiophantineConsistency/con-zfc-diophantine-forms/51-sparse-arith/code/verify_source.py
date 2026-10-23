#!/usr/bin/env python3
"""Exact independent certificate for raw-positive sparse-target extraction.

Reads JSON data only; does not import the builder or its algebra helpers.
All checks remain active under python -O.
"""
from pathlib import Path
from collections import defaultdict
from itertools import combinations_with_replacement, product
import gzip, hashlib, json, math

ROOT=Path(__file__).resolve().parents[1]
def require(test,message):
    if not test:raise ValueError(message)

def certify(weights,targets,rows,recipes,ports,n):
    require(len(weights)==n+1 and weights[0]==0,"Padding weight")
    require(len(set(weights))==n+1 and min(weights[1:])>0,"Distinct positive weights")
    require(len(targets)==len(rows) and len(set(targets))==len(targets),"Distinct target positions")
    pairs=[];sums={}
    for i,j in combinations_with_replacement(range(n+1),2):
        alpha=[0]*n
        if i:alpha[i-1]+=1
        if j:alpha[j-1]+=1
        e=weights[i]+weights[j]
        require(e not in sums,"Pair-sum collision")
        sums[e]=(tuple(alpha),1 if i==j else 2)
        pairs.append((e,tuple(alpha),1 if i==j else 2))
    dp={};expected=[];supports=[]
    for j,row in enumerate(rows):
        output={};support=set()
        for term in row:
            alpha=tuple(term['alpha']);degree=sum(alpha)
            require(len(alpha)==n and all(a>=0 for a in alpha) and degree<=2,"Quadratic monomial")
            e=sum(a*w for a,w in zip(alpha,weights[1:]));support.add(e)
            exponent=targets[j]-e
            require(exponent>=0,"Negative reversal exponent")
            require(exponent not in dp,"Reversal coefficients overlap")
            leaf=term['leaf']
            poly=[{'powers':[0]*len(ports),'coefficient':leaf}] if isinstance(leaf,int) else recipes[leaf]
            poly={tuple(t['powers']):term['sign']*t['coefficient'] for t in poly}
            dp[exponent]=poly
            factor=math.factorial(2-degree)*math.prod(math.factorial(a) for a in alpha)
            for p,c in poly.items():
                require(c%factor==0,"Factorial weighting")
                output[(alpha,p)]=2*(c//factor)
        expected.append(output);supports.append(support)
    # This universal condition includes every pair monomial in the dense square,
    # not just monomials that occur in the input equations.
    offdiagonal=0
    for j,support in enumerate(supports):
        for k,target in enumerate(targets):
            if j==k:continue
            for e in support:
                require(e+target-targets[j] not in sums,"Cross-row target interference")
                offdiagonal+=1
    extracted=[defaultdict(int) for _ in targets]
    ti={t:j for j,t in enumerate(targets)}
    for e,poly in dp.items():
        for s,alpha,mult in pairs:
            if e+s in ti:
                row=extracted[ti[e+s]]
                for p,c in poly.items():row[(alpha,p)]+=c*mult
    extracted=[{k:c for k,c in row.items() if c} for row in extracted]
    expected=[{k:c for k,c in row.items() if c} for row in expected]
    require(extracted==expected,"Exact symbolic extraction identity")
    return dp,expected,{'pairs':len(pairs),'weighted_records':len(dp),
        'offdiagonal_support_checks':offdiagonal,'dense_convolution_pairs':len(dp)*len(pairs)}

def main():
    data=json.loads((ROOT/'data/coefficient_recipes.json').read_text())
    pack=json.loads((ROOT/'data/targets.json').read_text())
    parent=json.loads((ROOT/'upstream/parent_sparse.json').read_text())
    n=len(data['variables']);m=len(data['rows'])
    targets=[None]*m
    for row,t in zip(pack['order'],pack['targets']):targets[row]=t
    dp,expected,receipt=certify(pack['weights'],targets,data['rows'],data['recipes'],data['ports'],n)
    # Independently replay the parent arithmetic DAG over sparse Z-polynomials.
    pcircuit=json.loads((ROOT/'upstream/parent_system.json').read_text())
    cnames=pcircuit['variables']+pcircuit['constants'];zero=(0,)*len(cnames)
    env={}
    for i,name in enumerate(cnames):
        mon=list(zero);mon[i]=1;env[name]={tuple(mon):1}
    def get(value):return ({zero:value} if value else {}) if isinstance(value,int) else env[value]
    def plus(a,b,sign=1):
        out=dict(a)
        for mon,co in b.items():out[mon]=out.get(mon,0)+sign*co
        return {mon:co for mon,co in out.items() if co}
    def times(a,b):
        out={}
        for ma,ca in a.items():
            for mb,cb in b.items():
                mon=tuple(x+y for x,y in zip(ma,mb));out[mon]=out.get(mon,0)+ca*cb
        return {mon:co for mon,co in out.items() if co}
    for name,op,a,b in pcircuit['source']:
        require(name not in env,'Duplicate parent gate')
        env[name]=times(get(a),get(b)) if op=='*' else plus(get(a),get(b),-1 if op=='-' else 1)
    require(cnames==parent['sparse_term_coordinate_order'],'Parent coordinate order')
    for (a,b),row in zip(pcircuit['comparisons'],parent['equations']):
        exact=plus(get(a),get(b),-1)
        stored={tuple(t['powers']):t['coefficient'] for t in row['terms']}
        require(exact==stored,'Exact parent circuit/sparse identity')
    # Bind the exact returned quadratic rows to the independently supplied raw
    # parent coefficients, with row8 negated and relocated last.
    raw=[]
    for j in data['row_order_one_based']:
        sign=-1 if j==8 else 1
        row=parent['equations'][j-1]
        r={}
        for term in row['terms']:
            mon=term['powers'];key=(tuple(mon[:n]),tuple(mon[n:]))
            r[key]=r.get(key,0)+2*sign*term['coefficient']
        raw.append({k:c for k,c in r.items() if c})
    require(raw==expected,"Raw parent binding")
    require(max(dp)==max(targets),"Top reversal exponent")
    require(dp[max(dp)]=={(0,)*4:2},"Positive leading coefficient")
    require(max(dp)+2*max(pack['weights'])==pack['span'],"Product support span")
    # Bound every ordinary raw coefficient after grouping port monomials.
    l1=0;portdegree=0
    for row in expected:
        grouped=defaultdict(list)
        for (alpha,p),c in row.items():grouped[alpha].append((p,c//2))
        for terms in grouped.values():
            l1=max(l1,sum(abs(c) for p,c in terms))
            portdegree=max(portdegree,max(sum(p) for p,c in terms))
    require(l1<=8 and portdegree<=2,"Uniform H bound")
    pvals={name:int.from_bytes(gzip.decompress((ROOT/'coefficients/payloads'/f'{file}.bin.gz').read_bytes()),'little')
        for name,file in zip(('beta','K0','MC','MF'),('beta','K','MC','MF_source'))}
    H=8*(1+sum(pvals.values()))**2
    beta_source=1<<data['beta_source_exponent']
    require(beta_source>4*33**2*H,"Decoded digit bound")
    require(beta_source>36*H+2,"Broad-range source bound")
    require(data['beta_source_exponent']%2==0,"Square and residue class source base")
    # All parent coordinates equal1 cannot solve row5: E-X(a-E)=1.
    row5=parent['equations'][4]
    terms={tuple(t['powers'][n:]):0 for t in row5['terms']}
    for t in row5['terms']:terms[tuple(t['powers'][n:])]+=t['coefficient']
    terms={k:v for k,v in terms.items() if v}
    require(terms=={(0,)*4:1},"Nonzero positive all-ones parent")
    rejected=0
    badtargets=targets[:];badtargets[1]=badtargets[0]
    badweights=pack['weights'][:];badweights[2]=badweights[1]
    for weights,tt in [(pack['weights'],badtargets),(badweights,targets)]:
        try:certify(weights,tt,data['rows'],data['recipes'],data['ports'],n)
        except ValueError:rejected+=1
        else:raise ValueError('Invalid control accepted')
    # Actual10large coefficients are re-evaluated as integers and byte-compared.
    manifest=json.loads((ROOT/'data/fixed_values.json').read_text())
    expectedfixed={'beta_source':beta_source}
    for name,recipe in data['recipes'].items():
        expectedfixed[name]=sum(term['coefficient']*math.prod(pvals[p]**e for p,e in zip(data['ports'],term['powers'])) for term in recipe)
    for name,val in expectedfixed.items():
        r=manifest[name];payload=gzip.decompress((ROOT/r['file']).read_bytes())
        require(int.from_bytes(payload,'little')*r['sign']==val,'Fixed integer payload')
        require(hashlib.sha256(payload).hexdigest()==r['sha256'],'Fixed payload digest')
    receipt.update({'status':'PASS','maximum_target':max(targets),'span':pack['span'],
        'raw_parent_rows':m,'variables_in_parent':n,'fixed_integer_leaves':len(manifest),
        'maximum_raw_coefficient_L1':l1,'maximum_port_degree':portdegree,
        'H_bit_length':H.bit_length(),'native_port_bit_lengths':{k:v.bit_length() for k,v in pvals.items()},
        'invalid_controls_rejected':rejected,
        'scope':'Exact finite source algebra and fixed coefficient binding; no claim of unbounded compiler verification.'})
    (ROOT/'certificates/source.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
