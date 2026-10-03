#!/usr/bin/env python3
"""Independent geometric reconstruction of the actual exported quartic.
Imports neither builder nor main checker. Uses explicit exceptions under -O.
"""
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
import json
import hashlib
ROOT=Path(__file__).resolve().parent.parent

def need(ok,why):
    if not ok: raise RuntimeError(why)

def canon(terms):
    out={}
    for t in terms:
        m=tuple(t['variables'])
        need(tuple(sorted(m))==m,'noncanonical monomial')
        need(m not in out,'duplicate exported monomial')
        need(type(t['coefficient']) is int and t['coefficient']!=0,'invalid coefficient')
        out[m]=t['coefficient']
    return out

def main():
    certificate=json.loads((ROOT/'local-quartic-certificate.json').read_text())
    coords=[(x,y) for y in range(-3,3) for x in range(-6,7)]
    ids={p:i for i,p in enumerate(coords)}
    patterns=[
        ('E',[(0,0),(1,0)],[(1,0),(2,0)]),
        ('W',[(0,0),(2,0)],[(-1,0),(1,0)]),
        ('R',[(0,0),(1,0),(3,0)],[(-1,0),(1,0),(4,1)]),
        ('L',[(0,0),(2,0),(4,0)],[(0,1),(3,1),(4,1)])]
    need(certificate['input_coordinates']==[list(p) for p in coords],'coordinate order')
    expected_names=[f'c_{x}_{y}' for x,y in coords]+['y']+[f'z_{i}' for i in range(614)]
    need(certificate['variable_order']==expected_names,'variable order')
    gates=[]; residuals=[]; indicators=[]; nextid=79
    top_terms=[]
    for name,old0,new0 in patterns:
        old,new=set(old0),set(new0)
        for sign,targets in [(1,new-old),(-1,old-new)]:
            for tx,ty in sorted(targets):
                a={(x-tx,y-ty) for x,y in old}
                # Since these patterns are horizontal and 2-connected, the halo
                # is exactly this rectangle; do not reuse Minkowski-sum code.
                left=min(x for x,y in a)-2; right=max(x for x,y in a)+2
                row=next(iter(a))[1]
                h={(x,y) for x in range(left,right+1) for y in range(row-2,row+3)}
                occupied=sorted(ids[p] for p in a); empty=sorted(ids[p] for p in h-a)
                item={'name':name,'sign':sign,'anchor':[-tx,-ty],
                      'ones':occupied,'zeros':empty}
                factors=[(i,False) for i in occupied]+[(i,True) for i in empty]
                prev=factors[0][0]
                for external,negated in factors[1:]:
                    gates.append({'target':nextid,'previous':prev,'input':external,'complement':negated})
                    # Algebraically z - u*(1-v) or z-u*v.
                    residual={(nextid,):1,tuple(sorted([prev,external])):1 if negated else -1}
                    if negated: residual[(prev,)]=-1
                    residuals.append(residual)
                    prev=nextid;nextid+=1
                item['result_variable']=prev;indicators.append(item)
                if name=='L':top_terms.append({'coefficient':sign*(-1)**len(empty),'variables':sorted(occupied+empty)})
    for i in range(78):residuals.append({(i,i):1,(i,):-1})
    out={(78,):1,(ids[(0,0)],):-1}
    for item in indicators:out[(item['result_variable'],)]=-item['sign']
    residuals.append(out)
    need(certificate['gates']==gates,'exported gates differ from geometry')
    need(certificate['indicators']==indicators,'exported indicators differ from geometry')
    need(certificate['degree_45_boolean_top_terms']==top_terms,'top terms mismatch')
    need([canon(r) for r in certificate['residuals']]==residuals,'exported residuals differ from geometry')
    # Symbolic SOS independently from the reconstructed residuals. Separate
    # diagonal and unordered cross terms instead of ordered products.
    quartic=Counter(); origins=defaultdict(list); uncollected=0
    for n,r in enumerate(residuals):
        items=list(r.items())
        terms=[]
        for m,c in items:terms.append((tuple(sorted(m+m)),c*c))
        for (m,c),(p,d) in combinations(items,2):terms.append((tuple(sorted(m+p)),2*c*d))
        need(len(set(m for m,c in terms))==len(terms),'within-square monomial collision')
        uncollected+=len(terms)
        for m,c in terms:quartic[m]+=c;origins[m].append((n,c))
    zero_keys=[m for m,c in quartic.items() if c==0]
    quartic={m:c for m,c in quartic.items() if c}
    need(quartic==canon(certificate['expanded_polynomial']),'actual expanded polynomial mismatch')
    counts={'input_bits':78,'external_variables':79,'auxiliary_variables':nextid-79,
            'residuals':len(residuals),'plain_product_gates':sum(not g['complement'] for g in gates),
            'complement_product_gates':sum(g['complement'] for g in gates),
            'residual_monomial_occurrences':sum(len(r) for r in residuals),
            'ordered_sos_expansion_occurrences':sum(len(r)**2 for r in residuals),
            'collected_expanded_terms':len(quartic),'degree':max(map(len,quartic)),
            'maximum_coefficient_magnitude':max(map(abs,quartic.values()))}
    need(counts==certificate['counts'],'resource ledger mismatch')
    repeats={m:o for m,o in origins.items() if len(o)>1}
    need(uncollected==4011,'unexpected independent-square term count')
    need(len(repeats)==608 and all(len(v)==2 for v in repeats.values()),'unexpected collisions')
    need(not zero_keys,'unexpected algebraic cancellation')
    need(all([v[1] for v in vals]==[1,1] for vals in repeats.values()),'unexpected collision signs')
    aux_squares=[m for m in repeats if len(m)==2 and m[0]==m[1] and m[0]>=79]
    input_fourths=[m for m in repeats if len(m)==4 and max(m)<78]
    need(len(aux_squares)==604 and len(input_fourths)==3,'duplicate-type counts')
    need((ids[(0,0)],)*2 in repeats,'missing central square duplicate')
    receipt={'status':'PASS','method':'Reconstructed all indicators, gates, residuals and the exact quartic from independently encoded geometry, without importing builder/checker.',
             'counts':counts,'distinct_terms_before_cross_residual_collection':uncollected,
             'duplicate_monomials':len(repeats),'duplicate_auxiliary_squares':len(aux_squares),
             'duplicate_central_input_square':1,'duplicate_input_product_fourths':len(input_fourths),
             'duplicate_input_product_coordinates':[[list(coords[i]) for i in m] for m in input_fourths],
             'cancelled_monomials':len(zero_keys),'coefficient_histogram':dict(sorted(Counter(quartic.values()).items())),
             'degree_histogram':dict(sorted(Counter(map(len,quartic)).items())),
             'certificate_sha256':hashlib.sha256((ROOT/'local-quartic-certificate.json').read_bytes()).hexdigest()}
    (ROOT/'audit'/'quartic-reconstruction-results.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))
if __name__=='__main__':main()
