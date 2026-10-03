#!/usr/bin/env python3
"""Independent literal-data checks; never imports or executes upstream code."""
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'data' / 'semigroup.json'
PIN = '506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9'

def require(condition, description):
    if not condition:
        raise RuntimeError(description)

def multiply(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]

def det(a):
    n=len(a)
    total=0
    for p in itertools.permutations(range(n)):
        v=1
        for i in range(n):
            v *= a[i][p[i]]
        total += (-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*v
    return total

def inverse(a):
    require(det(a)==1,'matrix must have determinant one')
    return [[a[1][1],-a[0][1]],[-a[1][0],a[0][0]]]

def e(j):
    return [[1+4*j,2],[-8*j*j,1-4*j]]

def block(a,b):
    return [a[0]+[0,0],a[1]+[0,0],[0,0]+b[0],[0,0]+b[1]]

def main():
    raw=SOURCE.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==PIN,'source pin')
    obj=json.loads(raw)
    gens=obj['generators']; tiles=obj['tiles']; codes=obj['top_codes']
    require(len(gens)==229 and len(tiles)==114,'fixed counts')
    def phi(word):
        out=[[1,0],[0,1]]
        for c in word:
            out=multiply(out,e(codes[c]))
        return out
    t=e(0)
    for j,tile in enumerate(tiles,1):
        require(tile['id']==j,'ordered tile identity')
        a,b=gens[j-1],gens[114+j-1]
        require(a['name']==f'A{j}' and b['name']==f'B{j}','family names/order')
        require(a['tile_id']==j and b['tile_id']==j,'family tile identity')
        require(a['matrix']==block(phi(tile['h']),e(j)),'A literal formula')
        lower=multiply(multiply(inverse(t),inverse(e(j))),t)
        require(b['matrix']==block(inverse(phi(tile['g'])),lower),'B literal formula')
    require(gens[-1]['name']=='C','final C name')
    require(gens[-1]['matrix']==block(inverse(phi('X#')),t),'C literal formula')
    require(len({tuple(sum(g['matrix'],[])) for g in gens})==229,'distinct generators')
    for g in gens:
        m=g['matrix']
        require(len(m)==4 and all(len(row)==4 for row in m),'4x4 dimensions')
        require(all(type(v) is int for row in m for v in row),'literal integers')
        require(all(m[i][j]==0 for i in range(4) for j in range(4) if (i<2)!=(j<2)),'block diagonal')
        require(det(m)==1,'Leibniz determinant')
    inverse_b=[inverse([row[:2] for row in g['matrix'][:2]]) for g in gens[114:228]]
    upper_a=[[row[:2] for row in g['matrix'][:2]] for g in gens[:114]]
    upper_c=[row[:2] for row in gens[-1]['matrix'][:2]]
    norm=lambda m:max(sum(abs(v) for v in row) for row in m)
    kh,kg,kd=max(map(norm,upper_a)),max(map(norm,inverse_b)),norm(upper_c)
    require((kh,kg,kd)==(64675047,12234453,6883),'exact maximum row-sum norms')
    require(all(v!=0 for m in upper_a+inverse_b for row in m for v in row),'all U and V entries nonzero')
    report={
        'status':'PASS',
        'source_sha256':PIN,
        'upstream_code_executed':False,
        'literal_generators_checked':229,
        'literal_tiles_checked':114,
        'independent_determinant_algorithm':'Leibniz permutation expansion',
        'C_top': [row[:2] for row in gens[-1]['matrix'][:2]],
        'lower_target':t,
        'max_abs_A_top':max(abs(x) for g in gens[:114] for row in g['matrix'][:2] for x in row[:2]),
        'max_abs_inverse_B_top':max(abs(x) for m in inverse_b for row in m for x in row),
        'max_row_sum_norm_A_top':kh,
        'max_row_sum_norm_inverse_B_top':kg,
        'row_sum_norm_C_top':kd,
        'all_912_U_and_V_entries_nonzero':True,
        'max_abs_C_top':max(abs(x) for row in gens[-1]['matrix'][:2] for x in row[:2]),
        'checks':['literal A_i and B_i formulas against tile strings','C against X# inverse','all 229 determinants and distinctness','all blocks and exact integer types']
    }
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
