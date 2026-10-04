#!/usr/bin/env python3
"""Bounded inert-source audit; the power-block obstruction is proved in the note."""
import argparse
import hashlib
import json
from pathlib import Path

PINS = {
    'group_directed_semigroup193.json': 'c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639',
    'group_directed_semigroup193.md': '75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
    'review_incoming_matrix_grill.md': '14c0c3042558b212db8ee5885338f9a7af983d57a702f0c7af2b3d352a657cb8',
}
I = ((1, 0), (0, 1))
P = ((1, 2), (0, 1))
Q = ((1, 0), (2, 1))

def require(b, msg):
    if not b:
        raise ValueError(msg)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def mm(a,b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)) for i in range(2))

def inv(a):
    require(a[0][0]*a[1][1]-a[0][1]*a[1][0]==1, 'determinant')
    return ((a[1][1],-a[0][1]),(-a[1][0],a[0][0]))

def iw(w):
    return [-a for a in reversed(w)]

def ew(j):
    return [-2]*j+[1]+[2]*j

def ev(w):
    gens={1:P,2:Q,-1:inv(P),-2:inv(Q)}
    a=I
    for c in w:
        a=mm(a,gens[c])
    return a

def block(a,b):
    return [[a[i][j] if i<2 and j<2 else b[i-2][j-2] if i>=2 and j>=2 else 0 for j in range(4)] for i in range(4)]

def run(root):
    data={}
    for name,pin in PINS.items():
        raw=(root/name).read_bytes()
        require(sha(raw)==pin, 'pin: '+name)
        if name.endswith('.json'):
            data=json.loads(raw)
    packet=data['packet']; codes=packet['top_codes']
    def word(s):
        return [a for c in s for a in ew(codes[c])]
    tiles={t['id']:t for t in packet['tiles']}
    records=[]
    for g in packet['generators']:
        name=g['name']
        if name=='C':
            top=iw(word(packet['terminal']+'#')); low=[1]
        else:
            t=tiles[g['tile_id']]; e=ew(t['id'])
            if name.startswith('A'):
                top=word(t['h']); low=e
            else:
                top=iw(word(t['g'])); low=[-1]+iw(e)+[1]
        require(block(ev(top),ev(low))==g['matrix'], 'full matrix: '+name)
        records.append({'name':name,'upper_word':top,'lower_word':low})
    require(len(records)==193,'generator count')
    # E_2=I+N, with N^2=0. The complete target for [1^x A0] is affine.
    E=ev(ew(codes['1']))
    N=tuple(tuple(E[i][j]-I[i][j] for j in range(2)) for i in range(2))
    require(mm(N,N)==((0,0),(0,0)),'nilpotence')
    left=inv(ev(word('A0]#'))); right=inv(ev(word('[')))
    constant=mm(left,right); slope=mm(mm(left,N),right)
    slope=tuple(tuple(-a for a in row) for row in slope)
    # Exact three coefficient checks of det(constant+x*slope)=1.
    a,b,c,d=[v for row in constant for v in row]
    e,f,g,h=[v for row in slope for v in row]
    require((a*d-b*c,a*h+d*e-b*g-c*f,e*h-f*g)==(1,0,0),'affine determinant coefficients')
    rows=[]; outputs=[]; coefficients={}
    for i in range(2):
        for j in range(2):
            n=f't{i}{j}'; ckey=f'constant_{i}{j}'; skey=f'slope_{i}{j}'
            coefficients[ckey]=constant[i][j]; coefficients[skey]=slope[i][j]
            rows += [[n+'_scaled','*','x',skey],[n,'+',n+'_scaled',ckey]]
            outputs.append(n)
    fixtures=[]
    for x in [0,1,2,3,7,16,31,64,128]:
        env=dict(coefficients,x=x)
        for dest,op,l,r in rows:
            env[dest]=env[l]*env[r] if op=='*' else env[l]+env[r]
        got=((env['t00'],env['t01']),(env['t10'],env['t11']))
        expected=inv(ev(word('['+'1'*x+'A0]#')))
        require(got==expected,'literal unary target')
        fixtures.append({'x':x,'upper_target':got})
    out={
        'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,
        'scope':'Actual free-word representation and unary target arithmetic only. No semilinear decision procedure, complete history certificate, or universality of the unary slice is implemented.',
        'free_word_audit':{'generators':len(records),'entry_comparisons':16*len(records),'word_recipe_sha256':sha(json.dumps(records,sort_keys=True,separators=(',',':')).encode()),'faithfulness':'Inherited pinned free-basis theorem; not inferred from the finite comparisons.'},
        'unary_target':{'prefix':'[','repeated_letter':'1','suffix':'A0]','variable':'x','external_domain':'positive integers; x=0 checked additionally','fixed_coefficients':coefficients,'source':rows,'upper_outputs':outputs,'lower_block':P,'ledger':{'M':4,'A':4,'total':8,'witnesses':0,'degree':1},'determinant_polynomial_coefficients':[1,0,0],'fixtures':fixtures},
        'theorem_checks':'The mathematical obstruction uses constructive Parikh semilinearity plus the actual two-free-group interface; finite fixtures do not prove the decision theorem.'
    }
    return json.loads(json.dumps(out))

def same(a,b):
    if type(a) is not type(b):
        return False
    if isinstance(a,dict):
        return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if isinstance(a,list):
        return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--root',type=Path,required=True)
    ag=ap.add_mutually_exclusive_group(required=True); ag.add_argument('--output',type=Path); ag.add_argument('--expect',type=Path)
    args=ap.parse_args(); result=run(args.root.resolve())
    if args.expect:
        require(same(result,json.loads(args.expect.read_text())),'typed receipt mismatch')
    else:
        args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print('PASS: 193 actual free-word matrix recipes; eight paid unary-target gates; exact affine determinant.')

if __name__=='__main__':
    main()
