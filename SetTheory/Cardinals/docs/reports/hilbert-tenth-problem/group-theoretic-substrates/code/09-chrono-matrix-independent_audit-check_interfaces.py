#!/usr/bin/env python3
"""Fresh matrix/interface and bounded semantic checks. No saved trace is read or run."""
import hashlib,itertools,json,math,pathlib,re,sys
from fractions import Fraction
PACKET=pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else pathlib.Path('/workspace/shared/matrix-chronological-certificate-20261004')
OUT=pathlib.Path(__file__).resolve().parent
def need(b,s):
    if not b: raise ValueError(s)
def pairs(p):
    d={}
    for k,v in p:
        need(k not in d,'duplicate key'); d[k]=v
    return d
def load(p): return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
    b=p.read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
manifest=load(PACKET/'evidence/frozen-manifest.json')
for f in manifest['files']:
    p=PACKET/f['path']; need(p.stat().st_size==f['bytes'] and sha(p)==f['sha256'],'frozen file '+f['path'])
prov=load(PACKET/'sources/provenance.json')
for f in prov['files']: need(blob(PACKET/'sources'/f['name'])==f['git_blob_sha'],'provenance blob '+f['name'])
context=load(PACKET/'sources/matrix193_context_absorption.json')
counted=load(PACKET/'sources/matrix195_counted_suffix.json')
countdown=load(PACKET/'sources/matrix193_countdown_rows.json')
coeff=load(PACKET/'evidence/coefficients.json')
for parent in [countdown,counted]:
    for name,pin in parent['pins'].items():
        p=PACKET/'sources'/name
        if p.is_file(): need(sha(p)==pin,'inherited pin '+name)
# Only constant coefficient arrays and metadata are used; accepting_witness/es,
# accepting_traces and packet.instructions are deliberately never consulted.
a=context['packet']; lift=counted['packet']; tr=countdown['transitions']
def mat(flat): return [flat[:2],flat[2:]]
def flat(m): return [v for r in m for v in r]
def mul(a,b):
    need(len(a[0])==len(b),'matrix product dimensions')
    return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def eye(n): return [[int(i==j) for j in range(n)] for i in range(n)]
def inv2(a):
    need(a[0][0]*a[1][1]-a[0][1]*a[1][0]==1,'SL2 inverse')
    return [[a[1][1],-a[0][1]],[-a[1][0],a[0][0]]]
def diag(*matrices):
    n=sum(len(m) for m in matrices); out=[[0]*n for _ in range(n)]; at=0
    for m in matrices:
        need(all(len(row)==len(m) for row in m),'square block')
        for i in range(len(m)):
            for j in range(len(m)): out[at+i][at+j]=m[i][j]
        at+=len(m)
    return out
def block(m,lo,n): return [row[lo:lo+n] for row in m[lo:lo+n]]
def rank(m):
    q=[[Fraction(v) for v in row] for row in m]; r=0
    for c in range(len(q[0])):
        p=next((i for i in range(r,len(q)) if q[i][c]),None)
        if p is None: continue
        q[r],q[p]=q[p],q[r]; v=q[r][c]; q[r]=[x/v for x in q[r]]
        for i in range(len(q)):
            if i!=r:
                v=q[i][c]; q[i]=[x-v*y for x,y in zip(q[i],q[r])]
        r+=1
    return r
letters={k:mat(v) for k,v in a['letters'].items()}
def psi(word):
    r=eye(2)
    for c in word:r=mul(r,letters[c])
    return r
need(a['U']=='[110' and a['V']=='A0]','fixed context')
L=inv2(psi(a['V']+a['separator']));R=inv2(psi(a['U']))
need(flat(L)==a['L'] and flat(R)==a['R'],'context L,R from actual letters')
C0=inv2(psi(a['terminal']+a['separator']))
C=mul(mul(inv2(L),C0),inv2(R)); P=[[1,2],[0,1]]
B=psi('01010111'*2)
need(B==mat(context['block']['B'])==lift['B']==[[-52109,29036],[-94920,52891]],'ordinary block B')
need(inv2(B)==mat(tr['loader']['Y_matrix']),'loader is B inverse')
need(C[0]==countdown['initial_state']['X']==[35426321,-19628667],'initial row e1 C')
old={g['name']:g for g in a['generators']};new={g['name']:g for g in lift['generators']}
need(len(old)==193==len(a['generators']) and len(new)==195==len(lift['generators']),'generator counts/names')
need(old['C']['matrix']==diag(C,P),'central matrix')
tiles={t['id']:t for t in a['tiles']}; rowtiles={t['tile_id']:t for t in tr['tiles']}
need(set(tiles)==set(rowtiles) and len(tiles)==96,'same actual retained tiles')
for i,t in tiles.items():
    A=old['A'+str(i)]['matrix'];BB=old['B'+str(i)]['matrix']
    H=mul(mul(inv2(L),psi(t['h'])),L)
    Ginv=mul(mul(R,inv2(psi(t['g']))),inv2(R))
    E=[[4*i+1,2],[-8*i*i,1-4*i]]
    need(A==diag(H,E),'full A context transfer')
    need(BB==diag(Ginv,mul(mul(inv2(P),inv2(E)),P)),'full B context/lower transfer')
    need(flat(H)==rowtiles[i]['H'],'actual H row tile')
    need(flat(mul(mul(inv2(C),H),C))==rowtiles[i]['K'],'actual K=C^-1 H C')
    need(flat(inv2(Ginv))==rowtiles[i]['G'],'actual G inverse convention')
    need(old['A'+str(i)]['tile_id']==old['B'+str(i)]['tile_id']==i,'generator tile IDs')
O=[[1,0,0],[0,0,0],[0,0,0]];F=[[0,1,0],[0,0,0],[0,0,0]];DD=[[0,0,0],[0,1,1],[0,0,1]]
for name,g in old.items():
    need(new[name]['matrix']==diag(g['matrix'],O),'195 old lift '+name)
    need(rank(new[name]['matrix'])==5,'lift rank')
need(new['END']['matrix']==diag(eye(4),F),'END')
need(new['COUNT']['matrix']==diag(B,eye(2),DD),'COUNT')
need(rank(new['END']['matrix'])==5 and rank(new['COUNT']['matrix'])==6,'extra ranks')
T=diag(eye(2),P,F);T[4][6]='x'
need(lift['target_template']==T and lift['input_port']=='x' and lift['target_source']==[] and lift['target_operations']==0,'literal target input')
need(lift['contexts']=={'U':a['U'],'V':a['V']},'same contexts')

# Finite corroboration of the complete control proof, including the empty word.
control={'O':O,'F':F,'D':DD};control_cases=0
for length in range(10):
    for word in itertools.product('OFD',repeat=length):
        product=eye(3)
        for c in word: product=mul(product,control[c])
        shaped=re.fullmatch('O*FD*',''.join(word)) is not None
        need((product[0][1]==1)==shaped,'control language')
        if shaped:
            expected=[row[:] for row in F];expected[0][2]=word.count('D');need(product==expected,'literal count')
        control_cases+=1

# Exhaustive signed-counter language check, generated afresh rather than saved paths.
counter_cases=0
for length in range(10):
    for word in itertools.product('LT',repeat=length):
        for x in range(-2,12):
            n=x; valid=True
            for c in word:
                if c=='L': n-=1
                elif n!=0: valid=False;break
            accepted=valid and n==0
            predicted=x>=0 and ''.join(word)=='L'*x+'T'*(length-x) and x<=length
            need(accepted==predicted,'signed counter accepted language')
            counter_cases+=1

# Arbitrary bounded pre/post candidates test all chronology boundaries.
chronology_cases=0;chronology_pass=0
for h in [1,2]:
    D=4;b=8;W=b**h
    for a0 in range(D):
        for digits in itertools.product(range(D),repeat=2*h+1):
            u=digits[:h];v=digits[h:2*h];f=digits[-1]
            U=sum(q*b**j for j,q in enumerate(u));V=sum(q*b**j for j,q in enumerate(v))
            packed=b*V+a0==U+W*f
            direct=u[0]==a0 and all(u[j+1]==v[j] for j in range(h-1)) and v[-1]==f
            need(packed==direct,'chronology iff')
            chronology_pass+=packed;chronology_cases+=1

# Exact Sub outer extraction including zero mask, zero value and out-of-range values.
sub_cases=0
for M in range(32):
    radix=2**(M+1);Z=(radix+1)**M
    for V in range(40):
        Y=radix**V;q,d=divmod(Z//Y,radix);r=Z%Y
        binomial=math.comb(M,V) if V<=M else 0
        need(d==binomial,'binomial digit')
        need((d%2==1)==((M & V)==V),'Sub exact parity')
        if d%2:
            half=(d-1)//2;dg=radix-d;rg=Y-r
            need(dg>0 and rg>0 and Z==(q*radix+2*half+1)*Y+r,'positive Sub adapters')
        sub_cases+=1

# Test rigorous fixed-row carry bounds at every corner for actual 97 maps.
carry_cases=0
for H in [1,2,2**27]:
    D=2*H;b=coeff['radix_factor']*D
    for i,A in enumerate(coeff['maps']):
        for r,row in enumerate(A):
            c=1-sum(row)
            for q in itertools.product([0,D-1],repeat=4):
                for v in [0,D-1]:
                    left=v+sum(-a*z for a,z in zip(row,q) if a<0)+H*max(-c,0)
                    right=sum(a*z for a,z in zip(row,q) if a>0)+H*max(c,0)
                    need(0<=left<b and 0<=right<b,'actual affine no-carry bound')
                    need(left-right==v-sum(a*z for a,z in zip(row,q))-c*H,'sign split')
                    carry_cases+=1

# Onehot/slices at many branch positions; fresh values, no source schedule execution.
slice_cases=0
for h in range(1,8):
    for offset in [0,1,47,96]:
        D=16;b=256;R=sum(b**t for t in range(h))
        choices=[(offset+31*t)%97 for t in range(h)]
        E=[sum(int(i==choices[t])*b**t for t in range(h)) for i in range(97)]
        need(sum(E)==R and all((e & R)==e for e in E),'onehot partition')
        for s in range(4):
            values=[(13*t+7*s+offset)%D for t in range(h)]
            Q=[sum(values[t]*int(i==choices[t])*b**t for t in range(h)) for i in range(97)]
            U=sum(values[t]*b**t for t in range(h))
            need(sum(Q)==U and all((q & ((D-1)*e))==q for q,e in zip(Q,E)),'slice partition')
            slice_cases+=1

result={'status':'PASS','frozen_author_files_verified':len(manifest['files']),
'provenance_blob_pins_verified':len(prov['files']),'full_context_generators_reconstructed':193,
'row_tile_pairs_reconstructed':96,'full_lifted_generators_reconstructed':195,'full_lifted_entries_checked':195*49,
'input_and_target_are_literal_x':True,'fixed_contexts':{'U':a['U'],'V':a['V']},
'control_words':control_cases,'signed_counter_candidates':counter_cases,
'arbitrary_chronology_candidates':chronology_cases,'chronology_passes':chronology_pass,
'binomial_subset_cases':sub_cases,'actual_matrix_carry_corner_cases':carry_cases,'slice_partition_cases':slice_cases,
'saved_schedules_used':False,'submitted_or_upstream_code_executed':False}
(OUT/'interface-audit-receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2))
