#!/usr/bin/env python3
"""Independent bounded mathematical challenge; no author Python imports or API audit."""
import argparse, hashlib, json, random
from pathlib import Path
from fractions import Fraction
from collections import Counter
if not __debug__: raise RuntimeError('run without -O')
PINS = {'group_projective_product_radix_scale.py': 'd33e8aa3bff7559c72768be7116f0328ebad0cf65190115101457a71a0e25965', 'group_projective_product_radix_scale.json': '1403987d49c3613b3ca6cdc1f1794d16199af9020c9c88fd53c49981f95db9a7', 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39', 'group_projective_factored_native_index.md': 'b7461afc50fd7c04939e44d945255421789d4f127b65ce8a9e41a0f545188177', 'group_projective_shifted_X_quotient.md': '4f76dda46f9385a769da0c809292b466d352be2a6f2d39c5e70519bdeda37e00', 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb', 'group_projective_coupled_linear_unit.md': '15fa0737a82996a8ea5c28aa62cbbe798ac5e06e4a3323c4dcaa01c9cd6286c7', 'group_projective_index_unit.md': '2a33b8596b0396667382495272669422bddcf395fa0de20f01af0dbe38bfe9bc', 'group_projective_strong_unit_product.md': '06978175efe47f59bf497f8882b3138692abead1458c58de6a53af92b4f83605', 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b'}

def need(ok,msg):
    if not ok: raise ValueError(msg)
def digest(b): return hashlib.sha256(b).hexdigest()
def same(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if type(a) in (tuple,list): return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b

# Six independent indeterminates q,H,M,Z,w,F. F is used only in the margin identity.
Z=(0,)*6
def const(n):return {Z:n} if n else {}
def var(i):
    m=list(Z);m[i]=1;return {tuple(m):1}
def add(a,b,c=1):
    z=dict(a)
    for m,v in b.items():
        z[m]=z.get(m,0)+c*v
        if not z[m]:del z[m]
    return z
def mul(a,b):
    z={}
    for m,v in a.items():
        for n,w in b.items():
            k=tuple(x+y for x,y in zip(m,n));z[k]=z.get(k,0)+v*w
    return {m:v for m,v in z.items() if v}
def scale(n,a):return mul(const(n),a)
def sub(a,b):return add(a,b,-1)
def symbolic():
    q,H,M,Zz,w,F=map(var,range(6));one=const(1)
    A=add(scale(16,H),const(13));B=add(scale(16,M),const(10));F3=add(scale(16,Zz),const(8))
    qm=sub(q,one);qp=add(q,one);z0=mul(qm,F3);S=add(A,mul(qp,add(B,z0)));r=mul(qm,S)
    f1=sub(sub(A,one),F3);f2=sub(B,F3);f0=sub(sub(sub(sub(q,f1),f2),F3),one)
    direct=add(f0,mul(q,add(f1,mul(q,add(f2,mul(q,F3))))))
    need(r==direct,'folded A+1 field packing')
    need(sub(S,z0)==add(add(A,mul(qp,B)),mul(q,z0)),'positive shift difference')
    wp=sub(add(w,z0),S)
    need(mul(q,add(wp,S))==mul(q,add(w,z0)),'signed quotient graph identity')
    margin=sub(scale(3,mul(mul(q,q),mul(qm,F))),scale(2,mul(mul(mul(q,q),q),add(F,one))))
    need(margin==mul(mul(q,q),sub(mul(sub(q,const(3)),F),scale(2,q))),'E margin identity')
    return {'identities':4,'folded_A_offset':13,'F1_uses_folded_A_minus_one':True}

def run_source(rows,v):
    d=dict(v)
    for n,o,a,b in rows:
        a=d[a] if type(a)is str else a;b=d[b] if type(b)is str else b
        d[n]=a*b if o=='*' else a+b if o=='+' else a-b
    return d

def source_audit(root):
    receipt=json.loads((root/'group_projective_product_radix_scale.json').read_text());rows=receipt['source'];out=receipt['output']
    d={n:(o,a,b) for n,o,a,b in rows};need(len(d)==len(rows)==244,'244 distinct paid gates')
    expected={'shifted_native_quotient':('+','selection__w','packed_top_sum'),
        'selection__wn2':('*','shifted_native_quotient','selection__q'),
        'packed_z_product':('*','packed_q_minus','selection__F3'),
        'packed_q_minus':('-','selection__q',1),'packed_q_plus':('+','selection__q',1),
        'packed_top_sum':('+','selection__padded_A','packed_middle_product'),
        'packed_middle_product':('*','packed_q_plus','packed_middle_sum'),
        'packed_middle_sum':('+','selection__padded_B','packed_z_product'),
        'selection__padded_A':('+','selection__scaled_A',13),
        'selection__padded_B':('+','selection__scaled_B',10),
        'selection__F3':('+','selection__scaled_Z',8),
        'selection__bs_packed':('*','packed_q_minus','packed_top_sum')}
    need(all(d[k]==v for k,v in expected.items()),'actual coefficient and index cone')
    need([n for n,o,a,b in rows if 'selection__w' in (a,b)]==['shifted_native_quotient'],'only old quotient consumer')
    def ancestors(n):
        seen=set();todo=[n]
        while todo:
            x=todo.pop()
            if type(x)is str and x not in seen:
                seen.add(x)
                if x in d:todo.extend(d[x][1:])
        return seen
    need('selection__w' not in ancestors('packed_top_sum')|ancestors('packed_z_product'),'offset independence')
    child=[[n,o,a,'packed_z_product'] if n=='shifted_native_quotient' else [n,o,a,b] for n,o,a,b in rows]
    nodes=set(d);free=sorted({x for n,o,a,b in rows for x in (a,b) if type(x)is str and x not in nodes})
    need(len(free)==37 and 'x' in free,'actual positive ports')
    cd={n:(a,b) for n,o,a,b in child};live=set();todo=[out]
    while todo:
        n=todo.pop()
        if type(n)is str and n in cd and n not in live:live.add(n);todo.extend(cd[n])
    need(live==nodes,'all changed-source gates stay live')
    # After the proved quotient/X cut, every other instruction is literally unchanged.
    need([(n,o,a,b) for n,o,a,b in child if n!='shifted_native_quotient']==[(n,o,a,b) for n,o,a,b in rows if n!='shifted_native_quotient'],'whole downstream conservation')
    rng=random.Random(6142);common=0
    for i in range(32):
        v={n:rng.randrange(-2,4) for n in free}
        if i>=24:v={n:Fraction(x,2) for n,x in v.items()}
        env=run_source(child,v);oldv=dict(v);oldv['selection__w']+=env['packed_z_product']-env['packed_top_sum'];prior=run_source(rows,oldv)
        need(all(prior[n]==env[n] for n in nodes),'all computed registers under pullback');common+=len(nodes)
    c=Counter('M' if o=='*' else 'A' for n,o,a,b in child)
    return {'paid_gates':244,'M':c['M'],'A':c['A'],'positive_witnesses':36,'literal_changed_operands':1,'numeric_whole_pullbacks':32,'rational_pullbacks':8,'matching_computed_registers':common,'all_gates_live':True}

def boundaries():
    padded=0;signs=0
    for q in range(16,145,16):
        total=q//16-1
        for aa in range(total+1):
            for bb in range(total-aa+1):
                for cc in range(total-aa-bb+1):
                    dd=total-aa-bb-cc;fs=[1+16*aa,4+16*bb,2+16*cc,8+16*dd]
                    need(sum(fs)==q-1 and min(fs)>0 and max(fs)<q,'positive untyped fields')
                    H=(fs[1]+fs[3]-12)//16;M=(fs[2]+fs[3]-10)//16;Zz=(fs[3]-8)//16
                    S=16*H+13+(q+1)*(16*M+10+(q-1)*fs[3]);r=sum(fs[j]*q**j for j in range(4))
                    X=q*(1+(q-1)*fs[3]);Y=3*q;E=X*Y;a=Y*(X+1);A=a+2;P=2*X*Y*Y+1
                    need(r==(q-1)*S and r<q**3*(fs[3]+1),'packing and untyped upper bound')
                    need(q*q*((q-3)*fs[3]-2*q)>=18432 and E>2*r+3,'pretyping E bound')
                    need(P>A and 2*A*A-1>P and 2*A>Y+1 and 6*X*Y*Y>a,'rank/ratio premises')
                    for e in (-1,1):
                        for lam in (-1,1):
                            K=r+e;J=2*K-lam
                            need(0<K<E and 0<J<E and J<=2*r+3,'both index/linear signs')
                            need(Y*(r-1)>2*J,'signed index c/2 bound');signs+=1
                    padded+=1
    # Small margins checked exactly; the note proves the same inequalities for all r'>=1.
    for rp in range(1,257):
        need(12*rp<16**(rp+1),'small error before exponent')
        need(2*4**rp<16**(rp+1),'binary representative interval')
    pops=0
    for r in range(17,65538,16):
        n=r-1;j=(n&-n).bit_length()-1
        need((r-2).bit_count()==r.bit_count()+j-2 and j>=4,'negative index population change');pops+=1
    mods=0
    for A in range(4):
        for T in range(4):
            for f in range(4):
                need((1+T*T-(A*A-1)*(f*f-1))%4!=3,'strong unit sign');mods+=1
    return {'padded_field_boundaries':padded,'both_index_and_linear_sign_bounds':signs,'pre_exponent_small_error_boundaries':256,'negative_index_population_identities':pops,'strong_unit_mod4_cases':mods}

def verify(root):
    pins={}
    for name,h in PINS.items():
        b=(root/name).read_bytes();need(digest(b)==h,'source pin '+name);pins[name]=h
    return {'status':'PASS','scope':'Independent mathematical bootstrap and one saved literal source; no proposed maintained API or degree audit, no universal numerical table.', 'pins':pins,'symbolic':symbolic(),'source':source_audit(root),'finite_boundaries':boundaries(),'theorem':'Positive zero bijection after smaller tail offset; inverse positivity proved only after recovering the native exponent and excluding the negative index.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--write',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.root)
    text=json.dumps(r,sort_keys=True,indent=2)+'\n';need(same(r,json.loads(text)),'exact JSON roundtrip')
    if a.write:a.write.write_text(text)
    else:need(same(r,json.loads(a.expect.read_text())),'exact receipt replay')
    print(json.dumps({k:r[k] for k in ('status','symbolic','source','finite_boundaries')},sort_keys=True))
if __name__=='__main__':main()
