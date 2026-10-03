#!/usr/bin/env python3
"""Independent pinned-data review: native alias, not a full polynomial zero."""
import argparse
import hashlib
import json
import math
from pathlib import Path

AUTHOR={
 'free_coefficient83_native_alias.py':'628995e89f2ec8d4dfdd59a92229e21caf95520e56828c9eae6effae6d21fab6',
 'free_coefficient83_native_alias.json':'9bf5e1c6452c5c5700821adaf63d59df1c61d2968704a23e63aae3cac067e846',
 'free_coefficient83_native_alias.md':'542775d7ff0ccd84f5fe94c32d6c396ad45a8cc033dd1cbd37ed72dedd40f96f',
}
DEPENDENCIES={
 'complete83_free_coefficient_scout.py':'a72a406021b96df8111c7f11d36e42241894f0834a660c9ed7c6a75cbfbe1485',
 'complete83_free_coefficient_scout.json':'682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016',
 'complete83_free_coefficient_scout.md':'867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31',
 'first_index_scaled_obstruction.md':'b67d208d4c18e45145cf91f272d72e2852c09d79be631da8f0a0ce5f377ba1fd',
 'first_index_scaled_obstruction.json':'52b04d7d47065b822d174f6d480fc31d40d908cc014d4fe517600f2b14ac1cea',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 '../../1980/HALF_PARAMETER_PELL_92_PROOF.md':'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
}
def require(ok,msg):
    if not ok:raise ValueError(msg)
def sha(x):return hashlib.sha256(x).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def exact(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

# Sequential chi/psi recurrences, independent of author binary pair powering.
def pell(A,n,mod=None):
    if n==0:return (1,0)
    x0,x1=1,A;y0,y1=0,1
    if mod:x1%=mod
    for _ in range(1,n):
        x0,x1=x1,2*A*x1-x0;y0,y1=y1,2*A*y1-y0
        if mod:x1%=mod;y1%=mod
    return x1,y1

def case(t):
    p=t*(t+2);n=t*(t+1);R=2*n-1
    X=pow(2,p,p);Y=pow(2,t+1,p);A=(Y*(X+1)+2)%p
    _,cmod=pell(A,p,p);g=math.gcd(cmod,p)
    require(R-p==t*t-1 and 2*R+3==(2*t+1)**2,'exact parameter identities')
    require(math.gcd(p,R-p)==math.gcd(t+2,3),'gcd simplification')
    require(((R-p)%g==0)==(math.gcd(t+2,3)%g==0),'equivalent CRT condition')
    return dict(t=t,p=p,n=n,R=R,c_mod_p=cmod,gcd_c_p=g,auxiliary_CRT_compatible=(R-p)%g==0,
                q16_positive_packing_interval=31*255<R<16**4-16**3)

def actual_interfaces(packet):
    rows={n:[op,a,b] for n,op,a,b in packet['source']}
    expected={
      'wn2':['*','w','q'],'sn2':['*','s','n2'],'n2':['*','Lbig','q'],'Lbig':['*','q','q'],
      'UM':['*','wn2','sn2'],'R10b':['+','eta','zeta'],'ksn2':['*','R10b','sn2'],
      'first_root_base':['*','UM','ksn2'],'first_next':['+','first_root_base','R10b'],
      'first_product':['*','first_root_base','first_next'],'norm_first':['-','tau_square','first_product'],
      'tau_square':['*','tau_root','tau_root'],'R10a':['+','ksn2','eta'],'R12':['+','UM','sn2'],
      'cam2':['*','R10a','R12'],'D1':['+','wn2','cam2'],'gamma_sum':['+','rho','sigma'],
      'a4':['*',4,'R12'],'a4m5':['+','a4',3],'gam':['*','gamma_sum','a4m5'],
      'R14':['+','D1','gam'],'L15':['*','R14','R14'],'a_square':['*','R12','R12'],
      'A':['+','a_square','a4m5'],'c2':['*','R10a','R10a'],'Ac2':['*','A','c2'],
      'norm_main':['-','L15','Ac2'],'hpm1':['*','h','UM'],
      'index_difference':['-','R10b','hpm1'],'norm_index':['-','index_difference','r_lhs'],
      'L16':['*','f','f'],'R16':['*','aux_coefficient_root','aux_coefficient_root'],
      'scaled_f_square':['*','A','L16'],'norm_strong':['-','scaled_f_square','R16'],
      'auxiliary_Tf':['*','auxiliary_quotient','f'],'auxiliary_Tf_minus_one':['-','auxiliary_Tf',1],
      'auxiliary_c_Tf':['*','R10a','auxiliary_Tf_minus_one'],'auxiliary_R_f2':['*','r_lhs','L16'],
      'aux_u_rhs':['-','auxiliary_c_Tf','auxiliary_R_f2'],'H2':['*','aux_u_rhs','aux_u_rhs'],
      'aux_y2':['*','y_aux','y_aux'],'aux_square_gap':['-','H2','aux_y2'],
      'L17':['*','R16','aux_square_gap'],'norm_aux':['+','L17','aux_y2'],
      'repunit':['*','Bm1','Jrep'],'q':['+','repunit',1],
      'q_minus_F':['-','q','F'],'q_minus_FZ':['-','q_minus_F','Z'],
      'gap_product':['*','repunit','q_minus_F'],'gap':['+','gap_product','q_minus_FZ'],
      'Lm1':['-','Lbig',1],'rproduct':['*','gap','Lm1'],
      'qMF':['*','q','MF'],'mask_factor':['+','MC','qMF'],'mask':['*','mask_factor','Jrep'],
      'r_lhs':['+','rproduct','mask']}
    require(all(rows.get(n)==v for n,v in expected.items()),'actual native and packing cones')
    require('r_lhs' not in packet['free'],'target is computed, not supplied')
    return len(expected)

def exact_native(advertised):
    t=11;p=t*(t+2);n=t*(t+1);R=2*n-1
    X=2**p;Y=2**(t+1);E=X*Y;a=Y*(X+1);A=a+2;Delta=A*A-1;H=4*a+3;P=2*X*Y*Y+1
    D,c=pell(A,p);tau,khalf=pell(P,n);k=2*khalf
    eta=c-k*Y;zeta=k*(Y+1)-c
    require(eta>0 and zeta>0 and eta+zeta==k,'strict source ratio')
    gamma,remainder=divmod(D-a*c-X,H);require(remainder==0 and gamma>1,'positive main projection')
    h,remainder=divmod(k-2*n,E);require(remainder==0 and h>0,'positive integral first index')
    require(tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1,'exact first norm')
    require(D*D-Delta*c*c==1 and k-h*E-R==1,'main and retained index factors')
    require(c>A*Delta*Delta and c>2*p and p!=R,'large-rank mismatch')
    require(pell(P,n,E)[1]==n%E,'untyped first-index congruence')
    require(X%16==0 and Y%(16**3)==0,'literal asymmetric scale')
    # Exhaust the short set of CRT classes, independently of modular inversion.
    indices=[R+c*j for j in range(4*p) if (R+c*j)%(4*p)==p]
    require(indices,'CRT compatibility');v=min(indices)
    require(v%c==R%c and v%4==3,'both auxiliary index conditions')
    f=D;S=Delta*c
    require(Delta*f*f-S*S==Delta,'scaled strong factor')
    require(pell(A,2*p,f)==(f-1,0) and pell(A,4*p,f)==(1,0),'modular Pell period')
    require(pell(A,v%(4*p),f)[1]==c%f,'reduced positive auxiliary index residue')
    require(S%c==0 and f*f%c==1 and math.gcd(c,f)==1,'two quotient denominator conditions')
    fields=dict(X=X,Y=Y,w=X//16,s=Y//16**3,E=E,a=a,A=A,Delta=Delta,H=H,P=P,
                D=D,c=c,tau_root=tau,k=k,eta=eta,zeta=zeta,rho=1,sigma=gamma-1,h=h,
                f=f,S=S,abstract_R=R,auxiliary_index=v)
    encoded={n:hex(x) for n,x in fields.items()};bits={n:x.bit_length() for n,x in fields.items()}
    require(exact(encoded,advertised['fields_hex']) and exact(bits,advertised['bit_lengths']),'every exact native field and bit length')
    require(advertised['full_compiler_zero'] is False,'explicit component scope')
    return dict(t=t,p=p,n=n,R=R,fields=len(fields),fields_sha256=sha(stable(encoded)),bit_lengths=bits,
                literal_factors=dict(first=1,main=1,index=1,scaled_strong='Delta'),
                auxiliary='Existence via CRT and Pell identities; V,y,T are not materialized',full_polynomial_zero=False)

def masks_and_packing(advertised):
    # Construct candidates by their prescribed low bits, then filter population.
    masks=[]
    for u in range(4):
        MC=2+4*u
        for v in range(2):
            MF0=4+8*v
            if 0<MC<15 and 0<MF0<15 and bin(MC).count('1')+bin(MF0).count('1')==4:masks.append([MC,MF0])
    require(masks==[[6,12],[10,12],[14,4]],'complete d4 weaker mask interface')
    squares=sorted({r*r%17 for r in range(9)})
    require([pow(2,e,15) for e in range(4)]==[1,2,4,8] and pow(2,4,15)==1,'exact order four')
    require(math.gcd(15,17)==1 and (15*8)%17==1,'repunit division justified modulo17')
    records=[]
    for parity in range(2):
        q=1 if parity==0 else -1;J=(q-1)*8%17
        require(J==parity and (q*q-1)%17==0,'two symbolic parity classes')
        for MC,MF0 in masks:
            R=(MC+q*(MF0+15))*J%17;bad=(2*R+3)%17
            require(bad not in squares,'uniform nonsquare contradiction')
            records.append(dict(k_parity=parity,q_mod17=q%17,J_mod17=J,MC=MC,MF0=MF0,
                                packed_R_mod17=R,impossible_square_residue=bad))
    require(exact(records,advertised['all_k_parity_cases']) and masks==advertised['masks'] and squares==advertised['square_residues_mod17'],'all advertised symbolic obstruction data')
    # Whole integer packing values supplement, rather than replace, the all-k proof.
    count=0
    for e in range(1,17):
        q=16**e;J=(q-1)//15
        for MC,MF0 in masks:
            for F,Z in [(1,1),(3,7),(q-1,q+2)]:
                R=(q*q-Z-q*F)*(q*q-1)+(MC+q*(MF0+15))*J
                require((2*R+3)%17 not in squares,'complete numeric packing identity')
                count+=1
    return dict(masks=masks,squares_mod17=squares,symbolic_parity_cases=records,whole_packing_checks=count,
                scope='All q=16^k at the declared necessary-mask interface; numerical checks are only supplements.')

def verify(root,author_root,scout_root):
    for name,pin in AUTHOR.items():require(sha((author_root/name).read_bytes())==pin,'author pin '+name)
    for name,pin in DEPENDENCIES.items():
        base=scout_root if name.startswith('complete83_free_coefficient_scout.') else root
        require(sha((base/name).read_bytes())==pin,'dependency pin '+name)
    a=json.loads((author_root/'free_coefficient83_native_alias.json').read_text())
    require(a['source_sha256']==AUTHOR['free_coefficient83_native_alias.py'],'author receipt source binding')
    require(a['dependency_pins']=={k:v for k,v in DEPENDENCIES.items() if not k.startswith('../../')},'all immediate author dependencies')
    packet=json.loads((scout_root/'complete83_free_coefficient_scout.json').read_text())['packet']
    interface_count=actual_interfaces(packet)
    require([x['t'] for x in a['modular_cases']]==[11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,65,71,83,101],'declared finite case list')
    selected=[case(x['t']) for x in a['modular_cases']]
    require(exact(selected,a['modular_cases']),'all twenty modular data rows')
    extra=[case(t) for t in range(11,104,2)]
    return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,dependency_pins=DEPENDENCIES,
                checked_source_rows=interface_count,exact_native=exact_native(a['exact_case']),declared_modular_cases=selected,
                extra_bounded_cases=extra,packing=masks_and_packing(a['mask_obstruction']),
                scope='Native first/main/index/strong factors and conditional auxiliary extension only; no input/transport, full polynomial zero or language theorem.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);ap.add_argument('--author-root',type=Path);ap.add_argument('--scout-root',type=Path)
    ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
    require(not(a.output and a.expect),'choose output or expect')
    r=verify(a.root,a.author_root or a.root,a.scout_root or a.root)
    require(exact(r,json.loads(json.dumps(r))),'type-exact JSON roundtrip')
    if a.expect:require(exact(r,json.loads(a.expect.read_text())),'exact receipt mismatch')
    if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',native_fields=r['exact_native']['fields'],modular_cases=len(r['declared_modular_cases']),bounded_extra_cases=len(r['extra_bounded_cases']),packing_cases=r['packing']['whole_packing_checks'],full_polynomial_zero=False)))
if __name__=='__main__':main()
