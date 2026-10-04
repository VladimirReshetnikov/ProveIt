#!/usr/bin/env python3
"""Pinned data-only obstruction; does not execute predecessor code."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import comb, gcd
from pathlib import Path

PINS = {'complete83_independent_gamma_scout.py': 'b67ee981d5475a745094924d6ec3cbe72dfb38e3d28d9bd2c144ff0c2a59dc18', 'complete83_independent_gamma_scout.json': 'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20', 'complete83_independent_gamma_scout.md': 'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41', 'complete80_main_root_gap_collapse.py': '61176046f591dc2af91de068a3042b88ed776c6dd6d681c0efaafb108e477e5b', 'complete80_main_root_gap_collapse.json': 'e059c395c7b906fb33b8e2e4acc47bf54e9f9753dddb5811e35c834c10294762', 'complete80_main_root_gap_collapse.md': '7bb2a237dce7c04a373a6c0ad0510decd056785d930c967a9b244598fdcebea9', 'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf', 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', 'review_complete74_asymmetric_scale_math.md': 'a7f8d64389597c5a8fff93bad1f023dfc440d736bb9d77f2acd549e758aa0b58', 'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541', '../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md': '75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87', '../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md': 'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39'}

def require(b,s):
    if not b: raise ValueError(s)
def canon(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def digest(x): return sha256(x).hexdigest()

def pell(A,n):
    disc=A*A-1;u,v=1,0;x,y=A,1
    while n:
        if n&1:u,v=u*x+disc*v*y,u*y+v*x
        x,y=x*x+disc*y*y,2*x*y;n//=2
    return u,v

def curve():
    summaries=[];records=[];pell_records=[]
    for R in range(3,34,2):
        r=(R-1)//2;central=comb(2*r,r)
        xs=sorted(set(range(1,65))|{(1<<R)-2,(1<<R)-1,1<<R,(1<<R)+1,(1<<R)+2})
        vals=[]
        for X in xs:
            M=sum(comb(2*r,r+j)*X**j for j in range(r+1));H=2*(X+1)*M+3
            require(M>=((1<<(2*r))+central)//2,'monotone upper-half polynomial')
            require(H>max(X,1<<R),'strict modulus bound')
            integral=((1<<R)-X)%H==0
            require(integral==(X==1<<R),'unique positive congruence point')
            vals.append([X,H,integral]);records.append([R,X,H,integral])
        summaries.append({'R':R,'tested_X_count':len(xs),'minimum_H_minus_2powerR':str(min(H-(1<<R) for X,H,ok in vals)),'integral_X':[X for X,H,ok in vals if ok]})
    for R in (3,7,11,15):
        r=(R-1)//2
        for X in ((1<<R)-2,1<<R,(1<<R)+2):
            M=sum(comb(2*r,r+j)*X**j for j in range(r+1));require(M%2==0,'even curve')
            a=M//2*(X+1);H=4*a+3;D,c=pell(a+2,R);numerator=D-a*c-X
            require((D-a*c-(1<<R))%H==0,'main Pell exponent recurrence')
            require((numerator%H==0)==(X==1<<R),'actual main-root divisibility')
            if X==1<<R:require(numerator>0,'positive main quotient')
            pell_records.append({'R':R,'X':X,'H':str(H),'main_quotient_remainder':str(numerator%H),'integral':numerator%H==0})
    return {'tested_points':len(records),'records_sha256':digest(canon(records)),'summaries':summaries,'exact_small_Pell_interfaces':pell_records,'scope':'Polynomial-curve and main-root arithmetic only; no native/compiler history or full zero.'}

def raw_models():
    records=[]
    # Local radix/coefficient interface models, not actual window compilers.
    b=5;L=5;d=b*L;r=1<<b;B=r**L;DC=r*r+r**3;DR=r;K=DC+B*DR
    for N in (3,5,7):
        t=d*N;q=1<<t;mod=q-1
        for x in range(1,(N-1)//2+1):
            u=2*d*x+b;C=1+(1<<u);Rword=(B*C)%mod
            require(2*x<N and DC*C<q,'nonwrapping DC term')
            # Sparse raw inner-radix coefficients before the arbitrary rotation.
            raw={}
            def inc(i):raw[i]=raw.get(i,0)+1
            for i in (0,2*L*x+1):
                for j in (2,3):inc(i+j)
            for i in (L,(L*(2*x+1)+1)%(L*N)):inc(i+1)
            require(max(raw)<L*N and max(raw.values())<=2,'local nonwrap coefficient bound')
            require(sum(v*r**i for i,v in raw.items())==DC*C+DR*Rword,'literal raw field')
            vals=[];powers=[]
            for e in range(t):
                Yword=((1<<e)*C)%mod;Factual=DC*C+DR*Rword+Yword
                digits=[(Yword//r**j)%r for j in range(L*N)]
                require(max(digits)<=r//2,'rotation digit bound')
                require(max(raw.get(j,0)+digits[j] for j in range(L*N))<=r-2,'no inner carries')
                require(DC<=Factual<mod,'strict representative range')
                require(Factual==(K+(1<<e))*C%mod and Factual!=4,'transport excludes target4')
                vals.append(Factual);powers.append(pow(2,e,mod))
            require(gcd(C,mod)==1,'odd-exponent inverse')
            target=(4*pow(C,-1,mod)-K)%mod
            require(target not in powers,'target outside dyadic subgroup')
            records.append({'b':b,'L':L,'d':d,'N':N,'x':x,'u':u,'DC':str(DC),'DR':str(DR),'q':str(q),'rotations':t,'min_field':str(min(vals)),'max_field':str(max(vals)),'transport_multiplier_residue':str(target),'wraps_End_to_origin':2*x+1==N,'all_field_values_sha256':digest(canon(vals))})
    return {'models':records,'rotations_checked':sum(r['rotations'] for r in records),'scope':'Small exact raw-coefficient/radix models satisfy only the local hypotheses. They are not authentic fixed-program numeral tuples, histories, native Pell witnesses or language counterexamples.'}

def build(root):
    for name,pin in PINS.items():require(digest((root/name).read_bytes())==pin,'pin '+name)
    parent=json.loads((root/'complete83_independent_gamma_scout.json').read_text())
    packet=parent['packet'];rows=packet['source'];by={r[0]:r for r in rows}
    required=[['repunit','*','Bm1','Jrep'],['q','+','repunit',1],['Lbig','*','q','q'],['n2','*','Lbig','q'],['wn2','*','w','q'],['sn2','*','s','n2'],['UM','*','wn2','sn2'],['R12','+','UM','sn2'],['a4','*',4,'R12'],['a4m5','+','a4',3],['cam2','*','R10a','R12'],['D1','+','wn2','cam2'],['gam','*','sigma','a4m5'],['R14','+','D1','gam'],['q_minus_F','-','q','F'],['q_minus_FZ','-','q_minus_F','Z'],['C_after_alpha','-','q_minus_FZ','alpha'],['scaled_t','*','twice_cell_bits','x'],['marked_rhs','-','C_after_alpha','scaled_t'],['W','-','marked_rhs','Z'],['odd_index','+','scaled_t','inner_bits'],['kinner','+','Kconstant','w'],['innerC','*','kinner','marked_rhs'],['transport_partial','+','innerC','q_minus_F'],['local_rhs','*','transport_quotient','repunit'],['norm_transport','-','transport_partial','local_rhs'],['norm_index','-','index_difference','r_lhs']]
    for row in required:require(by[row[0]]==row,'literal source boundary '+row[0])
    require('gamma_sum' not in by,'independent gamma source')
    known=set(packet['free'])
    for n,op,a,b in rows:
        require(n not in known and all(type(v)is int or v in known for v in (a,b)),'topology');known.add(n)
    live={packet['output']};todo=list(live)
    while todo:
        n=todo.pop()
        if n in by:
            for v in by[n][2:]:
                if type(v)is str and v not in live:live.add(v);todo.append(v)
    require(known==live,'all source live')
    counts=Counter(r[1] for r in rows)
    require((len(rows),counts['*'],counts['+']+counts['-'],len(packet['witnesses']))==(83,47,36,18),'ledger')
    def ancestors(name):
        reached={name};queue=[name]
        while queue:
            n=queue.pop()
            if n in by:
                for v in by[n][2:]:
                    if type(v)is str and v not in reached:reached.add(v);queue.append(v)
        return reached
    noninput=[n for n in packet['factors'] if n!='norm_input']
    for n in noninput:require(not {'delta','rho'}&ancestors(n),'refreshed input cannot change noninput '+n)
    return {'status':'PASS','source_sha256':digest(Path(__file__).read_bytes()),'pins':PINS,'scope':'Exact family obstruction within the unresolved independent-gamma83 source. No new circuit, universal bound, overall language resolution or full compiler tuple is asserted.','packet':packet,'copied_packet_sha256':digest(canon(packet)),'source_boundaries':required,'source_checks':{'all_83_rows_live':True,'all_supplied_ports_live':True,'M':47,'A':36,'witnesses':18,'noninput_factors_independent_of_delta_rho':noninput},'theorem':{'curve':'For every odd R>=3 and integer X>=1, H_R(X)>max(X,2^R), so H_R(X)|(2^R-X) iff X=2^R.','transport':'On actual inherited compiler coefficients, q=B^N and C=1+2^(2dx+b)<q give ((K+2^e)C mod(q-1))>=DC>4 for every integer exponent e, hence no F=4 transport unit.','full_source':'No positive independent-gamma83 zero has Z=1,F=4,W=2^(2dx+b) on a valid fixed compiler slice, regardless of delta,rho.'},'curve_checks':curve(),'raw_coefficient_diagnostics':raw_models()}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();out=build(a.root)
    if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    else:require(canon(json.loads(a.expect.read_text()))==canon(out),'exact typed receipt')
    print('PASS: exact main-congruence and sparse-marker transport obstruction; independent83 language remains unresolved')
if __name__=='__main__':main()
