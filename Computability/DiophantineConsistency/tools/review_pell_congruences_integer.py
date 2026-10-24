#!/usr/bin/env python3
"""Independent literal/identity audit of the integer Pell-congruence intake."""
import argparse,ast,gzip,hashlib,json,sys
from pathlib import Path
import sympy as S
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
OUT=HERE.parent/'PROPOSAL_REVIEW_PELL_CONGRUENCES_INTEGER.json'
def need(b,label):
    if not b:raise RuntimeError(label)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def eq(x,y,label):need(S.expand(x-y)==0,label)
def interpret(text,env,constant):
    def rec(n):
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.Constant)and type(n.value)is int:return constant(n.value)
        if isinstance(n,ast.UnaryOp)and isinstance(n.op,ast.USub):return -rec(n.operand)
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,ast.Add):return rec(n.left)+rec(n.right)
            if isinstance(n.op,ast.Sub):return rec(n.left)-rec(n.right)
            if isinstance(n.op,ast.Mult):return rec(n.left)*rec(n.right)
            if isinstance(n.op,ast.Pow)and isinstance(n.right,ast.Constant)and type(n.right.value)is int and n.right.value>=0:return rec(n.left)**n.right.value
        raise RuntimeError('nonpolynomial syntax')
    return rec(ast.parse(text,mode='eval').body)
def names(text):return {n.id for n in ast.walk(ast.parse(text,mode='eval'))if isinstance(n,ast.Name)}
def degree(text,env):
    def rec(n):
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.Constant):return 0
        if isinstance(n,ast.UnaryOp):return rec(n.operand)
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,(ast.Add,ast.Sub)):return max(rec(n.left),rec(n.right))
            if isinstance(n.op,ast.Mult):return rec(n.left)+rec(n.right)
            if isinstance(n.op,ast.Pow):return rec(n.left)*n.right.value
        raise RuntimeError('degree syntax')
    return rec(ast.parse(text,mode='eval').body)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path('/tmp/dioph-wave11-arrivals-eae4f1952b/con_zfc_pell_congruences_2026-10-23'))
    ap.add_argument('--replay',type=Path,default=Path('/tmp/proofs62ff-pell-congruences-integer-replay/REPLAY.json'))
    args=ap.parse_args();root=args.root
    arrival=json.loads((root.parent/'ARRIVAL.json').read_text())
    need(sha(REPO/arrival['archive'])==arrival['sha256'],'actual intake ZIP SHA256')
    prov=json.loads((root/'SOURCE_PROVENANCE.json').read_text())
    for row in prov['entries']:
        raw=(root/row['file']).read_bytes();need(hashlib.sha256(raw).hexdigest()==row['sha256'],'inherited source digest')
        need(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==row['git_blob_sha1'],'inherited Git blob')
    binding=json.loads((root/'coefficients/BINDING.json').read_text());ports={};hashes={}
    for name,row in binding['ports'].items():
        p=root/'coefficients'/row['file'];raw=gzip.decompress(p.read_bytes())
        need(sha(p)==row['sha256_gzip']and hashlib.sha256(raw).hexdigest()==row['sha256_raw'],'whole six-port binding')
        value=int.from_bytes(raw,'little');need(value.bit_length()==row['bits']and len(raw)==row['raw_bytes'],'port sizes')
        ports[name]=value;hashes[name]=row['sha256_raw']
    need(ports['beta']==(1<<1064921)-1 and ports['cone_A']==1<<1113 and ports['cone_B']==1<<666104,'exact scales')
    prime=1000000007;lam=S.Symbol('t');results={}
    targets=['degree88_17','degree32_18','degree28_19','degree20_20_rank_register']
    for name in targets:
        path=root/'transport'/(name+'.json');packet=json.loads(path.read_text());cert=packet['degree_certificate']
        known=set(packet['variables']+packet['fixed_numerals']);deps={}
        env={n:S.Poly(cert['slopes'][n]*lam,lam,modulus=prime)for n in packet['variables']}
        env.update({n:S.Poly(v%prime,lam,modulus=prime)for n,v in ports.items()})
        dd={n:1 for n in packet['variables']};dd.update({n:0 for n in ports})
        for n,text in packet['polynomial_abbreviations']:
            need(n not in known and names(text)<=known,'topological abbreviation')
            deps[n]=names(text);known.add(n)
            env[n]=interpret(text,env,lambda x:S.Poly(x,lam,modulus=prime));dd[n]=degree(text,dd)
        rows=packet['factored_residuals'];live=set().union(*(names(s)for s in rows));todo=list(live)
        while todo:
            n=todo.pop()
            for child in deps.get(n,set()):
                if child not in live:live.add(child);todo.append(child)
        need(set(packet['variables']+packet['fixed_numerals'])<=live,'all variables/fixed ports live')
        bounds=[degree(s,dd)for s in rows]
        polyrows=[interpret(s,env,lambda x:S.Poly(x,lam,modulus=prime))for s in rows]
        row=cert['residual_index_zero_based'];d=cert['residual_exact_degree']
        need(bounds==cert['residual_degree_upper_bounds'],'independent upper-degree bounds')
        need(d==max(bounds)and polyrows[row].degree()==d,'actual slice degree attainment')
        need(int(polyrows[row].LC())%prime==cert['coefficient_of_t_to_residual_degree'],'independent actual leading coefficient')
        need(packet['variable_count']==len(packet['variables'])and packet['residual_count']==len(rows),'literal dimensions')
        results[name]=dict(variables=len(packet['variables']),residuals=len(rows),exact_degree=2*d,
          residual_degree_upper_bounds=bounds,selected_row=row,leading_coefficient_mod_prime=int(polyrows[row].LC())%prime,
          literal_sha256=sha(path),all_declared_inputs_live=True)
    c,f,R,T,o,V=S.symbols('c f R T o V')
    crt=f*c*T-f*f*R-c
    eq(crt,f*(c*T-f*R)-c,'CRT first congruence exact identity')
    eq(crt+R,f*c*T-c-(f*f-1)*R,'CRT second congruence exact identity')
    tau,P,k=S.symbols('tau P k');new=2*tau-2*P+k
    eq(new*new+2*new*(2*P-k)+k*k-4,4*(tau*tau-P*P+P*k-1),'half-centered exact identity')
    q,K,W,C,z,alpha,MC,MF,J=S.symbols('q K W C z alpha MC MF J')
    F=(K+W)*C-z*(q-1);al=q-F-C
    eq(q-F-al,C,'alpha-C inverse');eq((K+W)*C-F-z*(q-1),0,'monic F transport')
    eq(((q-1)*(q-F)+al)*(q*q-1)+(MC+q*MF)*J,(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J,'all-occurrence rank simplification')
    crt_cases=0
    for cc in range(-12,13):
        for ff in range(-12,13):
            if not cc or not ff or (ff*ff-1)%cc:continue
            for rr in range(-4,5):
                for vv in range(-12,13):
                    lhs=(vv+cc)%ff==0 and (vv+rr)%cc==0
                    rhs=(vv+ff*ff*rr+cc)%(ff*cc)==0
                    need(lhs==rhs,'signed CRT exact-class bounded control');crt_cases+=1
    c0=105534389824824194647382298625
    need(1<<96<=c0<c0+1<=3*(1<<95),'canonical F coefficient bounds')
    need(121*8791+1113==1064921-97 and 121*3296+666104==1064921-1,'common canonical scales')
    rr,cc,yy,ff,reg=S.symbols('r c y f R')
    VV=ff*cc*S.Symbol('T')-ff*ff*reg-cc;II=(2*rr+1)*cc*cc
    aux=VV*VV+(1-II*II)*yy*(2*VV+yy)-1
    pp=S.Poly(S.expand(aux*aux),rr,cc,yy,ff,reg,S.Symbol('T'))
    need(pp.coeff_monomial(rr**4*cc**8*yy**2*ff**4*reg**2)==64,'uniform 20/20 coefficient')
    replay=json.loads(args.replay.read_text());need(replay['status']=='PASS'and len(replay['commands'])==10,'normal/optimized scoped replays')
    out=dict(status='PASS',arrival=arrival,sympy=S.__version__,python_optimization=sys.flags.optimize,
      authenticated_inherited_sources=len(prov['entries']),whole_tuple_raw_hashes=hashes,
      exact_coordinate_and_halfcenter_identities=True,signed_CRT_control_cases=crt_cases,
      canonical_scale_checks=True,rank_register_uniform_degree20_coefficient=64,
      literal_results=results,scoped_replay=replay,
      proof_scope='Ordinary early-rank/CRT/guard/monic projection review in companion note. No Lean, object-ZFC derivation, new native calibration or full release replay.')
    name=OUT if not sys.flags.optimize else OUT.with_name(OUT.stem+'_OPTIMIZED.json')
    name.write_text(json.dumps(out,indent=2)+'\n');print('PASS four target literals, whole tuple, exact local identities and scoped replays')
if __name__=='__main__':main()
