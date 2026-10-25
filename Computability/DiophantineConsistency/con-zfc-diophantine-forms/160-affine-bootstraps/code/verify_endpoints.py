#!/usr/bin/env python3
"""Independent finite audit of the signed-front Diophantine quartics.

This checker imports no producing/search module. Its polynomial algebra and
the Horn-factorization checker are separately authored inherited dependencies.
The unbounded mathematical proof is a different part of the deliverable.
"""
from pathlib import Path
import argparse,copy,hashlib,json,subprocess,sys,tempfile

ROOT=Path(__file__).resolve().parent.parent
PROFILES=('original_horizon','horizon16','horizon8','horizon8_small_frame','horizon8_linear_frame','horizon8_difference_frame')
PINS={
 'direct/factorial_free_affine/raw_source.json':'7b2d75791f10c717bbadca278e78e9f315508d56acdc8ad3eb82b63ddbb2e855',
 'direct/check_factorial_free.py':'6c68523f432dac8d067dbf1e2ff16ea559d9176ec3be719a1df95ddb771e4e57',
 'direct/parent/code/inherited_independent_algebra.py':'13c300ccbc77c1ff4a54a923f3bd24d6152ee65a9bddd8c1f4152d49cc9ba3a9'}

def need(ok,message):
    if not ok:raise ValueError(message)
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def load_checker(parent):
    for name,h in PINS.items():need(sha(parent/name)==h,'inherited byte pin '+name)
    sys.path.insert(0,str(parent/'direct'))
    import check_factorial_free as C
    return C

def source_check(C,parent,folder,actual=None):
    old=read(parent/'direct/factorial_free_affine/raw_source.json')
    cert=read(folder/'source_delta.json');profile=cert['profile']
    need(profile in PROFILES,'known source profile')
    need(cert['source_sha256']==PINS['direct/factorial_free_affine/raw_source.json'],'source delta pin')
    need(cert['source_relative_path']=='direct/factorial_free_affine/raw_source.json','source delta path')
    names={v['name']:i for i,v in enumerate(old['variables'])}
    bylabel={}
    for i,r in enumerate(old['residuals']):bylabel.setdefault(r['label'],[]).append(i)
    def one(l):
        need(len(bylabel.get(l,[]))==1,'unique source relation '+l);return bylabel[l][0]
    t=names['t0'];h=names['cofinal.horizon_root'];d=names['growth.power_base']
    F=names['crt.growth_majorant_F'];R=names['mul.1'];q=names['pow2.output']
    z=names['radix.odd_square_root_half'];sb=names['beta.odd_square_multiplier'];v=names['beta.odd_square_root_half']
    V=C.var;K=C.const;S=C.scale;P=C.plus;M=C.times
    need(C.poly(old['residuals'][0]['terms'])==P(V(R),S(M(V(F),V(F)),-1)),'selector old quadratic relation')
    square=lambda p:M(p,p)
    oldspec={one('radix.odd_square'):P(V(q),S(square(P(S(V(z),2),K(1))),-1)),
      one('beta.odd_square_multiplier'):P(V(sb),S(square(P(S(V(v),2),K(1))),-1)),
      one('cofinal.horizon'):P(V(t),S(square(V(h)),-1)),
      one('growth.base_definition'):P(V(d),S(V(t),-2),K(-34))}
    for i,p in oldspec.items():need(C.poly(old['residuals'][i]['terms'])==p,'old source identity '+str(i))
    changes={0:('selector.linear_offset',P(V(R),S(V(F),-1))),
      one('radix.odd_square'):('radix.affine_four',P(V(q),S(V(z),-4),K(-1))),
      one('beta.odd_square_multiplier'):('beta.affine_odd_multiplier',P(V(sb),S(V(v),-2),K(-1)))}
    if profile!='original_horizon':
        scale=16 if profile=='horizon16' else 8
        changes[one('cofinal.horizon')]=('cofinal.affine_horizon',P(V(t),S(V(h),-scale),K(16)))
    if profile in ('horizon16','horizon8_linear_frame','horizon8_difference_frame'):
        changes[one('growth.base_definition')]=('growth.base_definition',P(V(d),S(V(t),-1),K(-18)))
    if profile in ('horizon8_small_frame','horizon8_linear_frame','horizon8_difference_frame'):
        atoms=extract_frame_atoms(C,old)
        substitutions=[(t,P(S(V(h),8),K(-16))),
          (d,P(S(V(h),16 if profile=='horizon8_small_frame' else 8),K(2))),
          (R,V(F)),(q,P(S(V(z),4),K(1)))]
        transformed=[]
        for atom in atoms:
            for variable,replacement in substitutions:atom=C.subst(atom,variable,replacement)
            need(C.degree(atom)<=1,'affine transformed frame atom')
            transformed.append(atom)
        used=sorted({m[0] for atom in transformed for m in atom if len(m)==1})
        bounds=[abs(a.get((),0))+sum(c*c//4 for m,c in a.items() if len(m)==1) for a in transformed]
        constant=max(16,max(bounds)+1);W=names['shared.W']
        replacement=P(V(W),K(-constant),*[{(i,i):-1} for i in used])
        changes[one('shared.frame_definition')]=('shared.frame_definition',replacement)
        framecert={'schema':'linear_atom_majorant_v1','constant':constant,
          'original_atoms':[C.terms(a) for a in atoms],
          'substitutions':[{'coordinate':i,'replacement':C.terms(p)} for i,p in substitutions],
          'atoms':[C.terms(a) for a in transformed],'coordinate_squares':used,'atom_bounds':bounds,
          'identity':'For every integer z, a*z <= z*z+floor(a*a/4), and -a*z obeys the same bound.'}
        if profile=='horizon8_difference_frame':
            pr=one('cap.pooled_index_residue');yt=names['index0.Y'];yft=names['index2.Y']
            first=P(V(yt),S(V(t),-1),K(-16))
            second=P(V(yft),S(V(R),-1),S(V(t),-1),K(-16))
            difference=P(V(yft),S(V(yt),-1),S(V(R),-1))
            need(difference==P(second,S(first,-1)),'orientation difference identity')
            pool=P(C.poly(old['residuals'][pr]['terms']),S(M(second,second),-1),M(difference,difference))
            changes[pr]=('cap.pooled_index_residue',pool)
            framecert['orientation_difference']={'row':pr,'retained_error':C.terms(first),
              'old_error':C.terms(second),'new_error':C.terms(difference),
              'small_error_bound':'(4m+5)W^2+4m < 4W^3 for m<=15,W>=19'}
        need(read(folder/'frame_certificate.json')==framecert,'complete affine-atom majorant certificate')
    expected=copy.deepcopy(old)
    for i,(lab,p) in changes.items():expected['residuals'][i]={'label':lab,'terms':C.terms(p)}
    expected['variant']+=':signed_front_'+profile
    actual=actual if actual is not None else read(folder/'raw_source.json')
    need(expected==actual,'complete new source binding')
    want=[{'row':i,'old':old['residuals'][i],'new':expected['residuals'][i]} for i in sorted(changes)]
    need(cert['changes']==want,'exact semantic edit ledger')
    need(actual['domain']=='unrestricted integers','new source domain')
    need(all(C.degree(C.poly(r['terms']))<=2 for r in actual['residuals']),'new source quadratic')
    return actual

def extract_frame_atoms(C,raw):
    """Reconstruct an exact SOS frame identity, including the pre-sign bounds."""
    names={v['name']:i for i,v in enumerate(raw['variables'])}
    hit=[r for r in raw['residuals'] if r['label']=='shared.frame_definition'];need(len(hit)==1,'frame unique')
    row=C.poly(hit[0]['terms']);W=names['shared.W']
    need(row.get((W,))==1,'frame W coefficient')
    rhs=C.scale(C.plus(row,C.scale(C.var(W),-1)),-1)
    t=C.plus(C.var(names['t0']),C.const(16));q=C.var(names['pow2.output']);R=C.var(names['mul.1'])
    required=[t,C.plus(t,C.const(1)),C.plus(R,t),q,C.plus(q,C.const(1))]
    rest=C.plus(rhs,C.const(-2),*[C.scale(C.times(a,a),-1) for a in required])
    diagonal={m[0]:c for m,c in rest.items() if len(m)==2 and m[0]==m[1]}
    need(all(c==1 for c in diagonal.values()),'frame diagonal coefficients')
    squares=[]
    for i in sorted(diagonal):
        lin=rest.get((i,),0);need(lin in (0,2),'frame integral centers')
        squares.append(C.plus(C.var(i),C.const(lin//2)))
    expected=C.plus(*[C.times(a,a) for a in squares])
    need(rest==expected,'complete frame square decomposition')
    d=names['growth.power_base'];need(C.var(d) in squares,'actual growth base retained in frame')
    anchor=names['add.380'];need(C.plus(C.var(anchor),C.const(1)) in squares,'anchor index square retained')
    return required+squares

def frame_check(C,raw,folder):
    if (folder/'frame_certificate.json').exists():
        cert=read(folder/'frame_certificate.json')
        return {'exact_identity':'W = C + sum of distinct underlying coordinate squares',
          'coordinate_squares':len(cert['coordinate_squares']),'bounded_affine_atoms':len(cert['atoms']),
          'pre_sign_lower_bound':cert['constant'],'maximum_affine_bound':max(cert['atom_bounds']),
          'reason':'|c+sum(a_i*x_i)| <= sum(x_i^2)+|c|+sum(floor(a_i^2/4))'}
    atoms=extract_frame_atoms(C,raw)
    return {'exact_identity':'W = 2 + sum of the listed integer-atom squares',
      'squares':len(atoms),'pre_sign_lower_bound':7,
      'reason':'q=4z+1 gives q^2+(q+1)^2>=5'}

def corruptions(C,parent,folder):
    rejected=[]
    def rejects(label,run):
        try:run()
        except (ValueError,KeyError,IndexError):rejected.append(label);return
        raise ValueError('corruption was accepted: '+label)
    raw=read(folder/'raw_source.json');delta=read(folder/'source_delta.json')
    for edit in delta['changes']:
        bad=copy.deepcopy(raw);bad['residuals'][edit['row']]['terms'][0][0]+=1
        rejects('source row '+str(edit['row']),lambda b=bad:source_check(C,parent,folder,b))
    bad=copy.deepcopy(raw);r=next(x for x in bad['residuals'] if x['label']=='shared.frame_definition');r['terms'][0][0]+=1
    rejects('unlisted frame alteration',lambda:source_check(C,parent,folder,bad))
    endpoint=folder/'balanced';source=read(folder/'equation.json')
    cert=read(endpoint/'certificate.json');cert['projections'][0]['replacement'][0][0]+=1
    rejects('affine inverse coefficient',lambda:C.affine_check(source,endpoint,cert))
    expanded=read(endpoint/'expanded_polynomial.json');expanded['terms'][0][0]+=1
    rejects('collected quartic coefficient',lambda:C.quartic_check(endpoint,expanded=expanded))
    return rejected

def verify(parent,equations,variants,rebuild=False):
    C=load_checker(parent)
    # Bind the retained literal source to its independently specified parent
    # construction before inspecting any new edit.
    C.source_check(parent/'direct/factorial_free_affine')
    reports={}
    for variant in variants:
        folder=equations/variant;raw=source_check(C,parent,folder)
        reports[variant]={'source':'PASS','frame':frame_check(C,raw,folder),
          'finite_maps':C.projection_check(folder,raw),'stage':C.quartic_check(folder),'endpoints':{}}
        for profile in ('balanced','dimension'):
            endpoint=folder/profile
            reports[variant]['endpoints'][profile]={'maps':C.affine_check(read(folder/'equation.json'),endpoint),
              'metrics':C.quartic_check(endpoint)}
        reports[variant]['rejected_corruptions']=corruptions(C,parent,folder)
    summary=read(equations/'ENDPOINTS.json')
    for variant in variants:
        for profile in ('balanced','dimension'):
            need(summary[variant][profile]==reports[variant]['endpoints'][profile]['metrics'],'endpoint summary metrics')
        need(summary[variant]['stage']==reports[variant]['stage'],'stage summary metrics')
    rebuilt=None
    if rebuild:
        with tempfile.TemporaryDirectory(prefix='conzfc-rebuild-') as td:
            out=Path(td)/'equations'
            cmd=[sys.executable,'-B',str(ROOT/'code/build_endpoints.py'),'--parent',str(parent),'--output',str(out),'--variants',*variants]
            subprocess.run(cmd,check=True,capture_output=True,text=True)
            count=0
            for variant in variants:
                for p in sorted((out/variant).rglob('*.json')):
                    need(p.read_bytes()==(equations/p.relative_to(out)).read_bytes(),'byte rebuild '+str(p.relative_to(out)))
                    count+=1
            rebuilt={'files':count,'comparison':'byte-identical'}
    return {'status':'PASS','scope':'Exact finite source edits, frame SOS identity, inherited Horn identities, monic restorations, integral affine maps, and every quartic coefficient. Unbounded arithmetic and logical calibration are separate.','profiles':reports,'rebuild':rebuilt}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--parent',type=Path,default=ROOT/'inherited_factorial_free')
    ap.add_argument('--equations',type=Path,default=ROOT/'equations')
    ap.add_argument('--variants',nargs='+',choices=PROFILES)
    ap.add_argument('--rebuild',action='store_true');ap.add_argument('--receipt',type=Path)
    args=ap.parse_args();variants=args.variants or list(read(args.equations/'ENDPOINTS.json'))
    result=verify(args.parent,args.equations,variants,args.rebuild)
    if args.receipt:args.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
