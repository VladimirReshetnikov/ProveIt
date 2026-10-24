#!/usr/bin/env python3
"""Exact integer candidates; finite algebra only, Python standard library.

The polynomial engine is retained from ProveIt package 71.  The constructions,
compact 23-variable formula, and checks in this module are new compositions.
"""
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
from polynomial import Poly, parse, require

ROOT=Path(__file__).resolve().parent
PIN='2605669a532342f153b13eb6b4a0af4b54f5fa37'
SRC=ROOT/'upstream/quartic41.json'
PORTS=['beta','K0','MC','MF','cone_A','cone_B']

def write(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')

def source(signed=False,paired=False):
    data=json.loads(SRC.read_text())
    rows=[parse(r) for r in data['residuals']]
    vs=list(data['variables'])
    q=parse('beta*J+1'); C=q-parse('F+alpha')
    if signed:
        require(rows[2]==parse('X-4*(beta*J+1)*w_scale'),'source scale')
        require(rows[13]==parse('(K0+4*w_scale)*(beta*J+1-F-alpha)-F-z*beta*J'),'source transport')
        require(rows[22]==parse('X-2*u**2'),'source twice-square')
        rows[13]=(parse('K0')*q+parse('X'))*C-q*parse('F')-parse('Z')*(q-1)
        rows[22]=parse('X')-4*q*parse('u**2')
        rows.pop(2)
        vs=[v for v in vs if v not in ('w_scale','z')]+['Z']
    guard_indices=[i for i,r in enumerate(rows) if any(v.startswith(('FA_pos','FC_pos')) for v in r.symbols())]
    require(len(guard_indices)==2,'two original guards')
    U=parse('cone_A*F'); W=parse('cone_B')*C
    G=U*W-(q-U-W)**2
    rows=[r for i,r in enumerate(rows) if i not in guard_indices]
    vs=[v for v in vs if not v.startswith(('FA_pos','FC_pos'))]
    if paired:
        ez=[i for i,r in enumerate(rows) if any(v.startswith('eta_zeta_pos') for v in r.symbols())]
        require(len(ez)==1,'eta-zeta source guard')
        require(rows[ez[0]]==parse('eta*zeta-1-eta_zeta_pos1**2-eta_zeta_pos2**2-eta_zeta_pos3*(eta_zeta_pos3+1)'), 'literal eta-zeta guard')
        rows=[r for i,r in enumerate(rows) if i not in ez]
        vs=[v for v in vs if not v.startswith('eta_zeta_pos')]+['t','p1','p2','p3']
        e=parse('eta*zeta')
        rows += [G*e-(parse('t**2')-G-e+1)**2-parse('1+p1**2+p2**2+p3*(p3+1)')]
    else:
        vs+=['p1','p2','p3']
        rows += [G-parse('1+p1**2+p2**2+p3*(p3+1)')]
    return vs,rows

def eliminate(vs,rows,name,rhs,history,restore):
    rhs=parse(rhs)
    require(name not in rhs.symbols(),'acyclic elimination')
    defining=Poly.symbol(name)-rhs
    matches=[i for i,r in enumerate(rows) if r==defining or r==-defining]
    require(len(matches)==1,'unique monic row '+name)
    history.append({'variable':name,'rhs':rhs.expression(),'deleted_row':matches[0]})
    for k in restore:
        restore[k]=restore[k].substitute({name:rhs})
    return [v for v in vs if v!=name],[r.substitute({name:rhs}) for i,r in enumerate(rows) if i!=matches[0]]

def packet(name,vs,rows,parent_rows,restore,history,witness,coefficient,scope,adjustments=None):
    require(set().union(*(r.symbols() for r in rows))-set(PORTS)==set(vs),'all variables live')
    ds=[r.degree(vs) for r in rows]
    # Exact coefficient is computed from full residual squares; no generic-
    # coefficient degree guess or probabilistic polynomial identity test.
    poly=sum((r*r for r in rows),Poly())
    require(poly.degree(vs)==2*max(ds),'degree after cancellation')
    require(poly.coefficient(witness,vs)==coefficient,'literal exact-degree coefficient')
    mapped=[]
    for i,row in enumerate(parent_rows):
        p=row.substitute(restore)
        if p==0:
            mapped.append({'parent_row':i,'zero_identity':True})
        else:
            hit=[j for j,r in enumerate(rows) if p==r or p==-r]
            change=None
            if not hit:
                for j,(k,multiplier) in (adjustments or {}).items():
                    if p==rows[j]-multiplier*rows[k]:
                        hit=[j]
                        change={'subtract_row':k,'multiplier':multiplier.expression()}
            require(len(hit)==1,'restoration of row '+str(i))
            entry={'parent_row':i,'new_row':hit[0]}
            if change is not None:entry['elementary_row_combination']=change
            mapped.append(entry)
    require(sorted(x['new_row'] for x in mapped if 'new_row' in x)==list(range(len(rows))), 'retained-row bijection')
    obj={'name':name,'domain':'unrestricted integers','variables':vs,
         'variable_count':len(vs),'fixed_ports':PORTS,
         'residuals':[r.expression() for r in rows],'residual_count':len(rows),
         'single_polynomial':'sum of the squares of all listed residuals',
         'exact_degree':poly.degree(vs),'coefficient_binding':'../coefficients/BINDING.json',
         'restoration':{k:v.expression() for k,v in restore.items() if k not in vs},
         'proof_scope':scope,'reference_commit':PIN}
    write(ROOT/'forms'/(name+'.json'),obj)
    write(ROOT/'forms'/(name+'_expanded.json'),poly.records())
    audit={'name':name,'status':'PASS','variables':len(vs),'residuals':len(rows),
           'exact_degree':poly.degree(vs),'residual_degrees':ds,
           'exact_degree_witness':{'powers':witness,'coefficient':coefficient},
           'expanded_symbolic_terms':len(poly.terms),'eliminations':history,
           'parent_restoration':mapped,'all_variables_live':True}
    write(ROOT/'certificates'/(name+'.json'),audit)
    return audit

def compact23():
    """Separately stated eleven-row presentation for the main candidate."""
    a={}
    def reg(n,text):a[n]=parse(text,a)
    for n,text in [
        ('q','beta*J+1'),('C','q-F-alpha'),('Y','(2*v_scale+1)*q**3'),
        ('X','4*q*u**2'),('H','4*a+3'),('Delta','a**2+H'),('V','f*o-c'),
        ('k','1-V+j*c+h*E'),('zeta','k-eta'),('P','k+E*(c-eta)'),
        ('D','X+a*c+gamma*H'),
        ('R','((q-1)*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*J'),
        ('U','cone_A*F'),('W','cone_B*C'),('G','U*W-(q-U-W)**2'),
        ('e','eta*zeta'),('Pos','1+p1**2+p2**2+p3*(p3+1)')]:reg(n,text)
    formulas=[
        'a-E-Y','E*X+E-X*a','c-(a-E)*k-eta',
        'tau**2-P**2+P*k-1','D**2-Delta*c**2-1',
        'j*c-V-R','(K0*q+X)*C-q*F-Z*(q-1)',
        'I-(2*r+1)*c**2','I**2-Delta*(f**2-1)',
        'y**2-I**2*(y**2-V**2)-1',
        'G*e-(t**2-G-e+1)**2-Pos']
    return [parse(s,a) for s in formulas],formulas

def build():
    audits=[]
    vs,rs=source(signed=True); parents=list(rs)
    restore={v:Poly.symbol(v) for v in vs}
    center=parse('tau_tail+P-eta-zeta')
    rs=[r.substitute({'tau':center}) for r in rs]
    vs=['tau_tail' if v=='tau' else v for v in vs];restore['tau']=center
    history=[{'coordinate_change':'tau=tau_tail+P-eta-zeta','integer_inverse':True}]
    for n,r in [('P','eta+zeta+E*(c-eta)'),('F2','f**2'),('g','y**2-V**2'),('N','(beta*J+1)*(L+1)'),('C2','c**2'),('X','D-a*c-gamma*(4*a+3)')]:
        vs,rs=eliminate(vs,rs,n,r,history,restore)
    require((len(vs),len(rs))==(31,18),'S31 dimensions')
    audits.append(packet('sextic31',vs,rs,parents,restore,history,{'r':2,'c':4},4,
        '71 determinant guard composed with 75 signed bootstrap; named source34 calibration inherited'))
    vs,rs=source(paired=True);parents=list(rs)
    restore={v:Poly.symbol(v) for v in vs};history=[]
    for n,r in [('N','(beta*J+1)*(L+1)'),('C2','c**2'),('F2','f**2'),('g','y**2-V**2'),('X','2*u**2'),('Baux','I**2'),('D','2*u**2+a*c+gamma*(4*a+3)'),('Delta','a**2+4*a+3'),('P','eta+zeta+E*(c-eta)'),('L','(beta*J+1)**2-1')]:
        vs,rs=eliminate(vs,rs,n,r,history,restore)
    require((len(vs),len(rs))==(26,14),'O26 dimensions')
    audits.append(packet('octic26',vs,rs,parents,restore,history,{'t':8},1,
        '71 determinant guard composed with 68 simultaneous positivity; source34 calibration inherited'))
    vs,rs=source(signed=True,paired=True);parents=list(rs)
    restore={v:Poly.symbol(v) for v in vs};history=[]
    for n,r in [('N','(beta*J+1)*(L+1)'),('C2','c**2'),('F2','f**2'),('g','y**2-V**2'),('X','4*(beta*J+1)*u**2'),('Baux','I**2'),('D','4*(beta*J+1)*u**2+a*c+gamma*(4*a+3)'),('Delta','a**2+4*a+3'),('P','eta+zeta+E*(c-eta)'),('L','(beta*J+1)**2-1'),('zeta','1-V+j*c+h*E-eta'),('V','f*o-c')]:
        vs,rs=eliminate(vs,rs,n,r,history,restore)
    require((len(vs),len(rs))==(23,11),'D23 dimensions')
    comp,formulas=compact23()
    require(comp==rs,'independent compact eleven-row display')
    audits.append(packet('degree12_23',vs,rs,parents,restore,history,{'eta':4,'f':4,'o':4},1,
        'signed bootstrap plus joint determinant guard; source34 calibration inherited'))
    write(ROOT/'forms'/'compact23_display.json',{'variables':vs,'residuals':formulas,'verified_exactly_against_full_elimination':True})
    # Reduce modulo the retained strong norm BEFORE eliminating I.
    # This is an invertible polynomial row operation, not mere agreement
    # at numerical test points: r10_new = r10_old + multiplier*r9.
    multiplier=parse('y**2-(f*o-c)**2')
    rs[9]=rs[9]+multiplier*rs[8]
    history.append({'row_operation':'r10 := r10+(y**2-(f*o-c)**2)*r9','invertible':True})
    vs,rs=eliminate(vs,rs,'I','(2*r+1)*c**2',history,restore)
    require((len(vs),len(rs))==(22,10),'D22 dimensions')
    # Center the remaining Pell root; y_tail is unrestricted, so this is a
    # bijective integral polynomial coordinate change.
    shear=parse('f*o-c+y_tail')
    rs=[r.substitute({'y':shear}) for r in rs]
    for k in restore:restore[k]=restore[k].substitute({'y':shear})
    vs=['y_tail' if v=='y' else v for v in vs]
    multiplier=multiplier.substitute({'y':shear})
    history.append({'coordinate_change':'y_old=f*o-c+y_tail','inverse':'y_tail=y_old-f*o+c','integer_inverse':True})
    audits.append(packet('degree14_22',vs,rs,parents,restore,history,{'a':4,'f':6,'o':2,'y_tail':2},4,
        'invertible norm-row reduction, monic I elimination, and integral root centering',
        adjustments={8:(7,multiplier)}))
    write(ROOT/'certificates'/'ALGEBRA.json',audits)
    return audits

def coefficients():
    spec=importlib.util.spec_from_file_location('native34',ROOT/'coefficients/build_coefficients.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    values,finite_audit=module.construct()
    values={'beta':values['beta'],'K0':values['K'],'MC':values['MC'],'MF':values['MF_source'],'cone_A':1<<1113,'cone_B':1<<666104}
    upstream=json.loads((ROOT/'coefficients/UPSTREAM_BINDING.json').read_text())
    filenames={'beta':'beta.bin.gz','K0':'K.bin.gz','MC':'MC.bin.gz','MF':'MF_source.bin.gz','cone_A':'cone_A.bin.gz','cone_B':'cone_B.bin.gz'}
    records={}
    for name,value in values.items():
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        path=ROOT/'coefficients/payloads'/filenames[name]
        require(gzip.decompress(path.read_bytes())==raw,'literal coefficient payload '+name)
        digest=hashlib.sha256(raw).hexdigest()
        require(digest==upstream['payloads'][name]['raw_sha256'],'coherent source34 port '+name)
        records[name]={'path':'payloads/'+filenames[name],'raw_sha256':digest,'bits':value.bit_length(),'raw_bytes':len(raw),'format':'gzip of minimal unsigned little-endian'}
    result={'reference_commit':PIN,'tuple':'mixed-parity-unrounded-1064921','MF':'already shifted; use once','payloads':records,'raw_bytes':sum(x['raw_bytes'] for x in records.values()),'native_finite_audit':finite_audit,'status':'PASS'}
    write(ROOT/'coefficients'/'BINDING.json',result)
    return result

if __name__=='__main__':
    audit=build();co=coefficients()
    print(json.dumps({'status':'PASS','candidates':[{k:x[k] for k in ('name','variables','residuals','exact_degree','expanded_symbolic_terms')} for x in audit],'coefficient_bytes':co['raw_bytes']},indent=2))
