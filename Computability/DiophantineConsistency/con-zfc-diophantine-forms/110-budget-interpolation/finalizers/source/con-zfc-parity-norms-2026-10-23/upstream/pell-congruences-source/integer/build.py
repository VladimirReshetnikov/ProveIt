#!/usr/bin/env python3
"""Exact, standard-library construction of the integer consistency forms.

The arithmetic engine is inherited from package 71 (see ../NOTICE.md).
All new source data are inert expressions parsed by a restricted AST parser.
No blank-machine simulation or consistency assumption is used.
"""
from pathlib import Path
import gzip
import hashlib
import json
import sys
from polynomial import Poly, parse, require

# Expanded inert residuals can contain several thousand summands.
sys.setrecursionlimit(100000)

ROOT = Path(__file__).resolve().parent
TOP = ROOT.parent
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
PIN = 'cf4a5218a5a4e4358d3f5314151b6b05d4aa384e'
PRIME = 1000000007
ROW_CACHE = {}


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True)+'\n')


def values_mod():
    out = {}
    for name in PORTS:
        raw = gzip.decompress((TOP/'coefficients/payloads'/(name+'.bin.gz')).read_bytes())
        out[name] = int.from_bytes(raw, 'little') % PRIME
    return out


def exact_degree_certificate(rows, variables):
    """A nonzero residue proves an actual specialized coefficient is nonzero.

    The degree of a sum of real polynomial squares is twice the maximum
    residual degree: highest homogeneous squares cannot cancel.
    """
    degree = max(p.degree(variables) for p in rows)
    variables = set(variables)
    ports = values_mod()
    for index, p in enumerate(rows):
        if p.degree(variables) != degree:
            continue
        grouped = {}
        for m, coefficient in p.terms.items():
            v = tuple((x,e) for x,e in m if x in variables)
            if sum(e for x,e in v) != degree:
                continue
            a = coefficient % PRIME
            for x,e in m:
                if x not in variables:
                    a = a*pow(ports[x], e, PRIME) % PRIME
            grouped[v] = (grouped.get(v,0)+a) % PRIME
        for monomial, residue in sorted(grouped.items()):
            if residue:
                return {'residual_index_zero_based': index,
                        'residual_degree': degree,
                        'monomial': dict(monomial),
                        'prime': PRIME, 'actual_coefficient_mod_prime': residue,
                        'sum_of_squares_exact_degree': 2*degree,
                        'reason': 'nonzero specialized leading coefficient; no cancellation of highest real homogeneous squares'}
    raise ValueError('No specialized leading coefficient certified')


def pack(name, variables, rows, expected_degree, extra=None, definitions=None, formulas=None):
    ROW_CACHE[name] = rows
    live = set().union(*(p.symbols() for p in rows))
    require(live-set(PORTS) == set(variables), name+' variable liveness')
    require(not (live-set(PORTS)-set(variables)), 'undeclared symbol')
    cert = exact_degree_certificate(rows, variables)
    require(cert['sum_of_squares_exact_degree'] == expected_degree, name+' degree')
    packet = {'name': name, 'domain': 'unrestricted integers',
              'variables': variables, 'variable_count': len(variables),
              'fixed_numerals': PORTS, 'residual_count': len(rows),
              'residuals': [p.expression() for p in rows],
              'residual_degrees': [p.degree(variables) for p in rows],
              'exact_degree': expected_degree, 'degree_certificate': cert,
              'single_polynomial': 'sum of the squares of the listed residuals',
              'coefficient_binding': '../coefficients/BINDING.json',
              'comparison_pin': PIN,
              'proof_status': 'ordinary mathematical proof with named inherited native/Pell/calibration theorems; not a new end-to-end proof-assistant certificate'}
    if extra:
        packet.update(extra)
    if definitions is not None:
        packet['polynomial_abbreviations'] = definitions
    if formulas is not None:
        packet['factored_residuals'] = formulas
    dump(ROOT/(name+'.json'),packet)
    dump(TOP/'certificates'/(name+'_degree.json'),cert)
    return packet


def joint_guard(packet):
    variables = [v for v in packet['variables'] if not v.startswith(('eta_zeta_pos','cone_pos'))]
    variables += ['pair_root','pair_pos1','pair_pos2','pair_pos3']
    rows = ROW_CACHE[packet['name']]
    ez = rows[-2]+parse('1+eta_zeta_pos1**2+eta_zeta_pos2**2+eta_zeta_pos3*(eta_zeta_pos3+1)')
    cone = rows[-1]+parse('1+cone_pos1**2+cone_pos2**2+cone_pos3*(cone_pos3+1)')
    pair = cone*ez-(parse('pair_root**2')-cone-ez+1)**2
    pair -= parse('1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)')
    require(not any(x.startswith(('eta_zeta_pos','cone_pos')) for x in pair.symbols()), 'pair removes all six old private witnesses')
    return variables,rows[:-2]+[pair]


def main():
    source = json.loads((TOP/'inherited/orientation70/quartic40.json').read_text())
    direct = json.loads((TOP/'inherited/orientation70/quartic40_direct.json').read_text())
    packets = []
    base = None
    for suffix, original, qtext in [('',source,'beta*(3*J3+1)+1'),('_direct',direct,'beta*J+1')]:
        variables = [v for v in original['variables'] if not v.startswith(('FA_pos','FC_pos'))]
        variables += ['cone_pos1','cone_pos2','cone_pos3']
        q = parse(qtext); F=Poly.symbol('F'); alpha=Poly.symbol('alpha')
        C=q-F-alpha; U=parse('cone_A*F'); VV=parse('cone_B')*C
        cone=U*VV-(q-U-VV)**2-parse('1+cone_pos1**2+cone_pos2**2+cone_pos3*(cone_pos3+1)')
        rows=[parse(s) for s in original['residuals'][:22]]+[parse(original['residuals'][24]),cone]
        p=pack('quartic37'+suffix,variables,rows,4,{'parent':'../inherited/orientation70/'+('quartic40.json' if not suffix else 'quartic40_direct.json'), 'new_semantic_step':'determinant guard and residue orientation have compatible canonical witnesses'})
        require(len(variables)==37 and len(rows)==24, 'quartic dimensions')
        packets.append(p)
        if not suffix: base=p

    q='(beta*(3*J3+1)+1)'; W='(4*(3*w3+1))'
    qP=parse(q); WP=parse(W)
    kP=parse('eta+zeta')
    centered=parse('tau+E*(c-eta)')
    # The six monic projections and one integral change of root from package70.
    subs6={k:parse(v) for k,v in {'P':'eta+zeta+E*(c-eta)', 'N':q+'*(L+1)',
           'X':W+'*'+q,'C2':'c**2','F2':'f**2','g':'y**2-V**2'}.items()}
    subs6['tau']=centered
    all6=[parse(r).substitute(subs6) for r in base['residuals']]
    rows6=[p for p in all6 if p.terms]
    variables6=[v for v in base['variables'] if v not in set(subs6)-{'tau'}]
    p6=pack('sextic31',variables6,rows6,6,{'parent':'quartic37.json','restoration':{k:v.expression() for k,v in subs6.items()},'deleted_row_indices':[i for i,p in enumerate(all6) if not p.terms]})
    require(len(variables6)==31 and len(rows6)==18,'sextic dimensions')
    packets.append(p6)

    def octic_map(vexpr=None, gap=False):
        V=Poly.symbol('V') if vexpr is None else parse(vexpr)
        y=Poly.symbol('y') if not gap else V+Poly.symbol('y_gap')
        k=1-V+parse('c*j+h*E')
        subs={'L':qP**2-1,'N':qP**3,'X':WP*qP,'C2':parse('c**2'),
              'F2':parse('f**2'),'g':y**2-V**2,'Baux':parse('I**2'),
              'D':WP*qP+parse('a*c+(4*a+3)*gamma'),
              'Delta':parse('a**2+4*a+3'),'zeta':k-Poly.symbol('eta'),
              'P':k+parse('E*(c-eta)'), 'tau':centered}
        if vexpr is not None: subs['V']=V
        if gap: subs['y']=y
        return subs

    for label,degree,vexpr,gap in [('octic26',8,None,False),('degree10_25',10,'f*o-c',True)]:
        sub=octic_map(vexpr,gap)
        allrows=[parse(r).substitute(sub) for r in base['residuals']]
        rows=[p for p in allrows if p.terms]
        removed=set(sub)-{'tau','y'}
        vs=[('y_gap' if gap and v=='y' else v) for v in base['variables'] if v not in removed]
        p=pack(label,vs,rows,degree,{'parent':'quartic37.json','restoration':{k:v.expression() for k,v in sub.items()},'deleted_row_indices':[i for i,r in enumerate(allrows) if not r.terms]})
        packets.append(p)
        if label=='degree10_25':
            vs2,rr2=joint_guard(p)
            packets.append(pack('degree12_23',vs2,rr2,12,{'parent':label+'.json','guard_transformation':'package68 nearest-square pairing of determinant and eta*zeta'}))

    # CRT family: one quotient T replaces o and j. The two congruences
    # are recovered by the proved rank lemma, not by a guessed rational map.
    order=['J3','F','alpha','z','f','h','r','v_scale','w3','tau','eta',
           'y_gap','gamma','T','E','c','a','V',
           'eta_zeta_pos1','eta_zeta_pos2','eta_zeta_pos3','cone_pos1','cone_pos2','cone_pos3']
    for stage,expected in [(24,16),(23,26),(22,26),(21,28),(20,44)]:
        definitions=[]; aliases={}
        def define(name,formula):
            aliases[name]=parse(formula,aliases)
            definitions.append([name,formula])
        define('Jnative','3*J3+1'); define('q','beta*Jnative+1')
        define('W','4*(3*w3+1)'); define('C','q-F-alpha')
        define('X','q*W'); define('Y','(2*v_scale+1)*q**3')
        define('R','((q-1)*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*Jnative')
        if stage<=21: define('E','X*Y')
        if stage<=22: define('a','E+Y')
        define('H','4*a+3'); define('Delta','a**2+H')
        define('k','R+1+h*E')
        if stage<=20: define('eta','c-k*Y')
        define('zeta','k-eta'); define('P','k+E*(c-eta)')
        define('D','X+a*c+H*gamma'); define('I','(2*r+1)*c**2')
        define('Vcrt','f*c*T-f**2*R-c')
        if stage<=23: define('V','Vcrt')
        define('G','cone_A*F*cone_B*C-(q-cone_A*F-cone_B*C)**2')
        equations=[]
        if stage>=24: equations.append('V-Vcrt')
        if stage>=23: equations.append('a-E-Y')
        if stage>=22: equations.append('E*(X+1)-X*a' if stage>=23 else 'E-X*Y')
        if stage>=21: equations.append('c-k*(a-E)-eta' if stage>=23 else 'c-k*Y-eta')
        equations.append('tau**2+2*tau*(2*P-k)+k**2-4' if stage==20 else 'tau**2+(2*tau-k)*E*(c-eta)-1')
        equations += ['D**2-Delta*c**2-1','I**2-Delta*(f**2-1)',
                      'V**2+(1-I**2)*y_gap*(2*V+y_gap)-1',
                      '(K0+W)*C-F-z*(q-1)',
                      'eta*zeta-1-eta_zeta_pos1**2-eta_zeta_pos2**2-eta_zeta_pos3*(eta_zeta_pos3+1)',
                      'G-1-cone_pos1**2-cone_pos2**2-cone_pos3*(cone_pos3+1)']
        rows=[parse(s,aliases) for s in equations]
        vs=[v for v in order if v not in aliases]
        require(len(vs)==stage,'CRT variable count')
        p=pack('crt_degree'+str(expected)+'_'+str(stage),vs,rows,expected,
               {'new_semantic_step':'CRT quotient compression after preliminary strong-rank recovery',
                'root_change':'tau_old=(tau+2*P-k)/2; parity follows from first residual modulo4' if stage==20 else 'tau_old=tau+E*(c-eta)',
                'auxiliary_root_change':'y_old=V+y_gap'},definitions,equations)
        packets.append(p)
        # The paired degree-88 endpoint is emitted compactly, after the
        # transport projection, by transport/build_transport.py. Expanding
        # its shared guard here would add cost without improving the proof.
        if stage in (24,22,21):
            deg={24:20,22:26,21:32,20:88}[stage]
            vsp,rp=joint_guard(p)
            pairdefs=definitions+[['Zeta','eta*zeta']]
            pairform=equations[:-2]+['G*Zeta-(pair_root**2-G-Zeta+1)**2-1-pair_pos1**2-pair_pos2**2-pair_pos3*(pair_pos3+1)']
            packets.append(pack('degree'+str(deg)+'_'+str(stage-2),vsp,rp,deg,
                           {'parent':p['name']+'.json','guard_transformation':'package68 nearest-square pairing'},pairdefs,pairform))

    # Universal polynomial certificates for the three new transformations.
    a={n:Poly.symbol(n) for n in ['f','c','T','R','V','o','j','k','P','tau','y_gap','I']}
    crt=a['f']*a['c']*a['T']-a['f']**2*a['R']-a['c']
    require(crt+a['c']-a['f']*(a['c']*a['T']-a['f']*a['R'])==0,'first CRT congruence identity')
    require(crt+a['R']-(a['c']*(a['f']*a['T']-1)-(a['f']**2-1)*a['R'])==0,'second CRT congruence identity')
    centered_aux=a['V']**2+(1-a['I']**2)*a['y_gap']*(2*a['V']+a['y_gap'])-1
    old_aux=a['I']**2*a['V']**2-(a['I']**2-1)*(a['V']+a['y_gap'])**2-1
    require(centered_aux==old_aux,'centered auxiliary identity')
    # Avoid fractions: first expression is four times the old norm.
    half=(a['tau']+2*a['P']-a['k'])**2-4*a['P']**2+4*a['P']*a['k']-4
    target=a['tau']**2+2*a['tau']*(2*a['P']-a['k'])+a['k']**2-4
    require(half==target,'half-centered root exact identity')
    require((target-(a['tau']-a['k'])**2).terms==parse('4*tau*P-4').terms,'half-centered parity certificate')
    summary={p['name']:{'variables':p['variable_count'],'residuals':p['residual_count'],'degree':p['exact_degree'],
                        'expanded_residual_terms':sum(len(r.terms) for r in ROW_CACHE[p['name']])} for p in packets}
    dump(TOP/'certificates/INTEGER_CHECKS.json',{'status':'PASS','equations':summary,
         'universal_identities':['two CRT reconstruction identities','centered auxiliary norm','half-centered first norm','parity-forcing difference'],
         'scope':'exact algebra, specialized leading coefficients and literal dimensions; semantic rank and compiler arguments are in report and inherited sources'})
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
