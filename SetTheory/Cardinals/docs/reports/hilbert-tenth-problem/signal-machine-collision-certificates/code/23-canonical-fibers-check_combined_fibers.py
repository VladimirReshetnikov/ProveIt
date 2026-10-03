"""Independent data-only bridge: canonical circuits retain the infinite native fiber.

This checker executes no inherited code. Finite symbolic and dependency checks
support, but do not replace, the two proofs. No positive native seed is computed.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
from hashlib import sha256
import argparse
import copy
import json

ROOT = Path(__file__).resolve().parent
INPUT_PIN = 'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e'
ORDER = ['native__'+x for x in ('F0','F1','F2','a','c','d','f','h','i','j','k','o','r','s','w','tau','eta','zeta','ga','y_aux','odd_half','bound_beta')]
CHANGED = {'native__j','native__o','native__y_aux'}
FIXED = [x for x in ORDER if x not in CHANGED]
FIXTURES = ('incdec','zero3','nop','positive3')
MODES = ('native','phase4')
DESCENDANTS = ['native__of','native__aux_u_rhs','native__jc','native__H17','native__H2','native__aux_y2','native__aux_square_gap','native__L17','native__P17']


def require(value, message):
    if not value:
        raise ValueError(message)


def jload(path):
    def unique(pairs):
        out={}
        for key,value in pairs:
            require(key not in out,'duplicate JSON key: '+key)
            out[key]=value
        return out
    return json.loads(Path(path).read_bytes(),object_pairs_hook=unique)


# Sparse integral polynomial arithmetic, with canonical sorted variable multisets.
def add(a,b,scale=1):
    out=dict(a)
    for monomial,coefficient in b.items():
        out[monomial]=out.get(monomial,0)+scale*coefficient
        if not out[monomial]: del out[monomial]
    return out


def mul(a,b):
    out={}
    for ma,ca in a.items():
        for mb,cb in b.items():
            key=tuple(sorted(ma+mb))
            out[key]=out.get(key,0)+ca*cb
    return {m:c for m,c in out.items() if c}


def polynomial_of(name, rows, supplied, memo):
    if type(name) is int:return {():name} if name else {}
    if name in supplied:return {(name,):1}
    if name not in memo:
        require(name in rows,'unbound symbolic gate: '+name)
        _,op,a,b=rows[name]
        aa=polynomial_of(a,rows,supplied,memo);bb=polynomial_of(b,rows,supplied,memo)
        require(op in ('+','-','*'),'invalid arithmetic operation')
        memo[name]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
    return memo[name]


def inspect(packet, inherited):
    require(packet['parameters']==['x','Tclean'],'natural ports changed')
    coordinates=packet['auxiliaries']
    native=[x for x in coordinates if x.startswith('native__')]
    require(native==ORDER,'fixed 22-coordinate native order changed')
    require(len(set(coordinates))==len(coordinates),'duplicate witness coordinate')
    require(len(FIXED)==19 and len(CHANGED)==3,'19+3 native split')
    rows=[g for g in packet['source'] if g[0].startswith('native__')]
    original=[g for g in inherited['source'] if g[0].startswith('native__')]
    require(len(rows)==64 and rows==original,'literal 64 native gates changed')
    comparisons=packet['comparisons']
    require(len(comparisons)==21,'complete canonical comparison list required')
    require(comparisons[2:18]==inherited['comparisons'][2:18],'native comparison order changed')
    require(comparisons[14:16]==[['native__L17','native__P17'],['native__H17','native__aux_u_rhs']],'native norm/congruence rows moved')
    dependencies={name:{name} for name in coordinates+packet['parameters']}
    seen=set(dependencies)
    for name,op,a,b in packet['source']:
        require(name not in seen,'duplicate arithmetic gate')
        require(op in ('+','-','*'),'unknown operation')
        require(all(type(v) is int or v in seen for v in (a,b)),'forward/unbound reference')
        dependencies[name]=dependencies.get(a,set())|dependencies.get(b,set())
        seen.add(name)
    affected=[i+1 for i,(a,b) in enumerate(comparisons) if (dependencies.get(a,set())|dependencies.get(b,set()))&CHANGED]
    require(affected==[15,16],'changed native coordinates escape their two comparisons')
    descendants=[g[0] for g in rows if dependencies[g[0]]&CHANGED]
    require(descendants==DESCENDANTS,'native descendant order changed')
    outer_coordinates=[x for x in coordinates if x not in ORDER]
    ports=['native__q','native__padded_A','native__padded_B','native__F3']
    require(all(not (dependencies[x]&set(ORDER)) for x in ports),'native ports or scale depend on native witnesses')
    height=packet['canonical_height']
    require(height['constraint']=='eta+kappa=S+1' and height['native_positive_coordinate_count']==22,'canonical-height interface changed')
    require('canonical_height_slack' in outer_coordinates,'missing positive canonical-height slack')
    require(all(not ((dependencies.get(a,set())|dependencies.get(b,set()))&set(ORDER)) for a,b in (comparisons[0],comparisons[1],comparisons[18],comparisons[19],comparisons[20])),'an outer comparison uses native coordinates')
    # Exact symbolic checks of the two changed residuals and fixed norm.
    byname={g[0]:g for g in rows};memo={};supplied=set(coordinates+packet['parameters'])
    def poly(n):return polynomial_of(n,byname,supplied,memo)
    def v(n):return {(('native__'+n),):1}
    one={():1};p=add(mul({():2},v('r')),one)
    U=add(mul(v('j'),v('c')),p,-1)
    R=mul(v('i'),mul(v('c'),v('c')))
    Y=v('y_aux')
    norm=add(mul(mul(R,R),add(mul(U,U),mul(Y,Y),-1)),add(one,mul(Y,Y),-1),-1)
    congruence=add(U,add(mul(v('o'),v('f')),v('c'),-1),-1)
    require(add(poly('native__L17'),poly('native__P17'),-1)==norm,'norm polynomial differs')
    require(add(poly('native__H17'),poly('native__aux_u_rhs'),-1)==congruence,'congruence polynomial differs')
    fixed_norm=add(mul(R,R),mul(add(add(mul(v('a'),v('a')),mul({():4},v('a'))),{():3}),add(mul(v('f'),v('f')),one,-1)),-1)
    require(add(poly('native__ic22'),poly('native__R16'),-1)==fixed_norm,'fixed norm polynomial differs')
    # Source identities used for U>0 and R>=2 in the proof.
    expected={
      'native__bs_odd':['+', 'native__bs_even',1],
      'native__bs_even':['*',2,'native__odd_half'],
      'native__R11':['+','native__r1','native__hpm1'],
      'native__r1':['+','native__r',1],
      'native__hpm1':['*','native__h','native__UM'],
      'native__R10a':['+','native__ksn2','native__eta'],
      'native__ksn2':['*','native__k','native__sn2'],
      'native__sn2':['*','native__s','native__q'],
      'native__wn2':['*','native__w','native__q'],
      'native__UM':['*','native__wn2','native__sn2'],
    }
    require(all(byname[name][1:]==value for name,value in expected.items()),'positivity-chain gate changed')
    require(comparisons[4]==['native__s','native__bs_odd'] and comparisons[7]==['native__c','native__R10a'] and comparisons[9]==['native__k','native__R11'],'positivity-chain comparison changed')
    require(byname['native__q'][1:3]==['*',16],'prescribed scale padding changed')
    return {'native_gates':64,'native_coordinates':22,'fixed_native_coordinates':19,'outer_coordinates':len(outer_coordinates),'affected_native_comparisons_one_based':[13,14],'affected_complete_comparisons_one_based':affected,'all_outer_comparisons_independent_of_native_witnesses':True,'all_64_native_gates_and_16_native_comparisons_byte_structurally_equal_to_inherited_receipt':True,'symbolic_changed_residuals_and_fixed_norm':'exact integer polynomial identities','strict_positivity_source_chain':'q>=16; s>=3; k>r+1; c>48(r+1)>2r+1; U>0; R>=2'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expect',type=Path)
    args=parser.parse_args()
    path=ROOT/'inherited-source/three_mass_unbounded_interface.json'
    require(sha256(path.read_bytes()).hexdigest()==INPUT_PIN,'inherited JSON pin mismatch')
    inherited={f['name']:f for f in jload(path)['fixtures']}
    require(set(inherited)==set(FIXTURES),'inherited fixture inventory')
    results={};sample=None
    for fixture in FIXTURES:
        for mode in MODES:
            key=fixture+'-'+mode
            packet=jload(ROOT/'canonical-height/circuits'/(key+'-canonical.json'))
            results[key]=inspect(packet,inherited[fixture])
            if sample is None:sample=packet
    attacks=[]
    def reject(label,mutation):
        packet=copy.deepcopy(sample);mutation(packet)
        try:inspect(packet,inherited['incdec'])
        except (ValueError,KeyError,IndexError):attacks.append(label);return
        raise RuntimeError('corruption accepted: '+label)
    def wrong_order(d):
        a=d['auxiliaries'];i=a.index('native__j');j=a.index('native__o');a[i],a[j]=a[j],a[i]
    reject('native-coordinate-order',wrong_order)
    reject('native-gate-operand',lambda d:next(g for g in d['source'] if g[0]=='native__H17').__setitem__(3,'native__c'))
    reject('native-comparison-order',lambda d:d['comparisons'].__setitem__(14,['native__H17','native__aux_u_rhs']))
    reject('outer-comparison-native-dependency',lambda d:d['comparisons'].__setitem__(20,['native__j','canonical_sum_plus_one']))
    reject('missing-canonical-height-coordinate',lambda d:d['auxiliaries'].remove('canonical_height_slack'))
    # Formal norm-preservation identity in independent indeterminates R,D,V,Y,
    # reduced using D=R^2-1 via polynomial substitution.
    rr={('R',):1};vv={('V',):1};yy={('Y',):1};dd=add(mul(rr,rr),{():1},-1)
    vp=add(mul(rr,vv),mul(dd,yy));yp=add(vv,mul(rr,yy))
    require(add(mul(vp,vp),mul(dd,mul(yp,yp)),-1)==add(mul(vv,vv),mul(dd,mul(yy,yy)),-1),'universal matrix norm identity')
    report={'schema':'report22-combined-fiber-checks-v1','status':'passed','inherited_receipt_sha256':INPUT_PIN,'native_coordinate_order':ORDER,'changed_coordinates_in_order':[x for x in ORDER if x in CHANGED],'fixed_coordinates_in_order':FIXED,'canonical_circuits':results,'symbolic_matrix_identity':'verified as an integer polynomial identity for arbitrary R,V,Y with D=R^2-1','rejected_corruptions':attacks,'conclusion_scope':'At fixed input ports, accepted nonempty fibers have one outer tuple and infinitely many full positive tuples by composing the canonical-height and native-fiber theorems. The family varies j,o,y_aux and fixes the other 19 native supplied coordinates.','evidence_boundary':'No full positive native Pell tuple is materialized. The local numeric recurrence is auxiliary-only. Finite checks do not replace the unbounded proof; zero-step circuits are excluded.'}
    if args.expect:require(report==jload(args.expect),'combined receipt differs')
    print(json.dumps(report,indent=2,sort_keys=True))

if __name__=='__main__':main()
