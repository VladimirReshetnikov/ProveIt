#!/usr/bin/env python3
"""Pinned finite review and private repair replay for three spectral archives.

Accept extracted original package roots; do not modify them. All mutation,
exports, author scripts and unified-patch application run in temporary copies.
This is a bounded executable audit, not a proof of the infinitary theorems.
"""
from __future__ import annotations
import argparse, contextlib, copy, hashlib, importlib, itertools, json
import random, shutil, subprocess, sys, tempfile
from fractions import Fraction
from pathlib import Path

# Pins are inserted from the inspected immutable archives, not learned at replay.
PINS = {'positive': {'archive_sha256': 'fe519471be068a0f7f5822c2fd89f1767f15d60379fb8d06d4b7b87f994dfdf8', 'members': [{'path': 'Makefile', 'size': 653, 'sha256': '98a5b403b3c8f1b5a7a20d307eb75c50d5b5ebfcfd99501bd9de20726efd9b96'}, {'path': 'README.md', 'size': 5465, 'sha256': 'c73b8f4fc3efb1514a03ca811c0e0bf29f7de148957b62f115fc5117014750b0'}, {'path': 'SOURCE_AUDIT.md', 'size': 4742, 'sha256': '25a40edbd58b66c0c09f59b536ded852d3e561f8d2e364f5797ac6f9c9b50aed'}, {'path': 'article.pdf', 'size': 353152, 'sha256': '7adce8c50aaa4d4acb202c773dd34537ec45f9d451e1767a2d963166d7600fbf'}, {'path': 'article.tex', 'size': 85627, 'sha256': 'ffe039f42d006c97010b0ce626b67c8cd377225b3112f6311e9d95be7c9a19ba'}, {'path': 'code/check_export.py', 'size': 1690, 'sha256': '39694db63a5a3a39cc3be05578e8cd981efdc6ac793bdd8db4526483b89cf892'}, {'path': 'code/compiler.py', 'size': 11375, 'sha256': '3732b6f777083fb1d1014f98c204a87b80d4bcbfe1694a6b7f888938fb3ab394'}, {'path': 'code/profiles.py', 'size': 8354, 'sha256': '396102c3ddffa04df678f2face341c5c95f4f7fb7ee46c9ca8a33bd1a0603299'}, {'path': 'code/test_applications.py', 'size': 2646, 'sha256': 'e8e29e72bdd2007ced07789dab380582d83fa408c87998521c1dece582594883'}, {'path': 'code/test_profiles.py', 'size': 5610, 'sha256': '5060ff98ee15ac0de5bd896c057705d96fdab5f51645cdc53836951ed438f697'}, {'path': 'data/application_checks.json', 'size': 349, 'sha256': '576dad296728783030500056f35208031e5789ae99c1b579e8adb48cb3aad541'}, {'path': 'data/compiler_summary.json', 'size': 543, 'sha256': '93b4cf47c570bfd2a909225e8799b0c4ff675f560e47300584f387a6c13a2552'}, {'path': 'data/export_check_log.txt', 'size': 196, 'sha256': '10193e29d90c8161c527065824de16dbdf30c5436961a9cc17409bb8f7076640'}, {'path': 'data/finite_certificate.json', 'size': 252673, 'sha256': '459c4f5b79fef7898d7b166b32a8824201f53d27c0b35c1e8926c95baa808cb3'}, {'path': 'data/infinite_certificate.json', 'size': 272756, 'sha256': '51fe83d93ae4d5fe11ac4692115979d051914ed7a5ebcc59d637462bf699e4c0'}, {'path': 'data/test_log.txt', 'size': 2014, 'sha256': 'ff1940ca518a4752a092d7ceb1c01b7bd8f0055b73475c414dea6ddd82d241c8'}, {'path': 'data/test_results.json', 'size': 2014, 'sha256': 'ff1940ca518a4752a092d7ceb1c01b7bd8f0055b73475c414dea6ddd82d241c8'}]}, 'spectral': {'archive_sha256': '0a5cf2d12333bab718453e1139622518f55b6361bd0e947f47d8e748d06f9e53', 'members': [{'path': 'Makefile', 'size': 429, 'sha256': '935f3d936b43859bd73ef8e313eabfd36756e1ba0d5f58f0e798a151664d2456'}, {'path': 'README.md', 'size': 6760, 'sha256': '822c4d97e0ed888067f8b897c33ea0c4320c3b89fbf86d320a5ae8e07a511cd1'}, {'path': 'SHA256SUMS.txt', 'size': 1823, 'sha256': '90da60d6ced582bf921efbaa46bd5cd4ef2951b6230695618a7716dfa63ca751'}, {'path': 'SOURCES.md', 'size': 5051, 'sha256': 'fa278bf035e633ea579568659ab27491c9edb2d3b264d369055694d18cafd798'}, {'path': 'article.pdf', 'size': 500145, 'sha256': '4d22870364ff5ed213742d56b3adbb3395a8b3c115116cf176357eb59ebc791a'}, {'path': 'article.tex', 'size': 68799, 'sha256': '66800a6a5bc739300d263fa14481e45fc250327c8418b5d179e439be09ed4c37'}, {'path': 'code/quartic_compiler.py', 'size': 12462, 'sha256': '4e0da2d462f577771988cf07db245c1249587b90571907adf6ccba413c35c1e2'}, {'path': 'code/run_tests.py', 'size': 6828, 'sha256': '5239d2d54af50834093be552469b0ad2b54337039ae5f95c3a030789164de109'}, {'path': 'code/spectral_guards.py', 'size': 9463, 'sha256': '59c94e2809efb89398610729675a30cfc18858402f7db9b810fcf47a44904991'}, {'path': 'code/supplementary_checks.py', 'size': 2251, 'sha256': 'a4707ef2b54b02104579401685e73d5dfb4f742f7a6f644b49add34946c83917'}, {'path': 'examples/discrete_not_continuous.json', 'size': 796, 'sha256': '901a9b423832656de16edd79e1f6f9aa8e9e42d24857ddb18f3836991ff6f283'}, {'path': 'examples/hidden_negative.json', 'size': 846, 'sha256': '2d1629c3fc6bc93c6d308454fd35fe5e1c0a386ef3bbdc6d8bb542c170e0d519'}, {'path': 'examples/hidden_negative_quartic.json', 'size': 483010, 'sha256': '783ea7b4d52f2fa5d9deb7bd2f1594825c53a8a8d655272d2d13b7cccf609db8'}, {'path': 'examples/hidden_negative_quasi.json', 'size': 310426, 'sha256': 'e6e60aabe4a743709eea63242c870eaf03d4d2bcf410de6a4049c4eb74a8bd7d'}, {'path': 'examples/identically_zero.json', 'size': 402, 'sha256': '9c7344723890ae2aa08e0fbd1163a3f19d2efc2d59166a52d56217259037adde'}, {'path': 'examples/jordan_block.json', 'size': 774, 'sha256': '38e2152c2552ae54a0758d17fb138afb18e281abe7b08903b559f032c5956f67'}, {'path': 'examples/million_step_chart.json', 'size': 1382, 'sha256': '4804cd94842425cdd3accdfe9ee21a06df26410b4de341f49328250f9b956a74'}, {'path': 'validation/artifact_checks.json', 'size': 399, 'sha256': 'c7deeec1ebfd60f64c5b7fbee680e29128808e668acecc9a9891a9dd8ed550a8'}, {'path': 'validation/results.json', 'size': 3499, 'sha256': 'a432f148d8a9ef5bf3a4a5be6aece09a24a415daa179513b11fa4bc6d7f293b5'}, {'path': 'validation/supplementary_checks.json', 'size': 247, 'sha256': 'fe9329f04794406860c933cf36d4c707177c15e0137fa7dde188004ebf6cf351'}, {'path': 'validation/test_output.txt', 'size': 3499, 'sha256': 'a432f148d8a9ef5bf3a4a5be6aece09a24a415daa179513b11fa4bc6d7f293b5'}]}, 'clock': {'archive_sha256': 'dbbcc5ed44b2a1b87da14ab863c32a5b125484480652fa9a04c5e0340082fb22', 'members': [{'path': 'article.tex', 'size': 72235, 'sha256': '1e64f8c086e1c3f46287a0ee4839db5fffd6ab4334aaa0558982292943808d56'}, {'path': 'article.pdf', 'size': 312251, 'sha256': '1ab2a90b46520a6c77b918b8a7c3c03b62756982d2ae84e8d1123853d63b96cb'}, {'path': 'README.md', 'size': 4427, 'sha256': '96695781aed07fbded0913016b2419aaff9ab2342e8a6889bbe284e1cd1f8422'}, {'path': 'source_audit.md', 'size': 4306, 'sha256': '5fcd26246e19f47561ba8d296f463d7cdd88ea6b0b6601e6ee953ca5ef4847ed'}, {'path': 'test_results.json', 'size': 757, 'sha256': '88a554cf8e5f8afc81f4ddf03a64805451b5388d81589673bff4282f33055dbd'}, {'path': 'build.sh', 'size': 447, 'sha256': 'c8473b110702410907837f82338eab64a19c4e5c47bce93aa8945b614779278b'}, {'path': 'code/clock_certificates.py', 'size': 12329, 'sha256': '79033b477a6d03f2f6c615539bfd123aa9b51e61f4d8c719b283cfd1ae9d3e24'}, {'path': 'code/test_all.py', 'size': 6737, 'sha256': '31c6e07b52d7ab50e40ba42098fe1a1151e5e7b0e7cae3473421f8a80a930cf2'}, {'path': 'code/verify_export.py', 'size': 2588, 'sha256': '678e2a0cdf51ffd29ad53693c1e5fcc2365eadf084136d8880667e4da2a82bd7'}, {'path': 'examples/quadratic_certificate.json', 'size': 157768, 'sha256': '4f3d9e0444a4eaea3681d00b2c4db32fa580659da8c70556707ea72bc5c73390'}]}}
REPAIRS = {'positive': {'code/profiles.py': {'old': '396102c3ddffa04df678f2face341c5c95f4f7fb7ee46c9ca8a33bd1a0603299', 'new': '081b560fbf0d0926abdd0f57625c1252230cc9aac1fde261ef7f5164ea913080'}, 'code/check_export.py': {'old': '39694db63a5a3a39cc3be05578e8cd981efdc6ac793bdd8db4526483b89cf892', 'new': '476305b5bb8550d8ca7818ebdf2e5343349d1494cffa9a8373c9362b6605281f'}, 'patch_sha256': 'b4050e7a365c48dac78de4880a02ee239f82e94853d767f5788368db9281dab0'}, 'spectral': {'code/quartic_compiler.py': {'old': '4e0da2d462f577771988cf07db245c1249587b90571907adf6ccba413c35c1e2', 'new': '09d1f53adf288b0aa06cab13e1d0d240bba0729c5738432cda7da956a13c5f17'}, 'patch_sha256': '9df417dae9bdbb10c2847e24b9d199451ff6d5d679dbbffa1a001270ffe68315'}, 'clock': {'code/clock_certificates.py': {'old': '79033b477a6d03f2f6c615539bfd123aa9b51e61f4d8c719b283cfd1ae9d3e24', 'new': '1f08f068a89145bbbb45e972269cb26c96d0999029ac899e7cbe051acbd0785d'}, 'patch_sha256': 'acd02f6a554d6748a4de8cf3ee34e2b434425b1a836d98be2d7c02f1a7d2a141'}}
COMMANDS = {
 'positive': [['code/profiles.py'], ['code/test_profiles.py'], ['code/test_applications.py'], ['code/compiler.py'], ['code/check_export.py','data/finite_certificate.json','data/infinite_certificate.json']],
 'spectral': [['code/run_tests.py'], ['code/supplementary_checks.py']],
 'clock': [['code/test_all.py'], ['code/verify_export.py','examples/quadratic_certificate.json']]}
MODULES = {'positive':('profiles','compiler','check_export'), 'spectral':('spectral_guards','quartic_compiler'), 'clock':('clock_certificates','verify_export')}

def need(ok, message):
    if not ok: raise AssertionError(message)

def digest(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def json_digest(value): return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def normalized(key, rel, value):
    # Remove only known runtime metadata at their exact original paths.
    value = copy.deepcopy(value)
    if key == 'positive' and rel == 'data/test_results.json': value.pop('elapsed_seconds',None)
    if key == 'clock' and rel == 'test_results.json': value.pop('python',None)
    return value

@contextlib.contextmanager
def modules(key, root):
    stems=set(MODULES[key])|{p.stem for p in (root/'code').glob('*.py')}
    old={n:sys.modules[n] for n in stems if n in sys.modules}; paths=sys.path[:]
    try:
        for n in stems:sys.modules.pop(n,None)
        sys.path.insert(0,str(root/'code'))
        yield tuple(importlib.import_module(n) for n in MODULES[key])
    finally:
        for n in stems:sys.modules.pop(n,None)
        sys.modules.update(old);sys.path[:]=paths

def rejected(call):
    try: answer=call()
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,AssertionError): return True
    return answer is False

def eval_terms(rows, v):
    total=0
    for c, mon in rows:
        for i in mon:c*=v[i]
        total+=c
    return total

def sparse(rows):
    out={}
    for c,m in rows:
        t=tuple(sorted(m));out[t]=out.get(t,0)+c
    return {m:c for m,c in out.items() if c}

def exact_sos(rows):
    out={}
    for row in rows:
        p=sparse(row)
        for m,c in p.items():
            for n,d in p.items():
                t=tuple(sorted(m+n));out[t]=out.get(t,0)+c*d
    return {m:c for m,c in out.items() if c}

def serial(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]

def write_json(path,data):path.write_text(json.dumps(data,indent=2)+'\n')

def original_findings(roots,work):
    result={}
    with modules('positive',roots['positive']) as (p,compiler,checker):
        f=p.ExpPoly({1:[64],2:[-20],4:[1]})
        bogus=[[p.Run(0,6,1)],[p.Run(0,6,0)]]
        need(p.verify_profiles([f,p.ExpPoly({})],bogus,6),'Expected unauthenticated-chain regression')
        need(f.value(3)==-32,'Interior violation')
        result['unauthenticated_chain']={'accepted':True,'claimed_sign':1,'f3':-32}
        f=p.ExpPoly({1:[1]});chain,_=p.make_chain(f,{1:0});prof=p.build_profiles(chain,4)
        need(p.verify_profiles(chain,prof,4),'Original valid constant profile')
        f.terms[1]=(-1,)
        need(p.verify_profiles(chain,prof,4) and f.value(0)==1 and f.value(2)==-1,'Expected stale cached coefficient regression')
        result['mutable_cached_terms']={'accepted_old_profile':True,'cached0':1,'uncached2':-1}
        d=json.loads((roots['positive']/'data/finite_certificate.json').read_text())
        original=sparse(d['expanded_quartic']);a=d['sample_assignment'][0];b=3
        q=copy.deepcopy(original)
        for m,c in {(0,0):1,(0,):-a-b,():a*b}.items():q[m]=q.get(m,0)+c
        d['expanded_quartic']=serial(q);path=work/'forged_positive.json';write_json(path,d)
        with contextlib.redirect_stdout(__import__('io').StringIO()):checker.check(path)
        v=[0]*len(d['sample_assignment']);v[0]=65
        gap=eval_terms(d['expanded_quartic'],v)-sum(eval_terms(r,v)**2 for r in d['quadratic_residuals'])
        need(gap==62 and sparse(d['expanded_quartic'])!=exact_sos(d['quadratic_residuals']),'Expected false expansion')
        result['two_point_expansion']={'accepted':True,'perturbation':'(x0-64)*(x0-3)','independent_gap':gap}
    with modules('clock',roots['clock']) as (c,checker):
        rules=[c.Rule(0,0)];initial=[0,0,0];accepting=set()
        machine=c.Machine(rules,initial,accepting);cert=c.compile_certificate(machine,1);v=cert.canonical([0])
        rules[0]=c.Rule(7,7);initial[0]=7
        need(cert.validate(v) and machine.initial[0]==7 and v['q_0']==0,'Expected mutable machine snapshot regression')
        result['mutable_machine']={'accepted_old_zero':True,'export_initial_state':7,'zero_initial_state':0}
        need(c.encode_stack([0.0])==1.0,'Expected exact stack-bit boundary')
    with modules('spectral',roots['spectral']) as (s,q):
        d=json.loads((roots['spectral']/'examples/hidden_negative_quartic.json').read_text())
        for kind in ('boolean_value','float_coefficient','negative_index'):
            bad=copy.deepcopy(d)
            if kind=='boolean_value':
                i=next(i for i,v in enumerate(bad['values']) if v==0);bad['values'][i]=False
            elif kind=='float_coefficient':bad['residuals'][0][0][0]=float(bad['residuals'][0][0][0])
            else:
                row=next(t for row in bad['residuals'] for t in row if t[1]);row[1][0]-=len(bad['values'])
            path=work/(kind+'.json');write_json(path,bad);need(q.verify_export(path),'Expected spectral exact-schema regression '+kind)
        need(q.Emitter(True).bits is True,'Expected Boolean bit-width regression')
        result['spectral_exact_schema']={'accepted':['boolean_value','float_coefficient','negative_index','boolean_bit_width']}
    return result

def sequence_checks(roots):
    rng=random.Random(606008);out={}
    with modules('positive',roots['positive']) as (p,pc,chk):
      with modules('spectral',roots['spectral']) as (s,sc):
        comparisons=0;coeffchecks=0;tailchecks=0
        for z in range(180):
            bases=sorted(rng.sample(range(1,5),rng.randint(1,3)))
            terms={b:[rng.randint(-3,3) for _ in range(rng.randint(1,3))] for b in bases}
            shape={b:len(v)-1 for b,v in terms.items()}
            f=p.ExpPoly(terms);chain,aa=p.make_chain(f,shape);T=z%18
            seq=s.Sequence(tuple(s.Mode(b,tuple(v)) for b,v in terms.items()))
            cert=s.build_certificate(seq,T);need(s.verify_certificate(cert),'Spectral chart verification')
            prof=p.build_profiles(chain,T);inf=p.build_profiles(chain,None)
            need(p.verify_profiles(chain,prof,T) and p.verify_profiles(chain,inf,None),'Positive finite/infinite profiles')
            for j,g in enumerate(chain):
                expected=[]
                for n in range(T+1):
                    value=sum(sum(c*n**k for k,c in enumerate(cs))*b**n for b,cs in g.terms.items())
                    sign=(value>0)-(value<0)
                    if expected and expected[-1][2]==sign:expected[-1][1]=n
                    else:expected.append([n,n,sign])
                need([[r.lo,r.hi,r.sign] for r in prof[j]]==expected,'Literal positive chart')
                need([[r.lo,r.hi,r.sign] for r in p.restrict_profile(inf[j],T)]==expected,'Infinite restriction')
                if j==0:need(cert['charts'][0]==expected,'Cross-implementation chart')
                comparisons+=1
                if j<len(aa):
                    for n in range(4):need(chain[j+1].value(n)==g.value(n+1)-aa[j]*g.value(n),'Literal E-a recurrence');coeffchecks+=1
            threshold,tail=s.tail_threshold(seq)
            # Finite samples supplement the independently read infinite dominance proof.
            if threshold<20000:
                for n in (threshold,threshold+1,threshold+7):
                    value=seq.value(n);need((value>0)-(value<0)==tail,'Tail fixture');tailchecks+=1
        out={'sequence_instances':180,'finite_and_infinite_chain_rows':comparisons,'annihilator_value_identities':coeffchecks,'permanent_tail_samples':tailchecks}
        compiled=0
        for coeffs,T in [((1,-2),0),((0,0),1),((-1,2),4),((3,-3),6),((10,-1),7),((-4,4),3)]:
            seq=s.Sequence((s.Mode(1,(coeffs[0],)),s.Mode(2,(coeffs[1],))))
            cert=s.build_certificate(seq,T)
            for bits in (None,3,4):
                emitted=sc.compile_certificate(cert,bits)
                need(not emitted.failed_residuals(),'New compiler fixture residuals')
                need(len(emitted.power_atoms)==0 if bits else len(emitted.power_atoms)>0,'Power-mode separation')
                compiled+=1
        out['additional_spectral_compilers']=compiled
    return out

def stack_step(op,old,new):
    if op=='stay':return new-old
    if op=='empty':return old+new
    bit=int(op[-1])
    return new-2*old-bit-1 if op.startswith('push') else old-2*new-bit-1

def literal_quadratic(machine,T,deadlines,v):
    result=sum((v[f'{name}_0']-x)**2 for name,x in zip(('q','u','v'),machine.initial))
    for t in range(T):
        result+=(sum(v[f's_{t}_{r}'] for r in range(len(machine.rules)))-1)**2
        for r,rule in enumerate(machine.rules):
            ds=(v[f'q_{t}']-rule.source,v[f'q_{t+1}']-rule.target,stack_step(rule.left,v[f'u_{t}'],v[f'u_{t+1}']),stack_step(rule.right,v[f'v_{t}'],v[f'v_{t+1}']))
            for j,d in enumerate(ds):
                a,b,s=v[f'a_{t}_{r}_{j}'],v[f'b_{t}_{r}_{j}'],v[f's_{t}_{r}']
                result+=(d-a+b)**2+a*b+s*(a+b)
    for i,deadline in enumerate(deadlines,1):
        ticks=sum(v[f's_{t}_{r}'] for t in range(deadline) for r,rule in enumerate(machine.rules) if rule.target in machine.accepting)
        result+=(ticks-i-v[f'z_{i}'])**2
    return result

def clock_checks(root):
    rng=random.Random(20261004);comparisons=0;zeros=0;wrong=0;gadgets=0
    with modules('clock',root) as (c,checker):
        for D,s,a,b in itertools.product(range(-5,6),range(3),range(7),range(7)):
            F=(D-a+b)**2+a*b+s*(a+b)
            need((F==0)==(a==max(D,0) and b==max(-D,0) and (s==0 or D==0)),'Natural guard iff');gadgets+=1
        signed=(1,1,1,-1);need((1-1-1)**2-1+1*(1-1)==0,'Signed guard counterexample')
        machines=[c.Machine((c.Rule(0,0),c.Rule(0,0,'push1')), (0,0,0), frozenset({0})),c.example_machine(),c.Machine((),(3,1,2),frozenset())]
        for machine in machines:
          for T in range(4):
            ds=(T,)*min(T,2)
            cert=c.compile_certificate(machine,T,ds)
            need(len(cert.variables)==3*(T+1)+9*len(machine.rules)*T+len(ds),'Clock charged variable formula')
            for z in range(24):
                v={n:rng.randint(-3,4) if z%2 else rng.randint(0,4) for n in cert.variables}
                need(cert.polynomial.evaluate(v)==literal_quadratic(machine,T,ds,v),'Complete off-zero quadratic identity');comparisons+=1
        machine=machines[0]
        for T in range(4):
          for labels in itertools.product(range(2),repeat=T):
            for deadlines in itertools.product(range(T+1),repeat=min(T,2)):
                cert=c.compile_certificate(machine,T,deadlines)
                valid=all(d>=i for i,d in enumerate(deadlines,1))
                try:v=cert.canonical(labels)
                except ValueError:need(not valid,'Unexpected rejected deadline');wrong+=1
                else:need(valid and cert.validate(v),'Unexpected accepted deadline');zeros+=1
        # Duplicate legal rules permit fractional selector mixtures over Q>=0.
        m=c.Machine((c.Rule(0,0),c.Rule(0,0)),(0,0,0),frozenset())
        cert=c.compile_certificate(m,1);v={n:0 for n in cert.variables};v['s_0_0']=v['s_0_1']=Fraction(1,2)
        need(cert.polynomial.evaluate(v)==0 and not cert.validate(v),'Rational domain boundary')
    return {'natural_guard_cases':gadgets,'complete_offzero_quadratics':comparisons,'signed_quadratic_cases':comparisons//2,'canonical_deadline_zeros':zeros,'missed_deadlines':wrong,'signed_guard_counterexample':list(signed),'nonnegative_rational_selector_counterexample':'s0=s1=1/2 with duplicate stay rules'}

def exported_polynomial_checks(roots):
    out={}
    for mode in ('finite','infinite'):
        d=json.loads((roots['positive']/f'data/{mode}_certificate.json').read_text())
        e=exact_sos(d['quadratic_residuals']);need(sparse(d['expanded_quartic'])==e,'Complete symbolic exported SOS')
        need(all(eval_terms(r,d['sample_assignment'])==0 for r in d['quadratic_residuals']),'Export residuals')
        need(all(d['sample_assignment'][a['result']]==a['base']**d['sample_assignment'][a['exponent']] for a in d['power_atoms']),'Export powers')
        out[mode]={'variables':len(d['variables']),'residuals':len(d['quadratic_residuals']),'power_atoms':len(d['power_atoms']),'exact_sos_monomials':len(e),'degree':max(map(len,e))}
    return out

def repaired_checks(roots,work):
    n=0
    with modules('positive',roots['positive']) as (p,pc,checker):
        f=p.ExpPoly({1:[64],2:[-20],4:[1]});chain=[f,p.ExpPoly({})];rows=[[p.Run(0,6,1)],[p.Run(0,6,0)]]
        need(not p.verify_profiles(chain,rows,6),'Forged chain rejected');n+=1
        need(rejected(lambda:p.build_profiles(chain,6)),'Forged construction rejected');n+=1
        for chain in ([p.ExpPoly({1:[1]})],[p.ExpPoly({}),p.ExpPoly({1:[1]})],[p.ExpPoly({2:[1]}),p.ExpPoly({3:[1]}),p.ExpPoly({})]):
            need(not p.valid_chain(chain),'Invalid chain rejected');n+=1
        coeff=[1];terms={1:coeff};f=p.ExpPoly(terms);f.value(0);coeff[0]=-1;terms[2]=[10]
        need(dict(f.terms)=={1:(1,)} and f.value(0)==1 and f.value(2)==1,'Coefficient snapshot')
        for call in (lambda:f.terms.__setitem__(1,(-1,)),lambda:setattr(f,'terms',{1:(-1,)})):
            need(rejected(call),'Read-only cached coefficient surface');n+=1
        for x in (True,1.0,'1',Fraction(1)):
            for call in (lambda x=x:p.ExpPoly({x:[1]}),lambda x=x:p.ExpPoly({1:[x]}),lambda x=x:f.value(x),lambda x=x:p.annihilator({1:x}),lambda x=x:p.Run(x,4,1)):
                need(rejected(call),'Positive exact input boundary');n+=1
        # Warm valid_cache integer1 before bool/float attempts must still reject.
        f.value(1)
        for x in (True,1.0):need(rejected(lambda x=x:f.value(x)),'Exact index even after cache');n+=1
        d=json.loads((roots['positive']/'data/finite_certificate.json').read_text())
        q=sparse(d['expanded_quartic']);a=d['sample_assignment'][0]
        for m,c in {(0,0):1,(0,):-a-3,():3*a}.items():q[m]=q.get(m,0)+c
        bad=copy.deepcopy(d);bad['expanded_quartic']=serial(q);file=work/'bad_expansion.json';write_json(file,bad)
        need(rejected(lambda:checker.check(file)),'Complete SOS equality rejects two-point alias');n+=1
        for kind in ('value_bool','coefficient_float','index_negative','power_base_bool','domain','variable_index_bool'):
            bad=copy.deepcopy(d)
            if kind=='value_bool':bad['sample_assignment'][1]=False
            elif kind=='coefficient_float':bad['quadratic_residuals'][0][0][0]=1.0
            elif kind=='index_negative':bad['quadratic_residuals'][0][0][1][0]=-len(bad['variables'])
            elif kind=='power_base_bool':bad['power_atoms'][0]['base']=True
            elif kind=='domain':bad['domain']='integers'
            else:bad['variables'][0]['index']=False
            file=work/(kind+'.json');write_json(file,bad);need(rejected(lambda:checker.check(file)),'Positive schema '+kind);n+=1
        # Explicit checker guards remain active under optimized Python.
        r=subprocess.run([sys.executable,'-O',str(roots['positive']/'code/check_export.py'),str(work/'bad_expansion.json')],capture_output=True,timeout=60)
        need(r.returncode!=0,'Optimized independent checker rejects alias');n+=1
    with modules('clock',roots['clock']) as (c,checker):
        rules=[c.Rule(0,0)];initial=[0,0,0];accepting=[0]
        m=c.Machine(rules,initial,accepting);cert=c.compile_certificate(m,1,(1,));v=cert.canonical((0,))
        rules[0]=c.Rule(7,7);initial[0]=7;accepting.clear()
        need(m.initial==(0,0,0) and m.rules==(c.Rule(0,0),) and m.accepting==frozenset({0}) and cert.canonical((0,))==v,'Deep Machine snapshot')
        for x in (True,0.0,'0',Fraction(0)):
            for call in (lambda x=x:c.Machine((c.Rule(0,0),),(0,0,x),{0}),lambda x=x:c.Machine((c.Rule(0,0),),(0,0,0),[0,x]),lambda x=x:c.encode_stack([x])):
                need(rejected(call),'Clock exact domain');n+=1
        need(rejected(lambda:c.Machine([object()],(0,0,0),set())),'Unvalidated Rule rejected');n+=1
    with modules('spectral',roots['spectral']) as (s,q):
        d=json.loads((roots['spectral']/'examples/hidden_negative_quartic.json').read_text())
        for kind in ('bool_value','float_coefficient','negative_index','bool_bits','inputs_negative','wrong_name_count','mode_atoms'):
            bad=copy.deepcopy(d)
            if kind=='bool_value':bad['values'][next(i for i,x in enumerate(bad['values']) if x==0)]=False
            elif kind=='float_coefficient':bad['residuals'][0][0][0]=float(bad['residuals'][0][0][0])
            elif kind=='negative_index':next(t for r in bad['residuals'] for t in r if t[1])[1][0]-=len(bad['values'])
            elif kind=='bool_bits':bad['bits']=True
            elif kind=='inputs_negative':bad['inputs'][0]=-1
            elif kind=='wrong_name_count':bad['names'].pop()
            else:bad['power_atoms']=[[0,0,0]]
            file=work/(kind+'.json');write_json(file,bad);need(not q.verify_export(file),'Spectral schema '+kind);n+=1
        cert=s.build_certificate(s.Sequence((s.Mode(1,(1,)),)),0)
        for x in (True,1.0,'1',Fraction(1)):
            need(rejected(lambda x=x:q.compile_certificate(cert,x)),'Exact bit width');n+=1
        for x in (0,1,None,'false'):
            need(rejected(lambda x=x:q.compile_certificate(cert,None,x)),'Exact predicate flag');n+=1
    return {'focused_rejections':n,'immutable_snapshot_scenarios':2,'optimized_checker_rejection':True}

def author_replay(key,root,original):
    records=[]
    for argv in COMMANDS[key]:
        run=subprocess.run([sys.executable,*argv],cwd=root,text=True,capture_output=True,timeout=300)
        need(run.returncode==0,f'Author command failed {key} {argv}: {run.stderr}')
        records.append({'argv':argv,'exit_code':run.returncode})
    compared=[]
    for item in PINS[key]['members']:
        rel=item['path']
        if not rel.endswith('.json'):continue
        old=json.loads((original/rel).read_text());new=json.loads((root/rel).read_text())
        need(normalized(key,rel,old)==normalized(key,rel,new),'Author JSON differs '+key+'/'+rel)
        volatile = (key,rel) in (('positive','data/test_results.json'),('clock','test_results.json'))
        compared.append({'path':rel,'byte_identical':None if volatile else (original/rel).read_bytes()==(root/rel).read_bytes(),'normalized_sha256':json_digest(normalized(key,rel,new))})
    return {'commands':records,'json_comparisons':compared}

def verify(positive_root, spectral_root, clock_root, patch_dir, *, run_authors=True):
    roots=dict(zip(('positive','spectral','clock'),map(lambda p:Path(p).resolve(),(positive_root,spectral_root,clock_root))))
    patch_dir=Path(patch_dir).resolve()
    for key,root in roots.items():
        for row in PINS[key]['members']:
            need(digest(root/row['path'])==row['sha256'],'Original member pin '+key+'/'+row['path'])
        need(digest(patch_dir/(key+'_boundaries.patch'))==REPAIRS[key]['patch_sha256'],'Repair patch pin '+key)
    with tempfile.TemporaryDirectory(prefix='spectral-review-') as td:
        work=Path(td)
        result={'status':'PASS','review_source_sha256':digest(__file__),'scope':'Bounded finite checks plus private repairs; no infinitary theorem mechanically verified','pins':PINS,'repair_pins':REPAIRS}
        result['observed_original_boundaries']=original_findings(roots,work)
        result['exact_export_identities']=exported_polynomial_checks(roots)
        result['independent_sequences']=sequence_checks(roots)
        result['independent_clock_algebra']=clock_checks(roots['clock'])
        patched={};result['author_replays']={}
        for key,root in roots.items():
            originalcopy=work/(key+'_original');shutil.copytree(root,originalcopy)
            dest=work/(key+'_patched');shutil.copytree(root,dest);patched[key]=dest
            run=subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(patch_dir/(key+'_boundaries.patch'))],cwd=dest,text=True,capture_output=True,timeout=60)
            need(run.returncode==0,'Private patch application '+run.stdout+run.stderr)
            for rel,row in REPAIRS[key].items():
                if rel=='patch_sha256':continue
                need(digest(dest/rel)==row['new'],'Repaired source pin '+key+'/'+rel)
            if run_authors:
                result['author_replays'][key]={'original':author_replay(key,originalcopy,root),'repaired':author_replay(key,dest,root)}
        result['repair_regressions']=repaired_checks(patched,work)
        result['repaired_sequence_checks']=sequence_checks(patched)
        result['repaired_clock_checks']=clock_checks(patched['clock'])
        return result

def main():
    a=argparse.ArgumentParser(description=__doc__)
    for key in ('positive','spectral','clock'):a.add_argument('--'+key+'-root',type=Path,required=True)
    a.add_argument('--patch-dir',type=Path,required=True);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path)
    args=a.parse_args();r=verify(args.positive_root,args.spectral_root,args.clock_root,args.patch_dir)
    if args.expect:need(json.loads(args.expect.read_text())==r,'Saved receipt mismatch')
    if args.output:write_json(args.output,r)
    print(json.dumps(r,indent=2))

if __name__=='__main__':main()
