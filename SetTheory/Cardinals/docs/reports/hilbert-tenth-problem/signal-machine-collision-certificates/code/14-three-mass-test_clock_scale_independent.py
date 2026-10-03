#!/usr/bin/env python3
"""Independent clock-scale contract audit. Explicit checks remain active under -O."""
import argparse, copy, hashlib, importlib.util, json, subprocess, sys
from collections import Counter
from fractions import Fraction
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--source-dir',type=Path,required=True)
p.add_argument('--legacy-dir',type=Path,required=True)
p.add_argument('--output-dir',type=Path,required=True)
a=p.parse_args(); S=a.source_dir.resolve(); L=a.legacy_dir.resolve(); R=a.output_dir.resolve();R.mkdir(parents=True,exist_ok=True)
if (R/'scale-receipt.json').exists():raise RuntimeError('Refusing to overwrite prior report')
def module(name,path):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m
C=module('scaled_certificate',S/'certificate.py');K=module('scaled_checker',S/'checker.py');O=module('legacy_certificate',L/'certificate.py');OK=module('legacy_checker',L/'checker.py')
counts=Counter();failures=[]
def check(ok,label):
    counts['checks']+=1
    if not ok:failures.append(label)
def reject(label,fun):
    try:fun()
    except (ValueError,TypeError):counts['rejections']+=1;return
    except Exception as e:failures.append(label+': unexpected '+type(e).__name__);return
    failures.append(label+': unexpectedly accepted')
def dump(o):return json.dumps(o,indent=2)+'\n'
def mat(m,mod):return mod.machine_from_json({'states':list(m.states),'halt':m.halt,'instructions':[vars(i) for i in m.instructions]})
def ev(form,w):return sum(v*(w[k] if k else 1) for k,v in form.items())
def mul(form,factor):return {k:factor*v for k,v in form.items() if factor*v}
def oracle(m,q,N,h):
    trace=[{'step':0,'state':q,'N':N,'microtime':0}];t=0
    for i in range(h):
        possible=[]
        for ins in m.instructions:
            if ins.source!=q:continue
            prime=(2,3)[ins.counter]
            if ins.operation in ('dec','positive') and N%prime:continue
            if ins.operation=='zero' and not N%prime:continue
            possible.append(ins)
        if len(possible)!=1:return None
        ins=possible[0];old=N;prime=(2,3)[ins.counter]
        if ins.operation=='inc':N*=prime;dt=108*old+96*N+8
        elif ins.operation=='dec':N//=prime;dt=96*old+108*N+8
        else:dt=192*N+8
        q=ins.target;t+=dt;trace.append({'step':i+1,'state':q,'N':N,'microtime':t})
    return trace if q==m.halt else None

def audit_case(m,q,h,inp,free,N,time_mode,output_mode='free'):
    tr=oracle(m,q,N,h)
    if tr is None:return
    t=tr[-1]['microtime'];end=tr[-1]['N']
    out=None if output_mode=='none' else {'mode':'fixed','value':end} if output_mode=='fixed' else {'mode':'free','name':'terminal_N'}
    time=None if time_mode=='none' else {'mode':'fixed','value':t} if time_mode=='fixed' else {'mode':'free','name':'elapsed'}
    time4=copy.deepcopy(time)
    if time_mode=='fixed':time4['value']=4*t
    args=(m,q,h,inp,out,time)
    old=O.export_certificate(mat(m,O),q,h,inp,out,time)
    default=C.export_certificate(*args);one=C.export_certificate(*args,clock_scale=1)
    four=C.export_certificate(m,q,h,inp,out,time4,clock_scale=4)
    check(dump(old)==dump(default)==dump(one),'legacy default/explicit1 bytes')
    check('clock_scale' not in one and four['clock_scale']==4,'metadata contract')
    unchanged=set(one)-{'physical_time','squares','time_spec'}
    check(all(one[k]==four[k] for k in unchanged),'unchanged branch/loader/ledger/source fields')
    check(four['physical_time']==mul(one['physical_time'],4),'aggregate affine exactly fourfold')
    for b,f in zip(one['squares'],four['squares']):
        if b['label']!='terminal:physical-time':check(b==f,'non-time square unchanged')
        else:
            expected=mul(b['affine'],4)
            if time_mode=='free':expected['elapsed']=-1
            check(f['affine']==expected,'time endpoint scales expression, not output coordinate')
    w1=C.make_witness(one,free);w4=C.make_witness(four,free)
    check(O.make_witness(old,free)==w1,'legacy witness identical')
    expected_w=copy.deepcopy(w1)
    if time_mode=='free':expected_w['elapsed']*=4
    check(w4==expected_w,'only free witness clock scaled')
    r1=K.check(one,w1);r4=K.check(four,w4)
    check(OK.check(old,w1)==r1,'legacy receipt identical')
    check(r4['physical_time']==4*t and ev(four['physical_time'],w4)==4*t,'physical scalar matches oracle')
    check(r4['final_N']==end and r4['ledger']==r1['ledger'],'final value and ledger unchanged')
    for got,want in zip(r4['source_trace'],tr):
        check(all(got[k]==(4*v if k=='microtime' else v) for k,v in want.items()),'trace agrees with independent source oracle')
    check(len(r4['source_trace'])==len(tr),'trace length')
    counts['semantic_cases']+=1

for op in ('inc','dec','positive','zero','nop'):
    for counter in (0,1):
        m=C.Machine(('run','halt'),'halt',(C.Instruction('run','halt',op,counter),))
        for N in range(1,25):
            if oracle(m,'run',N,1) is None:continue
            for tm in ('none','free','fixed'):
                for om in ('none','free','fixed'):
                    audit_case(m,'run',1,{'mode':'fixed_raw','N':N},{},N,tm,om)
m=C.Machine(('run','halt'),'halt',(C.Instruction('run','halt','nop',0),))
for A in range(3):
    for B in range(3):
        for aa in range(A+1):
            for bb in range(B+1):
                for tm in ('none','free','fixed'):
                    audit_case(m,'run',1,{'mode':'bounded_counters','A':A,'B':B},{'input_a':aa,'input_b':bb},2**aa*3**bb,tm)
for N in (1,2,3,5,11,100,10**30):
    for tm in ('none','free','fixed'):audit_case(m,'run',1,{'mode':'free_raw','name':'x'},{'x':N-1},N,tm)
for N in (1,5,100):
    for tm in ('none','free','fixed'):audit_case(C.Machine(('halt',),'halt',()),'halt',0,{'mode':'fixed_raw','N':N},{},N,tm)
ops=[('inc',0),('inc',1),('positive',0),('positive',1),('dec',0),('dec',1),('zero',0),('zero',1),('nop',0)]
mixed=C.Machine(tuple([f'q{i}' for i in range(9)]+['halt']),'halt',tuple(C.Instruction(f'q{i}',f'q{i+1}' if i<8 else 'halt',op,c) for i,(op,c) in enumerate(ops)))
for N in (1,5,7):
    for tm in ('none','free','fixed'):audit_case(mixed,'q0',9,{'mode':'fixed_raw','N':N},{},N,tm)
base_args=(m,'run',1,{'mode':'fixed_raw','N':5},{'mode':'free'},{'mode':'free'})
c1=C.export_certificate(*base_args);c4=C.export_certificate(*base_args,clock_scale=4);w4=C.make_witness(c4)
class IntSubclass(int):pass
bad=[True,False,0,-1,2,3,5,10**100,1.0,4.0,0.25,'1','4','',None,[],{},(),Fraction(1),Fraction(4),IntSubclass(1),IntSubclass(4)]
for v in bad:
    reject('export scale '+repr(v),lambda v=v:C.export_certificate(*base_args,clock_scale=v))
    c=copy.deepcopy(c4);c['clock_scale']=v
    reject('witness scale '+repr(v),lambda c=c:C.make_witness(c))
    reject('checker scale '+repr(v),lambda c=c:K.check(c,w4))
for sc in (1,4):
    c=C.export_certificate(*base_args,clock_scale=sc);c['clock_scale']=sc
    check(K.check(c,C.make_witness(c))['physical_time']==sc*(192*5+8),'serialized explicit valid scale')
mutations=[]
def mutant(label,fun):
    c=copy.deepcopy(c4);w=copy.deepcopy(w4);fun(c,w);mutations.append((label,c,w));reject(label,lambda:K.check(c,w))
mutant('remove scale4 metadata',lambda c,w:c.pop('clock_scale'))
mutant('replace scale4 metadata with1',lambda c,w:c.update(clock_scale=1))
mutant('branch ticks incorrectly scaled',lambda c,w:c['steps'][0][0].update(ticks=mul(c['steps'][0][0]['ticks'],4)))
mutant('native aggregate',lambda c,w:c.update(physical_time=c1['physical_time']))
mutant('native time square',lambda c,w:c['squares'].__setitem__(-1,c1['squares'][-1]))
mutant('native output witness',lambda c,w:w.update(physical_time=w['physical_time']//4))
mutant('wrong output witness',lambda c,w:w.update(physical_time=w['physical_time']+1))
mutant('ledger altered',lambda c,w:c['ledger'].update(core_variables=8))
for val in (192*5+8,4*(192*5+8)-1,4*(192*5+8)+1):
    c=C.export_certificate(m,'run',1,{'mode':'fixed_raw','N':5},None,{'mode':'fixed','value':val},clock_scale=4)
    reject('incorrect fixed scaled endpoint',lambda c=c:C.make_witness(c))
c=copy.deepcopy(c4);c['expanded_polynomial']=C.expand_polynomial(c)
check(K.check(c,w4)['physical_time']==4*(192*5+8),'expanded scale4 accepted')
c['expanded_polynomial'][0]['coefficient']+=1;reject('mutated scaled expansion',lambda:K.check(c,w4))
# Isolated CLI runs, using matching optimization mode; each input/output is kept.
python=[sys.executable]+(['-O'] if sys.flags.optimize else [])
def cli(argv,ok=True):
    p=subprocess.run(python+list(map(str,argv)),text=True,capture_output=True)
    counts['cli_runs']+=1;check((p.returncode==0)==ok,'CLI '+str(argv))
    with (R/'cli.log').open('a') as f:f.write(json.dumps({'argv':python+list(map(str,argv)),'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr})+'\n')
    return p
request={'machine':{'states':list(m.states),'halt':m.halt,'instructions':[vars(i) for i in m.instructions]},'initial_state':'run','horizon':1,'input_spec':{'mode':'fixed_raw','N':5},'output_spec':{'mode':'free'},'time_spec':{'mode':'free'}}
for tag,sc in [('default',None),('one',1),('four',4)]:
    req=copy.deepcopy(request)
    if sc is not None:req['clock_scale']=sc
    rp=R/(tag+'-request.json');cp=R/(tag+'-certificate.json');wp=R/(tag+'-witness.json');receipt=R/(tag+'-check.json');rp.write_text(dump(req))
    cli([S/'certificate.py','export',rp,cp,'--expanded']);cli([S/'certificate.py','witness',cp,wp]);cli([S/'checker.py',cp,wp,'--receipt',receipt])
    check(json.loads(receipt.read_text())['physical_time']==(sc or 1)*(192*5+8),'CLI clock')
check((R/'default-certificate.json').read_bytes()==(R/'one-certificate.json').read_bytes(),'CLI default and1 bytes')
cli([L/'certificate.py','export',R/'default-request.json',R/'legacy-default-certificate.json','--expanded'])
check((R/'default-certificate.json').read_bytes()==(R/'legacy-default-certificate.json').read_bytes(),'CLI historical default bytes')
json_bad=[True,False,0,2,-1,1.0,4.0,'1','4',None,[],{}]
for i,v in enumerate(json_bad):
    req=copy.deepcopy(request);req['clock_scale']=v;rp=R/f'invalid-{i}-request.json';rp.write_text(dump(req));cli([S/'certificate.py','export',rp,R/f'invalid-{i}-export.json'],False)
    c=copy.deepcopy(c4);c['clock_scale']=v;cp=R/f'invalid-{i}-certificate.json';cp.write_text(dump(c));cli([S/'certificate.py','witness',cp,R/f'invalid-{i}-witness.json'],False);cli([S/'checker.py',cp,R/'four-witness.json'],False)
for i,(label,c,w) in enumerate(mutations):
    cp=R/f'mutation-{i}-certificate.json';wp=R/f'mutation-{i}-witness.json';cp.write_text(dump(c));wp.write_text(dump(w));cli([S/'checker.py',cp,wp],False)
hashes={path.name:hashlib.sha256(path.read_bytes()).hexdigest() for path in [S/'certificate.py',S/'checker.py',S/'three_mass_collision_generator.py',Path(__file__)]}
check(hashes['three_mass_collision_generator.py']=='14b8bde4362803181dbee33d81e083ba4758ee51df7b23fcfd920a6f1de12d52','frozen generator hash')
report={'status':'PASS' if not failures else 'DEFECT_FOUND','optimization':sys.flags.optimize,'counts':dict(counts),'failures':failures,'source_sha256':hashes}
(R/'scale-receipt.json').write_text(dump(report));print(dump(report),end='')
if failures:sys.exit(1)
