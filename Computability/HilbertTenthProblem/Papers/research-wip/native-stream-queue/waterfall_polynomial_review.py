#!/usr/bin/env python3
"""Pinned, portable bounded review of the Waterfall grouped compiler.

No archive or caller source is modified. Formal projection checks use an
independent sparse integer polynomial implementation, not source P arithmetic.
"""
from __future__ import annotations
import argparse, hashlib, importlib.util, itertools, json, random, shutil, subprocess, sys, tempfile
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run the review without Python -O; assertions are required')

PINS={'LICENSE-PROVENANCE.md': '33f59672c004289ff33a3d1276c88b26868bb3abea8cfbe11b428b188f55bc18', 'README.md': '1fea6e87a316ac318bb8f9e1f8cc98d788f8e11dac0bf074f5e8182c50527b96', 'SOURCE-PROVENANCE.md': '5ffadace5010a56fac1c58ffb45955eb0a7cb2fbd666a9df62430ebfa53e513b', 'build.sh': '52d03b9dfd11974a3dc705cd5f1007f738d36d0788152bc06723af3109806011', 'paper/affine-gap-table.tex': 'fcc548e40f23211f8150a4dda7dd961986309d953cbe362be3dc3d36a13cdf1f', 'paper/waterfall-diophantine.tex': '22d6fc7aa755dcd3f6043f1b7472a82f6df2221bc3b21582a9c0fa76372a4e2f', 'receipts/halting-example.json': 'eccceba955be855e5930be5147f5f027073064c4eee6c8092891a223ddfb7b9b', 'receipts/independent-receipt.json': '0ef24d91233c7afd0f753c3fcd33ea630ad02f69efb896dd241ae4c836ad26e9', 'receipts/matrix-definition.json': 'e40b7e6f6ee848ad6080f2c0446fad50a02ae6a5abe2fd04e74eab7ddfa30053', 'receipts/quadratic-independent.json': '72df4620fad9f5d21eb6ae2c61b5900d366d2388d6bae62e5c8f1a2f874db736', 'receipts/release-verification.json': 'ff2d8d89399df1764bd420c4ffb95450e5a0ec32148a66bad23339d7872eb355', 'replay/affine-gap-forms.json': '49d3782a6c551491ef96ae86ddfcfadb26cbda78f8ad642444b3890518cbbf71', 'replay/certificate-receipt.json': '76f70a878cf9ebdede001ce5ce1fac6f948194576ff5d770aa469756e586a6fa', 'replay/frontend-receipt.json': '6e5870d833eabdbd72f31cc7028ce66521ec4e4a7e58c7300689c3a0b1129399', 'replay/grouped-quadratic-receipt.json': '20015ca8590fab70c44bc218e4041eca9f8347147bf1eb3b17d08722086f3ce8', 'replay/grouped-quadratic7-certificate.json': '96e7e359c7ee28880252e73c9f77315d48d350f95c0d6b9eb36f91ad570d7f1c', 'replay/grouped-quadratic7-fixture.json': '3b04a56667415a1cf84067d11e81fc27497103e7655b350a9d9796cf18a79f45', 'replay/grouped_quadratic.py': '506c7d8505e2076628b351a016104a3ad851a4178fa664709ae87774a645dc7f', 'replay/unit-ledgers.json': 'a34368312f6c55e6d5a44ae03bcf3ebe4f307eb3f8bae6dd99ee8a91376e9fa1', 'replay/verify_certificates.py': '3e20a9820c442199f595c6dd7d5a5c74f0d9bc863d88fd2ca432d1452dc40f58', 'replay/verify_frontend.py': '951c3482067c6754f23f3ad4cf21e13efe32f51ec9eed599bce02cac6117589d', 'replay/verify_frontend_independent.py': 'd8956977d1d302004573ae9e162f929fa144026a464b6524d84a18a16f10531b', 'replay/verify_halting_example.py': 'cacc0a77fdcefac2775665c8272cf518ae9798543c40dbc083753875cd4dff68', 'replay/verify_matrix_definition.py': 'acdbfaf3dc3d5199b97dab6b1fabdcca741313c6d13a9fe6de45589db5ce34e6', 'replay/verify_quadratic_independent.py': '05c06c401ed3583dabe16b06fc5293ec7858b2abea23087bd6c0d82aa83d906f', 'replay/verify_release.py': 'dd502cc1268db1960da45260efe9e9c4e70813ba9ee918a88e4a1b5efcaa0d95', 'run-replay.sh': 'a703d0b085adea523ebe6c088bd996c1d168afa6a8554f1215d07b5f60154532', 'source/UniversalTM15x2.tm.txt': 'ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae', 'source/UniversalTM15x2.twm.txt': '52cfed3f6cba671ed7b166c126288d555ed687b74622ae5a9aaa5bee1345e46a', 'waterfall-diophantine.pdf': '8a37afcc8587649bdd5dc2d86b94b52369a3008c9c98932d5f9f373a0798d797', 'SHA256SUMS': '9f82c14406ef9b404594492ab87f5028c74e8c0bd350e99db64c465d2980561b'}
PATCH_PIN='0d73ed20437c35f420b3ecdf2b2f97dc370d303db8957b76d71bda1cd484a284'
PATCHED_PIN='f60497d970dad984ee9a13581c4421592e17cfb5b39663561de6c182c4e5841e'
AUTHOR=['grouped_quadratic.py','verify_quadratic_independent.py','verify_certificates.py','verify_halting_example.py','verify_release.py']

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def rejected(f):
    try:f()
    except (TypeError,ValueError,KeyError,AssertionError):return True
    raise AssertionError('malformed input unexpectedly accepted')

# Integer sparse polynomials, with monomials sorted at every multiplication.
def add(*ps):
    out={}
    for p in ps:
        for m,c in p.items():out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}
def sc(c,p):return {m:c*v for m,v in p.items() if c*v}
def con(c):return {():c} if c else {}
def var(n):return {(n,):1}
def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            t=tuple(sorted(m+n));out[t]=out.get(t,0)+c*d
    return {m:c for m,c in out.items() if c}
def sub(p,rest):
    out={}
    for m,c in p.items():
        term=con(c)
        for n in m:term=mul(term,rest.get(n,var(n)))
        for n,d in term.items():out[n]=out.get(n,0)+d
    return {n:d for n,d in out.items() if d}

def val(p,env):
    return sum(c*__import__('math').prod(env[n] for n in m) for m,c in p.items())
def vars_of(p):return {n for m in p for n in m}

def source_poly(cert):
    out={}
    for _,p in cert.squares:out=add(out,mul(p.t,p.t))
    for _,a,b in cert.products:out=add(out,mul(a.t,b.t))
    return out

def projection(mod,k,kind):
    """Construct independently from actual RULES; no cached derivative source."""
    assert kind in ('first','first_head','first_suffix_head')
    if kind=='first_head':assert k>=2
    if kind=='first_suffix_head':assert k>=4
    cert=mod.DirectionalQuadratic(k);rest={}
    def fixed_selector(j,key):
        idx=[i for i,r in enumerate(mod.RULES) if r[:2]==key]
        assert len(idx)==1
        for i in range(29):rest[f'e{j}_{i}']=con(int(i==idx[0]))
    def output_r(j):
        return add(sc(2,var(f'YL{j}')),var(f'QR{j}'),
                   *(sc(r[4],var(f'e{j}_{i}')) for i,r in enumerate(mod.RULES) if not r[3]))
    fixed_selector(0,(0,0))
    for n in ('QL0','rL0','YL0'):rest[n]={}
    rest['YR0']=var('L0')
    if kind=='first_suffix_head':
        g,h,i=k-3,k-2,k-1
        for j,key,rem in ((g,(6,0),0),(h,(7,0),1),(i,(8,1),1)):
            fixed_selector(j,key)
            for n in ('QR','rR','YR'):rest[f'{n}{j}']={}
            rest[f'rL{j}']=con(rem)
        rest[f'QL{g}']=add(sc(4,var(f'QL{i}')),con(3))
        rest[f'QL{h}']=add(sc(2,var(f'QL{i}')),con(1))
        for j in (g,h,i):rest[f'YL{j}']=sub(output_r(j-1),rest)
        # This is an all-assignment affine identity, not a trace-only claim.
        boundary_r=sub(output_r(g-1),rest)
        assert sub(output_r(i),rest)==add(sc(8,boundary_r),con(3))
        initial_l=sub(dict(cert.squares[5*g+3][1].t),rest)
        # Source's inputL_g is 8 QI+6 minus previous outputL.
        assert initial_l.get((f'QL{i}',),0)==8
    if kind!='first':
        s1=add(*(sc(r[1],var(f'e1_{i}')) for i,r in enumerate(mod.RULES)))
        rest['rR0']=sub(s1,rest)
    remaining=[n for n in cert.witnesses if n not in rest]
    allowed=set(cert.parameters+remaining)
    for p in rest.values():
        assert vars_of(p)<=allowed
        assert all(type(c) is int and c>=0 for c in p.values())
        assert all(len(m)<=1 for m in p)
    squares=[(n,sub(p.t,rest)) for n,p in cert.squares]
    products=[(n,sub(a.t,rest),sub(b.t,rest)) for n,a,b in cert.products]
    deleted_squares=[n for n,p in squares if not p]
    deleted_products=[n for n,a,b in products if not mul(a,b)]
    squares=[(n,p) for n,p in squares if p]
    products=[(n,a,b) for n,a,b in products if mul(a,b)]
    child={}
    for _,p in squares:child=add(child,mul(p,p))
    for _,a,b in products:
        assert all(c>=0 for c in a.values()) and all(c>=0 for c in b.values())
        child=add(child,mul(a,b))
    # Complete formal equality, including every source term and output parameter.
    full=sub(source_poly(cert),rest)
    assert child==full
    assert vars_of(child)<=allowed
    assert child.get(('tau','tau'))==1 and max(map(len,child))==2
    if kind=='first':expect=(35*k-33,5*k,2*k-2)
    elif kind=='first_head':expect=(35*k-34,5*k-1,2*k-2)
    else:expect=(35*k-138,5*k-15,2*k-8)
    assert (len(remaining),len(squares),len(products))==expect
    if k==4 and kind=='first_suffix_head':
        assert dict(squares)['state1']==con(5)
        assert rest['rR0']=={}
    return cert,rest,remaining,child,dict(k=k,kind=kind,witnesses=len(remaining),squares=len(squares),products=len(products),
         monomials=len(child),deleted_square_names=deleted_squares,deleted_product_names=deleted_products)

def independent_trace(root,L,R,limit):
    rows=(root/'source/UniversalTM15x2.tm.txt').read_text().splitlines()[0].split('_')
    q=s=0;steps=[]
    for j in range(limit+1):
        instruction=rows[q][3*s:3*s+3]
        if instruction=='---':return steps,(q,s,L,R)
        if j==limit:return None
        w=int(instruction[0]);right=instruction[1]=='R';qn=ord(instruction[2])-65
        directional,other=(R,L) if right else (L,R)
        Q,r=divmod(directional,2)
        steps.append((q,s,Q,r,other,right,6+3*Q+r+3*other))
        L,R=(2*L+w,Q) if right else (Q,2*R+w)
        q,s=qn,r

def main_checks(root,patch,work):
    for name,digest in PINS.items():assert sha(root/name)==digest,(name,sha(root/name))
    assert sha(patch)==PATCH_PIN
    before=load(root/'replay/grouped_quadratic.py','waterfall_original_review')
    cert=before.DirectionalQuadratic(7);env,halt,_=cert.lift(6,0)
    assert halt and cert.energy(env)==0
    bad=dict(env,L0=6.0);assert type(cert.energy(bad)) is float and cert.energy(bad)==0
    bad=dict(env,e0_0=True);assert cert.energy(bad)==0
    fenv,fhalt,_=cert.lift(6.0,0);assert fhalt and cert.energy(fenv)==0.0
    exported=cert.dump();exported['witnesses'].clear();assert not cert.witnesses
    original_regressions=['float natural parameter accepted at zero','Boolean witness accepted at zero',
                          'float half-tape lift produces noninteger witness types','exported witness list aliases compiler']
    original=work/'original';patched=work/'patched'
    shutil.copytree(root,original);shutil.copytree(root,patched)
    dry=subprocess.run(['patch','--batch','--fuzz=0','--dry-run','-p1','-i',str(patch)],cwd=patched,capture_output=True,text=True,timeout=300)
    assert dry.returncode==0,dry.stdout+dry.stderr
    apply=subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(patch)],cwd=patched,capture_output=True,text=True,timeout=300)
    assert apply.returncode==0,apply.stdout+apply.stderr
    assert sha(patched/'replay/grouped_quadratic.py')==PATCHED_PIN
    after=load(patched/'replay/grouped_quadratic.py','waterfall_patched_review')
    cert=after.DirectionalQuadratic(7);env,halt,_=cert.lift(6,0)
    nreject=0
    malformed=[True,False,1.0,0.0,'1',None,-1]
    for x in malformed+[0]:
        rejected(lambda x=x:after.DirectionalQuadratic(x));nreject+=1
    for x in malformed:
        for slot in range(3):
            args=[6,0,7];args[slot]=x
            rejected(lambda args=args:after.tm_history(*args));nreject+=1
        for slot in range(2):
            args=[6,0];args[slot]=x
            rejected(lambda args=args:cert.lift(*args));nreject+=1
    for key in cert.parameters+cert.witnesses:
        for x in malformed:
            bad=dict(env);bad[key]=x
            rejected(lambda bad=bad:cert.energy(bad));nreject+=1
    for bad in ({k:v for k,v in env.items() if k!='L0'},dict(env,extra=0)):
        rejected(lambda bad=bad:cert.energy(bad));nreject+=1
    rejected(lambda:after.DirectionalQuadratic(8).lift(6,0));nreject+=1
    for x in [True,False,0.0,1.0,'1',None]:
        rejected(lambda x=x:after.P({():x}));nreject+=1
        rejected(lambda x=x:after.P.cast(x));nreject+=1
        rejected(lambda x=x:after.P.var('x').at({'x':x}));nreject+=1
    for mon in [('x',1),('',),('x',True),'x']:
        rejected(lambda mon=mon:after.P({mon:0}));nreject+=1
    for x in [True,1,1.0,None,'']:
        rejected(lambda x=x:after.P.var(x));nreject+=1
    assert after.tm_history(6,0,0)==([],False,(0,0,6,0))
    assert after.P({():-9,('x',):2}).at({'x':-11})==-31
    huge=10**500
    hugeenv=dict(env);hugeenv['L0']=huge
    assert type(cert.energy(hugeenv)) is int
    assert cert.energy(hugeenv)==cert.polynomial().at(hugeenv)>0
    originaldump=cert.dump();copydump=cert.dump()
    copydump['parameters'].clear();copydump['witnesses'].clear()
    copydump['squared_linear_residuals'][0]['polynomial'][0]['coefficient']=0.5
    copydump['nonnegative_products'][0]['left'].clear()
    assert cert.dump()==originaldump and cert.energy(env)==0
    terms={('x',):2};p=after.P(terms);terms[('x',)]=0.5
    assert p.at({'x':3})==6
    author_results=[]
    for branch in (original,patched):
        branchlog=work/(branch.name+'_logs');branchlog.mkdir()
        for script in AUTHOR:
            done=subprocess.run([sys.executable,str(branch/'replay'/script)],cwd=branch,capture_output=True,text=True,timeout=300)
            (branchlog/(script+'.log')).write_text(done.stdout+done.stderr)
            assert done.returncode==0,(branch.name,script,done.stdout,done.stderr)
            author_results.append(dict(copy=branch.name,command='python replay/'+script,status='PASS'))
    outputs=[]
    for directory in ('replay','receipts'):
        for file in sorted((original/directory).glob('*.json')):
            rel=file.relative_to(original)
            assert file.read_bytes()==(patched/rel).read_bytes(),str(rel)
            assert file.read_bytes()==(root/rel).read_bytes(),('original changed shipped JSON',str(rel))
            outputs.append(dict(path=str(rel),sha256=sha(file)))
    original_receipts={}
    for rel in ('replay/grouped-quadratic-receipt.json','receipts/quadratic-independent.json','replay/certificate-receipt.json',
                'receipts/halting-example.json','receipts/release-verification.json'):
        if (original/rel).is_file():
            data=json.loads((original/rel).read_text());data.pop('example',None);data.pop('events',None)
            original_receipts[rel]=data
    rng=random.Random(754744808)
    schedules=[];signed=natural=fixture_roundtrips=coordinate_mutations=arbitrary_bad=0
    for k in (1,2,3,4,5,7,8,12):
        kinds=['first']+(['first_head'] if k>=2 else [])+(['first_suffix_head'] if k>=4 else [])
        for kind in kinds:
            old,rest,remaining,poly,ledger=projection(after,k,kind);schedules.append(ledger)
            for signed_flag in (False,True):
                for _ in range(40):
                    vals={name:rng.randrange(-4,5) if signed_flag else rng.randrange(5) for name in old.parameters+remaining}
                    restored=dict(vals);restored.update({n:val(p,vals) for n,p in rest.items()})
                    source_value=sum(p.at(restored)**2 for _,p in old.squares)+sum(a.at(restored)*b.at(restored) for _,a,b in old.products)
                    assert val(poly,vals)==source_value
                    if signed_flag:signed+=1
                    else:
                        assert all(type(v) is int and v>=0 for v in restored.values())
                        assert source_value==old.energy(restored)>=0;natural+=1
            if k==7:
                parent,halt,_=old.lift(6,0);assert halt
                child={n:parent[n] for n in old.parameters+remaining}
                restored=dict(child);restored.update({n:val(p,child) for n,p in rest.items()})
                assert restored==parent and val(poly,child)==0;fixture_roundtrips+=1
                for name in remaining+['C','tau']:
                    bad=dict(child);bad[name]+=1
                    assert val(poly,bad)>0;coordinate_mutations+=1
                for _ in range(500):
                    bad=dict(child)
                    chosen=rng.sample(remaining+['C','tau'],rng.randrange(2,min(12,len(remaining))+1))
                    for name in chosen:bad[name]+=rng.randrange(1,6)
                    assert val(poly,bad)>0;arbitrary_bad+=1
    # Independent raw TM table determines complete natural witnesses; compare all
    # bounded first halts in a finite half-tape box against the source compiler.
    traces=0;early=0;prefixes=0
    for L in range(24):
        for R in range(24):
            result=independent_trace(root,L,R,40)
            if result is None:continue
            steps,end=result;k=len(steps);traces+=1
            original_cert=after.DirectionalQuadratic(k);lift,halt,observed=original_cert.lift(L,R)
            assert halt and observed==end and original_cert.energy(lift)==0
            assert lift['C']==sum(s[-1] for s in steps)
            assert lift['tau']==1+2*lift['C']+7*k
            for j,(q,s,Q,r,Y,right,count) in enumerate(steps):
                side='R' if right else 'L'
                for name,expected in (('Q',Q),('r',r),('Y',Y)):assert lift[f'{name}{side}{j}']==expected
                rule=[i for i,rule in enumerate(after.RULES) if rule[:2]==(q,s)][0]
                assert lift[f'e{j}_{rule}']==1
            rejected(lambda L=L,R=R,k=k:after.DirectionalQuadratic(k+1).lift(L,R));early+=1
            if k>1:
                prior=after.DirectionalQuadratic(k-1);v,halt,_=prior.lift(L,R)
                assert not halt and prior.energy(v)>0;prefixes+=1
    return dict(status='PASS',source_pins=PINS,patch_sha256=PATCH_PIN,patched_source_sha256=PATCHED_PIN,
        original_regressions=original_regressions,malformed_rejections=nreject,export_nested_snapshot_checks=5,
        author_runs=author_results,unchanged_json_outputs=outputs,author_receipts=original_receipts,
        projection_source_ring_identities=len(schedules),projection_schedules=schedules,
        restored_signed_assignments=signed,restored_natural_assignments=natural,
        first_halt_fixture_roundtrips=fixture_roundtrips,projected_single_coordinate_mutations=coordinate_mutations,
        projected_joint_mutations=arbitrary_bad,independent_raw_table_first_halts=traces,
        early_halt_horizon_rejections=early,strict_prehalting_prefixes=prefixes,
        scope='Complete formal polynomial graph identities for listed horizons; all-horizon proof is separate. Natural fixed-horizon family only. No fixed-arity universal operation claim.')

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--patch',type=Path,required=True);p.add_argument('--receipt',type=Path,required=True)
    a=p.parse_args();root=a.root.resolve();patch=a.patch.resolve()
    with tempfile.TemporaryDirectory(prefix='waterfall-polynomial-review-') as td:
        result=main_checks(root,patch,Path(td))
    a.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('author_receipts','unchanged_json_outputs','projection_schedules','source_pins')},indent=2))
if __name__=='__main__':main()
