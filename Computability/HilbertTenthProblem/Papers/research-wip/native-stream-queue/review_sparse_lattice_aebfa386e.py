#!/usr/bin/env python3
"""Pinned isolated sparse-lattice review and exact-constructor regression."""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import hashlib, importlib.util, itertools, json
from pathlib import Path
import shutil, subprocess, sys, tempfile, zipfile

ARCHIVE_SHA = '90c9dadeccad7c70c777b141b0c65029b992048fd69448f0f8e035ec522cdc68'
PATCH_SHA = 'b35dbe66ef29003111e3839ecb6a87bff6e5bf438360df4f31eb0ee855a8c4f2'
MEMBERS = {'sparse-lattice-release/README.md': '415cd1bdb86e0efd15f47eacd9e6ac9dc9e9d7b40d840dc1527730ab4989629c', 'sparse-lattice-release/SHA256SUMS': '1b559b95498d8655be253bb91af5d2d3d8c5144390da8b47dc8b3183c7bdaede', 'sparse-lattice-release/SOURCE-PROVENANCE.md': '5d837e9f7b7d2db138195a943a1eb5f063edfc0f1f99b2227e9234d7cbe6d112', 'sparse-lattice-release/build.sh': 'e63418cb25914020c70529dfe5e772d10dd511f53f2134a5c6d29f8fa468e4ac', 'sparse-lattice-release/paper/barriers.tex': '86a22c1930cd2003fb4fa0b017c2090efa60aa769e6d818a22eea99e630f6ac9', 'sparse-lattice-release/paper/core.tex': '3a4c6b5fdd18d569fd50b36dd79652429c84773d02a819442ef32a020ba7639e', 'sparse-lattice-release/paper/reproduction.tex': 'f621a67ce2fada86eb366826a1ff7780dead7552cdf152c86c77a7074154aefa', 'sparse-lattice-release/paper/semilinearity.tex': '9114ba954d8878772afd3f65837cfbc668ff8f03e3c26c921d48633dd52561b7', 'sparse-lattice-release/paper/source.tex': '7d1dd8c99339d8ae8c9849c7be1d0fd02974d5d683ea217c55d391ad2cad5031', 'sparse-lattice-release/paper/sparse-lattice.tex': '21e18bba9473e3e27df3d9d0dfa6e077a757664dcf00be3678e08d6a98686768', 'sparse-lattice-release/receipts/coefficient-crosscheck.json': '9a6acf1547428b829868c1196a311a7b4f2f0ec0c14dd9bfa278e2c0ddf3ca9a', 'sparse-lattice-release/receipts/core-checks.json': '74d186eacfe4c87d27bc5a7fa970ac898ed6f000462f498e6a48361cdf103b6b', 'sparse-lattice-release/receipts/independent-dynamics.json': '77f75b789ef158c69192bdd11b1b546a1af671d16321a96763937b82966c6425', 'sparse-lattice-release/receipts/independent-rows.json': 'e1a61f72a23973c15c3234819244e87170b58a527fb4139ee18678616ca6fb95', 'sparse-lattice-release/receipts/legacy-factorized.json': '17dfbefdf4f16d5a2fb49f86d69d63dc9f07eff60372f0831e990e8d281f1907', 'sparse-lattice-release/receipts/morita-n0.json': '9883877a98c75ac6d58446292410813d3d63af456f4f4073c22596f3a29b57d1', 'sparse-lattice-release/receipts/morita-n2.json': 'd2aa41a555ef23427a7fa88b6654698fc0fbf03f60d8757edeee97647b5d2fa9', 'sparse-lattice-release/receipts/morita-source.json': 'c27dd7fd5ae38de3dadc832095e0b29f5ef6f5a97fd2052e3f33e55ad3e355d0', 'sparse-lattice-release/receipts/release-verification.json': '6602b76eb3ebb9f08de2721c31ee15bf041d857b1cd1e47c9c123a1d7584fe14', 'sparse-lattice-release/receipts/semilinearity-components.json': '1d34e1ce08cbbb7c908f53c7875abae1da7b326a5190ed64241891f0f8b8abb9', 'sparse-lattice-release/receipts/semilinearity-independent.json': 'a204324fce285fdca271ed5d9d32820d69a7b65279028e04ad7d6fb999ad7fd8', 'sparse-lattice-release/receipts/two-mass-arithmetic.json': 'b52614cf5c469e7132cda508325c37d7dfee71268a053d2ba5cdbb5706440e1c', 'sparse-lattice-release/receipts/visual-qa.json': 'bca10e67283293160b87cadb4827bbb5e02fac5385215cd02203aaf985a8e755', 'sparse-lattice-release/replay/core/fixtures/binary_three_way_collision.json': '9f14f37676d31830bb3fad20be016dadf4e104aca5e401693a117560ae562964', 'sparse-lattice-release/replay/core/fixtures/binary_three_way_collision_orthant.json': 'b5a850ce727c1f0cad205e1930fdd571254aef8289b52f2c68ce07b6d7c35690', 'sparse-lattice-release/replay/core/fixtures/huge_empty_span.json': 'f89a554b6e5685d44111974b6238ce0f2030c446b5badc55377c7e0761e90858', 'sparse-lattice-release/replay/core/fixtures/morita_doubling_n0_pulse_T7.json.gz': '6114a092e38eaa31b57efaf00d8bb40dc1e8f54ae4579e407182d207327bdee0', 'sparse-lattice-release/replay/core/fixtures/morita_doubling_n2_pulse_T41.json.gz': '87dc5f3bedca34f322c22ee19d28c72a97b7a9f453641f3199377c23fc3ccf0d', 'sparse-lattice-release/replay/core/fixtures/ternary_mixed_mass.json': 'bcd95854294dd8760f12085a47323fc38baf2efcc8cfc4064edf02882dbe3810', 'sparse-lattice-release/replay/core/morita_audit.py': '16b184e23e128bc55efe48f9298f005d082d6a0023b6785ab0ffcbfc3b1b91ab', 'sparse-lattice-release/replay/core/run_checks.py': '2b0a5cf97d2dc38bcbb846d271db0ec8f285faa069afad4d2f4ea1b5a138a965', 'sparse-lattice-release/replay/core/run_morita_fixture.py': '1e68bd152160f3c979df5b59742b9b2fcf5792d342f0c8330df4ed78b9fd50b3', 'sparse-lattice-release/replay/core/sparse_mass.py': '1c35e0104730dfe99c9be4c350b49d66646d8e0dd7c7580b262367f1070d02c8', 'sparse-lattice-release/replay/independent/crosscheck_row_producer.py': 'd601675f55a5f7bb933695e8a545b8deb7523271573cc83810ddc727632d5b9b', 'sparse-lattice-release/replay/independent/independent_dynamics.py': 'cd7190dcda700afbec9c6d518ccbc0bd9ffa1fad4c58fbc44150bbcb9b2bf029', 'sparse-lattice-release/replay/independent/independent_polynomial_audit.py': '7dc5314dd01d73a995c6477e696082c45251b14dbf840a088b4b42742e5d66e8', 'sparse-lattice-release/replay/independent/independent_row_polynomial_audit.py': '509b01905c16cfbf480a34ae84651a6005867af9abda3cfddb1893a36a02122e', 'sparse-lattice-release/replay/morita/audit.py': '16b184e23e128bc55efe48f9298f005d082d6a0023b6785ab0ffcbfc3b1b91ab', 'sparse-lattice-release/replay/package_release.py': 'efcd5f539ea625e41e9fa338c1269720fac03caa92ad609ac8e46b86801c39ef', 'sparse-lattice-release/replay/run_release.py': '1e25127219bc7bbda20a8ae3a7f7174dca11b8ab9f577b1579ea326037291ec7', 'sparse-lattice-release/replay/semilinearity/audit.py': '202f375c0db50ca57b2868f8069a8e331473468ebf01ecb6877e1b3ddba130b7', 'sparse-lattice-release/replay/semilinearity/check.py': 'b33a353095213c5029bed8ccb9a3a29f6af1ed7627151f3cb63a1987191d9f12', 'sparse-lattice-release/replay/two-mass/audit.py': 'b5d20ccf40495e07ed0f09e880e1398f30abf27269b8fdcb2be320081370adb3', 'sparse-lattice-release/replay/two-mass/regression.py': '667d9dce9b37274e10b6ae6a4b8606fd8ecab6b49a8f083d92bdffc3914a749e', 'sparse-lattice-release/replay/verify_manifest.py': '19a5952ffdc8adaaeeb35a30686451ee093d36586612d79ab1c9f524c9e67815', 'sparse-lattice-release/run-replay.sh': '18eeb21ba74e930acbd7f540f2bc0be95d1efec733d33493da33d582ef7e2268', 'sparse-lattice-release/sparse-lattice.pdf': '9c29486b594927937ec2f6f7cbbf5354802a5a059efe62eee88ae972f86a95fe', 'sparse-lattice-release/tables/doubling-complete.csv': '1c8f6f4b05979dfc8436b0ded58ce13bc1b730de4813d07b2a8d2f2d2a7f3d60', 'sparse-lattice-release/tables/false-signal-complete.csv': 'ade52ce4cfb7fcb61de9952de6de2f7b59e8c50f37c50ff2db9ebc105475e283'}

def need(ok, message):
    if not ok:
        raise AssertionError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,(list,tuple)): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def module(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m)
    return m

def unpack(archive,base):
    need(sha(archive)==ARCHIVE_SHA,'archive pin')
    with zipfile.ZipFile(archive) as z:
        names=[m.filename for m in z.infolist()]
        need(len(names)==len(set(names)),'duplicate members')
        found={}
        for m in z.infolist():
            p=Path(m.filename)
            need(not p.is_absolute() and '..' not in p.parts and '\\' not in m.filename and (m.external_attr>>16)&0o170000!=0o120000,'unsafe member')
            if m.is_dir(): continue
            data=z.read(m);found[m.filename]=hashlib.sha256(data).hexdigest()
            target=base/p;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        need(found==MEMBERS,'member inventory')
    return base/'sparse-lattice-release'

def author(root):
    subprocess.run([sys.executable,'replay/verify_manifest.py'],cwd=root,check=True,capture_output=True)
    return release(root)

def release(root):
    run=subprocess.run([sys.executable,'replay/run_release.py','--regenerate-source'],cwd=root,check=True,capture_output=True,text=True,timeout=1200)
    work=Path(run.stdout.rsplit('Fresh output directory: ',1)[1].strip())
    result=json.loads((work/'results/release-verification.json').read_text())
    expected=json.loads((root/'receipts/release-verification.json').read_text())
    for d in (result,expected):
        d.pop('python');d.pop('packaged_producer_sha256')
    need(exact(result,expected),'author normalized receipt')
    return result

def focused(original,fixed):
    a=module(original/'replay/core/sparse_mass.py','sparse_original_review')
    m=module(fixed/'replay/core/sparse_mass.py','sparse_fixed_review')
    counts=Counter()
    def check(key,value): need(value,key);counts[key]+=1
    b=a.Builder();b.new('x',2**60+1);b.constrain('float',a.Poly((((),float(2**60)),((0,),-1.0))))
    check('original_float_false_zero',b.validate_witness() and 2**60-b.values[0]==-1)
    invalid=[[],(((),0),),(((),True),),(((),1.0),),(([],1),),(((False,),1),),(((0.0,),1),),(((1,0),1),),(((0,),1),((),1)),(((),1),((),2)),([(),1],)]
    for terms in invalid:
        try:m.Poly(terms)
        except (ValueError,TypeError):check('malformed_constructor_rejected',True)
        else:raise AssertionError('invalid polynomial accepted')
    check('signed_parameter_index_retained',m.Poly.variable(-1).evaluate([],[-7])==-7)
    # Independent lane transport/collision: no producer dynamics functions.
    def step(table,conf):
        incoming=defaultdict(lambda:[0,0,0])
        for x,lanes in conf.items():
            for lane,mass in enumerate(lanes):incoming[x+lane-1][2-lane]+=mass
        return {x:table[tuple(v)] for x,v in incoming.items() if sum(v)}
    fibers=defaultdict(list)
    for key in itertools.product(range(2),repeat=3):fibers[sum(key)].append(key)
    tables=[]
    for p,q in itertools.product(itertools.permutations(fibers[1]),itertools.permutations(fibers[2])):
        table={(0,0,0):(0,0,0),(1,1,1):(1,1,1)};table.update(zip(fibers[1],p));table.update(zip(fibers[2],q));tables.append(table)
    # Irreversible full-table case is covered by the theorem too.
    tables.append({key:tuple(int(j<sum(key)) for j in range(3)) for key in itertools.product(range(2),repeat=3)})
    for table in tables:
        for conf in ({0:(1,1,1)},{-2:(0,0,1),0:(0,1,0),2:(1,0,0)},{0:(1,0,0),10**80:(0,0,1)}):
            for horizon in (0,1,2):
                t=m.LocalTable.from_mapping(1,table);b,meta=m.compile_history(t,conf,horizon)
                baseline,oldmeta=a.compile_history(a.LocalTable.from_mapping(1,table),conf,horizon)
                check('patched_exact_polynomial_unchanged',[x.json() for x in b.residuals]==[x.json() for x in baseline.residuals] and b.values==baseline.values and meta==oldmeta)
                expected=[conf]
                for _ in range(horizon):expected.append(step(table,expected[-1]))
                check('independent_whole_history',b.validate_witness() and b.decode(meta['physical_shift'])==expected)
                M=sum(map(sum,conf.values()));check('exact_paid_counts',len(b.values)==horizon*(M*22+5*M*(M-1)) and len(b.residuals)==horizon*(17*M+5*M*(M-1)))
                check('height',max(b.values,default=0)<=meta['witness_height_bound'])
                yes,_=m.compile_history(t,conf,horizon,endpoint=expected[-1]);no,_=m.compile_history(t,conf,horizon,endpoint={10**81:(1,0,0)})
                check('endpoint_accept_and_reject',yes.validate_witness() and not no.validate_witness())
    t=m.LocalTable.from_mapping(2,{k:k for k in itertools.product(range(3),repeat=3)})
    for orthant in (False,True):
        b,_=m.compile_history(t,{0:(0,0,1)},1,orthant_exact=orthant)
        values=list(b.values);ids=[j for j,name in enumerate(b.names) if '.row.' in name]
        for i in ids:values[i]=0
        values[ids[0]]=values[ids[18]]=Fraction(1,2)
        check('real_orthant_distinction',(b.score(values)==0)==(not orthant))
    # A caller must still bind the intended descriptor; altered coefficient packets fail.
    b,meta=m.compile_history(m.LocalTable.from_mapping(1,tables[0]),{0:(0,0,1)},1)
    with tempfile.TemporaryDirectory() as tmp:
        path=Path(tmp)/'cert.json';packet=b.export(path,meta)
        check('bound_export',m.verify_bound_export(path)['valid'])
        for field in ('residuals','rows'):
            bad=json.loads(json.dumps(packet));bad[field]=[];path.write_text(json.dumps(bad))
            try:m.verify_bound_export(path)
            except ValueError:check('changed_bound_circuit_rejected',True)
            else:raise AssertionError('changed bound circuit')
    # The printed scheme defect and unsafe observer use a separate source module.
    source=module(original/'replay/core/morita_audit.py','sparse_morita_review')
    for j in (0,1):
        delta=[(0,1-j,'0',1),(1,j,'+',2)]
        bad,_,_=source.audit_rows(3,source.compile_partial(3,delta,printed_82=True))
        good,_,_=source.audit_rows(3,source.compile_partial(3,delta))
        check('printed_sign_counterexample_and_repair',any(row[0]=='mass' for row in bad) and not good)
    need((original/'replay/core/morita_audit.py').read_bytes()==(original/'replay/morita/audit.py').read_bytes(),'duplicate source audit differs')
    return dict(counts)

def verify(archive,patch,authors):
    need(__debug__,'assertions required');need(sha(patch)==PATCH_SHA,'patch pin')
    with tempfile.TemporaryDirectory(prefix='sparse-review-') as tmp:
        root=unpack(archive,Path(tmp)/'original');fixed=Path(tmp)/'fixed';shutil.copytree(root,fixed)
        subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(Path(patch).resolve())],cwd=fixed,check=True,capture_output=True)
        checks=focused(root,fixed)
        result=dict(status='PASS',archive_sha256=ARCHIVE_SHA,member_sha256=MEMBERS,patch_sha256=PATCH_SHA,patched_source_sha256=sha(fixed/'replay/core/sparse_mass.py'),independent=checks)
        if authors:
            result['original_author']=author(root)
            # Patched source intentionally differs from the original manifest; verify
            # the original manifest before patching, then use actual-source-pinned replay.
            result['patched_author']=release(fixed)
            need(exact(result['original_author'],result['patched_author']),'author result changed')
        return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archive',required=True,type=Path);p.add_argument('--patch',required=True,type=Path);p.add_argument('--authors',action='store_true');p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);args=p.parse_args()
    result=verify(args.archive,args.patch,args.authors)
    if args.expect:need(exact(result,json.loads(args.expect.read_text())),'saved receipt mismatch')
    if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result['independent'],sort_keys=True))
