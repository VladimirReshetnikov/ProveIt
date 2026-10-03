#!/usr/bin/env python3
"""Pinned isolated replay and independent review of two coercive graph reports."""
import argparse
from collections import Counter
from contextlib import contextmanager
from fractions import Fraction
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import random
import shutil
import subprocess
import sys
import tempfile
import zipfile

ARCHIVES=[{'members': {'Coercive_Green_Diophantine/README.md': '7dfc1478b9bdf78d46c2b2b763acdb90c4c4c420ecce1b571e290385ccdc562b', 'Coercive_Green_Diophantine/SOURCE_AUDIT.md': '679c001fe6905fa536696956693e59f364ab328147be73ced1ab3b8a6f3dee2a', 'Coercive_Green_Diophantine/article.pdf': '0f2f540cc8f753d30a64d8cac07fb79c6a8410bc2cebf324f8c6ec72c7c5250e', 'Coercive_Green_Diophantine/article.tex': '650c0676443ae54e8193640b1918c77a3ba33bdef1a44aa97fa0df87d951301a', 'Coercive_Green_Diophantine/code/green_machine.py': 'af92eec80675dfa170169b8ca9b713c60aaf2b9f23c4e9888f2f1005244428ad', 'Coercive_Green_Diophantine/code/verify.py': '997cf213b4898e3f0d8d3e35b53743c52961f9cecff7bc4ab5c084b4f7a119af', 'Coercive_Green_Diophantine/examples/countdown.json': 'bc58ed2201d3afd063391f91ec18e139d8a981e2e99fb6c9e4b80ac91bad40cf', 'Coercive_Green_Diophantine/examples/modular_false_positive.json': 'f31b05a6ff40764f4a78dd90154ba5e5e347f2488ae7f3103fdc8cf0837b35e5', 'Coercive_Green_Diophantine/validation/results.json': 'b8c2dc02914e11cded8220f9fb51ead94fdb15bcfa7b54ba97d626b93cb09ed5', 'Coercive_Green_Diophantine/validation/test_output.txt': 'b8c2dc02914e11cded8220f9fb51ead94fdb15bcfa7b54ba97d626b93cb09ed5'}, 'name': 'Coercive_Green_Diophantine', 'sha256': '8e2830036ad0a465f729d4729835b350ea288f758fd8bac8a3ac179ebe368d7a'}, {'members': {'well_conditioned_diophantine/README.md': '707d5d10bf6b9c4343097b2bc0fa7287115daa487099d0a942824d4928fec5e9', 'well_conditioned_diophantine/SHA256SUMS': 'dfb903b3d4f6ff5c283719175aecf850f8713c245932487572b2bc2f9232f8bb', 'well_conditioned_diophantine/article.pdf': '23d3a25765839ac03bf4d821c108ed86ddc10fccbbac4a71cf4f7e76aee73de8', 'well_conditioned_diophantine/article.tex': 'fb50479ffea02eff6cf675945e82b1eb33d8131b10e0cf3d102fd18e6aa13e40', 'well_conditioned_diophantine/build.sh': '8d29dd6caf384505fac88a166b660b6cb632cdc9d575c0f16ad96933a32dc217', 'well_conditioned_diophantine/examples/countdown_T3_polynomial.json': '46c0a14e756e313a1d51feba63f0f1f48da79a254e956aa168fd820392cdcc38', 'well_conditioned_diophantine/examples/countdown_T3_witness.json': '4d5810d6edff440b03739eebba64da06b77ef7a3368138bfa76409ad573e57e7', 'well_conditioned_diophantine/examples/localization_bounds.json': 'b0572c86af6a8059f55d89cd3aae40402b5fc2cae4753d3acae8b684ff921b6a', 'well_conditioned_diophantine/sources.md': '6f6d651ae28fb448612b6f5397edd3805db59119b769bc00b4ee471eb6c8e8c4', 'well_conditioned_diophantine/src/substrate.py': '3dd949eae682c7b57d2c3ee9f8e86dad5d40c156a33d6010568868bc1b9173e4', 'well_conditioned_diophantine/verification.json': '575e04f378436f6bbd7821c174014158332b94cf83dfe6dff58d900c25b66958', 'well_conditioned_diophantine/verify.py': 'ad08c9c72920fd15422007f89757c62d7561e6d16367afe348aec9ff629cdf96'}, 'name': 'Well_Conditioned_Diophantine_Computation', 'sha256': '9cd194e2d3b1cd7814ad465c1c4abae8966b6c7bb0b5a13d1955d17aba159258'}]
PATCH_SHA='cdd6307d5659ae0c72e7715b72e22e8692b07362d0a0f008f89a9ac85372f2a9'
PATCHED_SOURCE_SHA='7aec66923ff0137a57743842544909290b067bfb2bdd999541b40c6425d0d338'

def need(x,m):
 if not x:raise ValueError(m)
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def extract(path,base,info):
 need(hashlib.sha256(path.read_bytes()).hexdigest()==info['sha256'],'Archive pin mismatch');original={}
 with zipfile.ZipFile(path) as z:
  need(len(z.infolist())==len({e.filename for e in z.infolist()}),'Duplicate archive entry')
  for e in z.infolist():
   rel=Path(e.filename);need(not rel.is_absolute() and '..' not in rel.parts and '\\' not in e.filename and (e.external_attr>>16)&0o170000!=0o120000,'Unsafe archive member')
   if e.is_dir():continue
   data=z.read(e);need(hashlib.sha256(data).hexdigest()==info['members'].get(e.filename),'Member pin mismatch');original[e.filename]=data
   target=base/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
 need(set(original)==set(info['members']),'Member inventory mismatch');return original

@contextmanager
def module(path,name):
 before=sys.modules.get(name);present=name in sys.modules
 try:
  spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);yield m
 finally:
  sys.modules.pop(name,None)
  if present:sys.modules[name]=before

def command(args,root):
 r=subprocess.run(args,cwd=root,capture_output=True,text=True,timeout=300)
 need(r.returncode==0,'Author command failed: '+r.stderr[-1500:]);return r.stdout

def author(root,original,kind):
 if kind=='green':
  commands=[['code/verify.py'],['code/green_machine.py','--export-example','examples']];record='validation/results.json';versions=['python']
 else:commands=[['verify.py']];record='verification.json';versions=[]
 for cmd in commands:command([sys.executable,*cmd],root)
 saved=json.loads(original[root.name+'/'+record]);actual=json.loads((root/record).read_text())
 for name in versions:saved.pop(name);actual.pop(name)
 need(exact(saved,actual),'Author receipt differs outside runtime metadata');exported=[]
 for name,data in original.items():
  if '/examples/' in name:
   rel=Path(name).relative_to(root.name);need((root/rel).read_bytes()==data,'Valid export differs: '+str(rel));exported.append(str(rel))
 return dict(commands=commands,checks=actual['checks'] if kind=='green' else actual['total_checks'],normalized_fields=versions,byte_identical_exports=exported)

def green_checks(m):
 counts=Counter();p=m.Program((('inc',1,1),('test',0,2,3),('test',1,0,3),('halt',)))
 for state,a,b,h in product(range(4),range(3),range(3),range(20)):
  c=m.Config(state,a,b,h);succ=p.step(c);pred=p.predecessor(c)
  need(succ is None or p.predecessor(succ)==c,'Successor inverse');need(pred is None or p.step(pred)==c,'Predecessor inverse');counts['history_labels']+=1
 for initial in range(9):
  p=m.Program((('test',0,0,1),('halt',)));s=m.Config(0,initial,2)
  for alpha in (3,4,7,13):
   charge,vector=m.certificate(p,s,alpha,initial+1);tr,_=m.run(p,s,initial+1)
   # Independently solve the finite linear equations by exact elimination.
   n=len(tr);A=[[Fraction(alpha if i==j else -1 if abs(i-j)==1 else 0) for j in range(n)]+[Fraction(i==0)] for i in range(n)]
   for k in range(n):
    pivot=A[k][k];A[k]=[v/pivot for v in A[k]]
    for i in range(n):
     if i!=k:
      scale=A[i][k];A[i]=[a-scale*b for a,b in zip(A[i],A[k])]
   need(all(Fraction(vector[v],charge)==A[i][-1] for i,v in enumerate(tr)),'Exact inverse column mismatch');counts['independent_linear_solves']+=1
   support=tr+[m.Config(1,90,90)];names,rows=m.slice_rows(p,s,alpha,support)
   values={**{f'u{i}':vector.get(v,0) for i,v in enumerate(support)},'q':charge}
   need(m.rows_value(names,rows,values)==0 and m.check_certificate(p,s,alpha,charge,vector),'Complete finite certificate')
   for name in names:
    bad=dict(values);bad[name]+=1;need(m.rows_value(names,rows,bad)>0,'Unbound finite coordinate');counts['coordinate_mutations']+=1
   for bits in (0,3,17,60):
    lo,hi=m.green_interval(p,s,alpha,bits);need(lo<=A[0][-1]<=hi and hi-lo<=Fraction(1,2**bits),'Rational interval');counts['rational_enclosures']+=1
 divergent=m.Program((('inc',0,0),('halt',)));source=m.Config(0,0,0)
 for length in range(1,13):
  trace,_=m.run(divergent,source,length-1);ds=m.continuants(3,length);v={x:ds[length-1-i] for i,x in enumerate(trace)}
  applied=m.apply_l(divergent,3,v);need(applied=={source:ds[length],divergent.step(trace[-1]):-1},'Exterior leakage omitted');counts['exact_exterior_leakage']+=1
 return dict(counts=dict(counts))

def connected_checks(m):
 counts=Counter();p=m.transfer();rng=random.Random(20261003)
 for n in range(350):
  v=m.decode_node(p,n);need(m.encode_node(p,v)==n,'Exact graph enumeration');counts['node_codes']+=1
  for kind in range(4):
   k=4*n+kind;nb=m.connected_neighbors(p,k);need(len(nb)<=3 and all(k in m.connected_neighbors(p,w) for w in nb),'Connected symmetry');need(set(map(m.swap,nb))==set(m.connected_neighbors(p,m.swap(k))),'Rail symmetry');counts['connected_vertices']+=1
 for c in product(range(4),repeat=2):
  T=2*c[0]+1;cert=m.compile_certificate(p,T);v=m.canonical_assignment(p,c,T);charge,net=m.canonical_network_certificate(p,c,T)
  root=4*m.encode_node(p,p.root(c));need(m.apply_operator(p,net)=={root:charge,root+1:-charge},'Dipole exterior equations');counts['full_dipole_certificates']+=1
  need(cert.energy(v)==0,'Unique finite witness');poly=cert.expanded()
  for _ in range(8):
   point={n:rng.randrange(-4,5) for n in cert.variables+cert.parameters};out=sum(coef*product_value([point[n] for n in mon]) for mon,coef in poly.items())
   need(cert.energy(point,natural=False)==out,'All-value quadratic expansion');counts['signed_full_polynomials']+=1
 for m0 in (3,5,7,13):
  for ps in ((),(2,),(3,),(2,3,5),(5,19,29)):
   info=m.localization_bound(m0,ps);B=info['first_excluded_length']
   for length in range(1,max(B+8,36)):
    value=m.continuant(m0,length);rest=value
    for prime in ps:
     while rest%prime==0:rest//=prime
    need(rest!=1 or length<B,'Finite-prime bound');counts['localization_lengths']+=1
 return dict(counts=dict(counts))

def product_value(xs):
 value=1
 for x in xs:value*=x
 return value

def defect(m):
 p=m.countdown();cert=m.compile_certificate(p,3);v=m.canonical_assignment(p,(2,),3);v['x0']=99;before=cert.energy(v)
 exported=cert.export();next(r for r in exported['linear_residuals'] if 'x0' in r).clear();after=cert.energy(v)
 try:m.localization_bound(5,[2,2.0]);prime_alias_accepted=True
 except (ValueError,TypeError):prime_alias_accepted=False
 return dict(wrong_input_energy_before=before,wrong_input_energy_after_export_mutation=after,inexact_prime_alias_accepted=prime_alias_accepted)

def repaired_checks(m):
 counts=Counter();d=defect(m);need(d==dict(wrong_input_energy_before=9409,wrong_input_energy_after_export_mutation=9409,inexact_prime_alias_accepted=False),'Original defect not repaired')
 def reject(fn):
  try:fn()
  except (TypeError,ValueError,AttributeError):counts['rejected_calls']+=1;return
  raise ValueError('Malformed or mutable boundary accepted')
 p=m.countdown();cert=m.compile_certificate(p,3);v=m.canonical_assignment(p,(2,),3)
 for row in cert.rows:reject(lambda row=row:row.__setitem__('x0',0))
 for flag in (0,1,None,'',[],1.0):reject(lambda flag=flag:cert.energy(v,natural=flag))
 for ps in ([2,2.0],[2.0,2],[2,True],[2,3.0],[False],[4],['2']):
  reject(lambda ps=ps:m.localization_bound(5,ps));reject(lambda ps=ps:m.smooth(12,ps));reject(lambda ps=ps:m.localized_membership(p,(2,),ps))
 raw=[{'x':1,'':-2}];cross=[['x','x']];names=['x'];q=m.Certificate(names,[],raw,cross)
 raw[0].clear();cross[0][0]='missing';names[0]='missing';need(q.energy({'x':2})==4,'Constructor did not snapshot');counts['constructor_snapshots']+=1
 for row in ({'x':True},{'x':1.0},{'missing':1},{None:1}):reject(lambda row=row:m.Certificate(('x',),(),(row,),()))
 for pair in (('x','missing'),('x',),('x',1)):reject(lambda pair=pair:m.Certificate(('x',),(),(),(pair,)))
 for names in (('x','x'),('x',True),('',)):reject(lambda names=names:m.Certificate(names,(),(),()))
 return dict(original_defect_replay=d,counts=dict(counts))

def verify(green_archive,connected_archive,patch):
 patch=Path(patch);need(hashlib.sha256(patch.read_bytes()).hexdigest()==PATCH_SHA,'Patch pin')
 with tempfile.TemporaryDirectory(prefix='coercive-connected-review-') as tmp:
  base=Path(tmp);g=extract(Path(green_archive),base,ARCHIVES[0]);w=extract(Path(connected_archive),base,ARCHIVES[1]);gr=base/'Coercive_Green_Diophantine';wr=base/'well_conditioned_diophantine'
  ga=author(gr,g,'green');wa=author(wr,w,'connected')
  with module(gr/'code/green_machine.py','_independent_green') as m:gc=green_checks(m)
  with module(wr/'src/substrate.py','_independent_connected') as m:
   wc=connected_checks(m);before=defect(m)
  need(before==dict(wrong_input_energy_before=9409,wrong_input_energy_after_export_mutation=0,inexact_prime_alias_accepted=True),'Original defect fixture changed')
  repaired=base/'repair'/'well_conditioned_diophantine';shutil.copytree(wr,repaired)
  command(['patch','-p1','--batch','--forward','-i',str(patch.resolve())],repaired)
  need(hashlib.sha256((repaired/'src/substrate.py').read_bytes()).hexdigest()==PATCHED_SOURCE_SHA,'Patched source pin')
  ra=author(repaired,w,'connected')
  with module(repaired/'src/substrate.py','_independent_connected') as m:rc=repaired_checks(m)
 return dict(status='PASS_COERCIVE_CONNECTED_REVIEW',archives=ARCHIVES,patch_sha256=PATCH_SHA,patched_source_sha256=PATCHED_SOURCE_SHA,coercive=dict(author=ga,independent=gc),connected=dict(author=wa,independent=wc,original_defects=before,repaired_author=ra,repair_checks=rc),scope='Full two articles and all substantive modules read; finite original/independent tests, explicit API repairs; no fixed-arity ordinary universal polynomial or new87 operation bound.')

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--green-archive',type=Path,required=True);p.add_argument('--connected-archive',type=Path,required=True);p.add_argument('--patch',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();out=verify(a.green_archive,a.connected_archive,a.patch)
 if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Saved receipt differs')
 print(json.dumps(out,indent=2,sort_keys=True))
