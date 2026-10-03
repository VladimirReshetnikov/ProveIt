#!/usr/bin/env python3
from pathlib import Path
import importlib.util,sys,hashlib,json,itertools,subprocess,argparse,tempfile,shutil
if not __debug__:
 raise RuntimeError('This development checker requires assertions; do not run Python with -O.')
parser=argparse.ArgumentParser(description='Replay pinned maximal-parallel constructor repair on a private copy.')
parser.add_argument('--original-root',type=Path,required=True)
parser.add_argument('--patch',type=Path,required=True)
parser.add_argument('--receipt',type=Path,required=True)
cli_args=parser.parse_args()
P=cli_args.original_root.resolve();patch=cli_args.patch.resolve()
assert hashlib.sha256((P/'code/parallel_certificates.py').read_bytes()).hexdigest()=='27cb3689fa8329f940055489756a977befd98ee2ab4b2c59651451d440f26111'
assert hashlib.sha256((P/'code/verify.py').read_bytes()).hexdigest()=='f65bf1ad71c6abaadb4c755634ea3a738b042af0d2df9ee93a12491136945f1a'
assert hashlib.sha256(patch.read_bytes()).hexdigest()=='eeea36e7beefaa9a3ebd4ee5f6686c56ddfcc1ae464f8c8027d26d2fc83bbfd6'
temp=tempfile.TemporaryDirectory(prefix='maximal-parallel-patch-')
NEW=Path(temp.name)/'patched';shutil.copytree(P,NEW)
proc=subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(patch)],cwd=NEW,timeout=300,capture_output=True,text=True)
assert proc.returncode==0,proc.stderr
assert hashlib.sha256((NEW/'code/parallel_certificates.py').read_bytes()).hexdigest()=='3562772c879ea092045d6963f13c35ccdcfd7f3e3605457dc6c3cb3a7c17d09b'
def load(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m
p=load('parallel_patch_original',P/'code/parallel_certificates.py')
n=load('parallel_patch_new',NEW/'code/parallel_certificates.py')
stats={};reject=0
class IntSubclass(int):pass
class FakeAtom:
 species=0;threshold=1;present=True
class ChildAtom(n.Atom):pass
for field,values in [('species',(-1,True,False,0.0,0.5,'0',None,IntSubclass(0))),('threshold',(-1,0,True,False,1.0,0.5,'1',None,IntSubclass(1))),('present',(0,1,2,-1,0.0,1.0,None,'yes',[],{}))]:
 for v in values:
  args=dict(species=0,threshold=1,present=True);args[field]=v
  try:n.Atom(**args)
  except (ValueError,TypeError):reject+=1
  else:raise AssertionError((field,v))
for atom in (FakeAtom(),ChildAtom(0,1),{'species':0},None,True,1):
 try:n.Network(((1,),),((0,),),((atom,),))
 except (ValueError,TypeError):reject+=1
 else:raise AssertionError('fake guard accepted')
for bad in (-1,True,False,0.0,0.5,'1',None,IntSubclass(1)):
 for side in (0,1):
  args=[((1,),),((0,),)];args[side]=((bad,),)
  try:n.Network(*args)
  except (ValueError,TypeError):reject+=1
  else:raise AssertionError('nonexact matrix')
for A,B,G in [((),(),()),(((),),((),),()),(((0,),),((0,),),()),(((1,0),),((0,),),()),(((1,),),(),()),(((1,),),((0,),),((),())),(((1,),),((0,),),((n.Atom(1,1),),)),(((1,),),((0,),),None)]:
 try:n.Network(A,B,G)
 except (ValueError,TypeError):reject+=1
 else:raise AssertionError('invalid shape')
stats['malformed_rejections']=reject
snapshots=exports=natural=0
for a,b,t,yes in itertools.product((1,2),(0,1),(1,2),(False,True)):
 A=[[a]];B=[[b]];G=[[n.Atom(0,t,yes)]]
 net=n.Network(A,B,G);c=n.RoundCertificate(net);before=json.dumps(c.as_dict(),sort_keys=True)
 # All nested and outer seeds mutated after compilation. Accepted network is fixed.
 A[0][0]=a+3;A.append([0]);B[0][0]=b+7;B.append([0]);G[0].clear();G.append([n.Atom(0,t,not yes)])
 assert net.consume==((a,),) and net.produce==((b,),) and net.guards==((n.Atom(0,t,yes),),)
 assert json.dumps(c.as_dict(),sort_keys=True)==before
 snapshots+=1
 for x in range(5):
  old=p.Network(((a,),),((b,),),((p.Atom(0,t,yes),),))
  for flat in (False,True):
   for keep in ((0,),(1,)):
    co=p.RoundCertificate(old,flat=flat,retention=keep);cn=n.RoundCertificate(net,flat=flat,retention=keep)
    assert json.dumps(co.as_dict(),sort_keys=True)==json.dumps(cn.as_dict(),sort_keys=True);exports+=1
    for f in range(5):
     wo=co.canonical_assignment((x,),(f,));wn=cn.canonical_assignment((x,),(f,));assert wo==wn
     if wn is not None:assert cn.polynomial.evaluate(wn)==0
     natural+=1
# Generator containers are consumed once into immutable values.
net=n.Network((iter(c) for c in ([1,0],[0,1])),(iter(c) for c in ([0,2],[2,0])),(iter(g) for g in ([n.Atom(0,1)],[n.Atom(1,1)])))
assert net.consume==((1,0),(0,1)) and type(net.consume) is tuple and all(type(c) is tuple for c in net.consume)
snapshots+=1
for t in range(4):
 for halt in (False,True):
  old=p.HistoryCertificate(p.Network(((1,),),((0,),)),t,first_halt=halt)
  new=n.HistoryCertificate(n.Network([[1]],[[0]]),t,first_halt=halt)
  assert json.dumps(old.as_dict(),sort_keys=True)==json.dumps(new.as_dict(),sort_keys=True);exports+=1
# Full-size exact integers, no floating or root count truncation.
a=10**200+7;x=10**500+9;b=10**150+11
old=p.RoundCertificate(p.Network(((a,),),((b,),)))
new=n.RoundCertificate(n.Network([[a]],[[b]]))
w=new.canonical_assignment((x,),(x//a,));assert w==old.canonical_assignment((x,),(x//a,)) and new.polynomial.evaluate(w)==0
stats.update(deep_network_snapshots=snapshots,valid_export_equivalences=exports,valid_canonical_assignments=natural,large_integer_case=1)
proc=subprocess.run([sys.executable,str(NEW/'code/verify.py')],timeout=300,capture_output=True,text=True)
assert proc.returncode==0,proc.stderr
comparison={}
for path in (P/'data').iterdir():
 if path.suffix=='.json':
  assert path.read_bytes()==(NEW/'data'/path.name).read_bytes()
  comparison[path.name]=hashlib.sha256(path.read_bytes()).hexdigest()
# Exact CLI example is regenerated independently; original source also repeated.
for base in (P,NEW):
 proc=subprocess.run([sys.executable,str(base/'code/parallel_certificates.py')],check=True,timeout=300,capture_output=True)
 assert proc.stdout==(P/'data/example_certificate.json').read_bytes()
stats['cli_exports_identical']=2
proc=subprocess.run(['patch','--batch','--fuzz=0','--dry-run','-p1','-i',str(patch)],cwd=P,timeout=300,capture_output=True,text=True)
assert proc.returncode==0
R={'status':'PASS','scope':'Exact constructor contract and immutable accepted inputs; no polynomial formula or theorem change. All checks finite.','original_compiler_sha256':hashlib.sha256((P/'code/parallel_certificates.py').read_bytes()).hexdigest(),'patched_compiler_sha256':hashlib.sha256((NEW/'code/parallel_certificates.py').read_bytes()).hexdigest(),'patch_sha256':hashlib.sha256(patch.read_bytes()).hexdigest(),'checks':stats,'author_json_files_unchanged':comparison,'patch_dry_run':proc.stdout}
cli_args.receipt.write_text(json.dumps(R,indent=2)+'\n');print(json.dumps(R,indent=2));temp.cleanup()
