"""Pinned portable review of the eager-tree archive; no giant scalar expansion."""
from __future__ import annotations
import argparse,copy,hashlib,importlib.util,json,random,shutil,subprocess,sys,tempfile
from pathlib import Path
PINS={'README.md': 'a987fb2ec540488ecfcd1b241a98605e85e12cfe13ebcf7f589b79030171db9f', 'VERIFICATION.md': '63a5d5da9669786b84ada4e1e96c36bd7ce92a99406cb11b613763c657f99e32', 'eager-tree-certificates.pdf': '0e4c72feddf5b0187b6d055db273355e57012a5552bfe919ace18207577ca19f', 'eager-tree-certificates.tex': '196e6fbebcdeceaa81c3356682ef5325b0a4faae093167414465f30371e92c31', 'build_pdf.py': '4d569c117355863b72c11292a695c13aef339fd39d9144fa462b55fd5e10a294', 'reproduce.py': '21104c49f48a7c818da2f9b9ea0b48879f736397ecef334f9e4fda1b86bbdcce', 'verify_manifest.py': '84d491ac994b82b6f07ae25c407877c9eb685423a015395d1776b08c5792f110', 'requirements-optional.txt': '5c17f2bd0ca0626fc3633b97c10741b33c018ca229c4c073ca1d7a94e5a9b909', 'sources.json': '7bcf24542682be538f27df8cba77ceae7982863d830ae27abd64b1eec45b5a3a', 'code/analyze_growth.py': '564ddcf01d0b979bcd684b514538568c90267a13f93c28a62aee01d19f30be94', 'code/audit_exact_count.py': '1a40fa46fc1f949a8dfacc606d4c5173b967439ab7e0e62f9a55b7b0dfda6c9b', 'code/audit_exact_count_receipt.json': 'd1d8996a31f07cdf52e907775862f38c71add9eee2890717ff98adc7a0845004', 'code/canonical.py': '42e4abaeb77da1842e70e2e9245584f18dd6fdfbf9094b0a62f4ea5b8a9b41bd', 'code/canonical_identity.json': '19c30d63c48ed4126091f73478a72ef4a39d257a5e61b15b696a8318aaf64721', 'code/canonical_overlay_audit.py': '661666842650cf2703253bedf9b58ed15f07042dc77db1d7aadc1b247af3ca81', 'code/canonical_overlay_receipt.json': '2b725672ec92082f5c93d1a8cbdd7bf8815834e1affa1747e79b8fe9d470a9a1', 'code/canonical_projected.py': '17ec7345bce074233b4fbbf295a9630233af9e6788f790a1f23201100fa2fa19', 'code/canonical_projected_audit.py': 'c23980869fd66f26bb162b39f7e9910bb52c7359ffb0c40a938654f94d05acb7', 'code/canonical_projected_audit_receipt.json': '52a0c98f3817e5ac290e0c34a8c10b29603c0aee77917dd05cac20cee7b82b7b', 'code/canonical_projected_identity.json': '2255d1f3649db71fc71fa920199c4d3adff38631690b0840efb383f149412f18', 'code/canonical_projected_receipt.json': 'f1f66a6c593e16d107a897124f557e9bf387d1e0db7f793c685d16235a604923', 'code/canonical_receipt.json': '6aacfbedbcd57e0c33cb9dc3b7476f8b3596245fab8e6a7eb876303c6519ca1a', 'code/constant_bit_bound.json': 'b7ff2d6b73bb61b9c92e5bd41cc65799d0a0b4b330774d4f35030f658e31e692', 'code/constant_bit_bound.py': '748e916caa6d4ddeca6ae44d9ff9e96fffda0d84d6803fee3f6a602bcd6d2b16', 'code/counter_source.py': '637f135a0c2152a0bd319c2eb376fe8c7b295f0a31b1a2c408aebfbd227d040d', 'code/counter_source_receipt.json': 'd196967b246dd54176c24a3061687a4dead0b0f2b593f549fb3cef0abaad11ef', 'code/cyclic_counterfeit.json': 'c9d1f38be4c64f8f29033f40afdd6bdc20d807560538be8c8c87d24be3e728cf', 'code/eager_compiler.py': '156624d1288c9167f8bfc6b1ed91564f10d5199f2d07c0fd4759ffed2f90c164', 'code/eager_compiler_receipt.json': 'b5f762a3d999314994e39650bad3c4a1619a878f2df952f079141ede8b591ff9', 'code/exact_growth_receipt.json': '778bd44c495474a94d6c4a57ad7895d2c4dce689ce4cf3dc7260148f0bd75712', 'code/export_shared_macro.py': 'f65a03c41e50e7b4ec6f3ca5c4a2c856ff3546539e683fdf9a86e82d3d9db58c', 'code/identity_certificate.json': 'bf243cebec4fd892960448702b1d76f241492b8358ecba2e89feba151d6d37a4', 'code/independent_audit.py': 'c3c34619e96ae499ba904282b453509994f5fad0adfaa99d32e45a57e74d3c75', 'code/independent_compiler_audit.py': '8eaae0232b1cf2a5ec42299b7e33d44f40f1d637b4ff0061034e55337e4575fb', 'code/independent_compiler_receipt.json': 'a1cbe11a17bbb7e3fcc1b897c826acb05d074bc7c491ba219ac9cc1bbbc8da86', 'code/independent_growth_audit.py': '21575c28e160a530cec9db648e4f4ba9a3065872051ae935452eb001bc74f288', 'code/independent_growth_receipt.json': '29294112cf84c1ce1754ec7bbb3d835ce006278f87387f9858a4e99858d8f239', 'code/independent_receipt.json': 'aea2b75bfe0f018e4f643af867211f95220c13b6673fd97224600e19449e6d46', 'code/independent_shared_audit.py': '4f7dc4bd64b38d0022f4b4470ff5bd1d4adb39ee42b2812aba40e903a8c726bd', 'code/independent_shared_receipt.json': '240dbadaca3126f585080757bbf6b06964366773686ff58f2d397f0846b521a2', 'code/literal_universal_tree.json': 'c6b647090cfc99e32f6a097e89dee8bab68f2be9a2ab3cbd5da222f6d0f70823', 'code/literal_universal_tree.sexpr': '6c8a9e8d33c76c72f106479bb37d18867e586cb8171aa4b91f136b8da6b34d69', 'code/packet_assumptions_receipt.json': '4c22cdd7ce4c29ccf63557323121154ad9e3a3f9076670f364a303ae50782b0a', 'code/receipt.json': 'cf25eb544bdf0a372e612dd034284664d43f59478e06b28bb07fd47b6d0fb73d', 'code/shared_compression.py': '37f6d785a212f5bad2f76dc8bddc640bb42e329e3f37f01d1e7ad13dbe4a81e8', 'code/shared_compression_program.json': 'f136280be791e6199064c960b5cc5f9ea6b8634392b36cacfae8d40a10a6bc74', 'code/shared_compression_receipt.json': '16e4c9888abf074c68d6498f4cf5698b02599678cb08e12151db64def2d10f85', 'code/shared_symbolic_proofs.json': '0341fdacffda5964705b1a0aadd7b84693b66328009198c65c882952c253e2c1', 'code/symbolic_audit.py': '79564e510bbb2a722ad7fa3c6a8a36fdaa6b29143bf77cc3618cd2b228204050', 'code/symbolic_receipt.json': '1ca2782bdeae292388a1a683425ea419fc39e019d42ae5833039ec032956b3d9', 'code/tree_kernel.py': 'f7a6433758b1d7167f1a7ff6f52f12b7348b60c714069884090b11187f2a8dcb', 'code/universal_code_circuit.json': '3528ad35d5d1ea99ac92c3d8af0f23f9ca3f2c129b0ad281fa2056f468e3e3b1', 'code/universal_lambda_source.json': 'a9aa268fe9052ebef2cbf368450d26be2b3d629fa34a05123f005d2cbad0e316', 'code/verify_packet_assumptions.py': '09fbcc859f0c561d6103ae6a81c63503116c5422ecda3a3740362906a1d648d0', 'code/verify_shared_macro.py': 'ea7188b2e29ebfe10d34481d6d438584951882d89d471feaf93dfeedc7267bae', 'MANIFEST.sha256': '8d332462fa6259862d0908984b31131ebdc2f1b728d8a50f81491c1cb4c94c88'}
PATCH_SHA='bb669fe7b71621d6fbe968ce8ed5833092dee996e262a78a6471f0aeb9bccdfe'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def same(a,b):return type(a) is type(b) and (a.keys()==b.keys() and all(same(a[k],b[k]) for k in a) if isinstance(a,dict) else len(a)==len(b) and all(same(x,y) for x,y in zip(a,b)) if isinstance(a,list) else a==b)
def load(p,name):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def manual(rows,p,n,o):
 def f(a,b):return a*a+2*a*b+b*b+a+3*b+2
 out=[];N=len(rows)
 for r in rows:
  x,y,z,h,a,b,c,u,v,d,e,q,j,k=[r[f] for f in ('x','y','z','h','a','b','c','u','v','d','e','q','j','k')]
  t0,t1,t2,t3,t4=r['t'];active=t3+t4
  out += [sum(r['t'])-1,d-f(a,b),e-f(a,y),q-f(0,b),j-f(2*a+1,b),k-f(d,c),x-t1*(2*a+1)-t2*q-t3*j-t4*k,t0*(z-2*y-1),t1*(z-e),t2*(z-b)]
  out += [sum(r['pointers'][0])-active,sum(r['pointers'][1])-active,sum(r['pointers'][2])-t3]
  target=((t3*b+t4*y,t3*y+t4*a,active*u),(t3*a+t4*u,t3*y+t4*b,t3*v+t4*z),(t3*u,t3*v,t3*z))
  for slot in range(3):
   for col,field in enumerate(('x','y','z')):out.append(sum(r['pointers'][slot][j]*rows[j][field] for j in range(N))-target[slot][col])
  out.append(h-1-sum(r['pointers'][s][j]*rows[j]['h'] for s in range(3) for j in range(N)))
 return out+[rows[0]['x']-p,rows[0]['y']-n,rows[0]['z']-o]

def run(root,patch,authors=False):
 if not __debug__:raise RuntimeError('review requires assertions enabled')
 root=Path(root);patch=Path(patch)
 for f,h in PINS.items():
  if sha(root/f)!=h:raise ValueError('source/member hash mismatch: '+f)
 if sha(patch)!=PATCH_SHA:raise ValueError('patch hash mismatch')
 out={'archive_sha256':'5c6c100296a58df366939febf2f7b6ca57616f17f77a71520f6f3a5e20204ab4','source_pins':PINS,'patch_sha256':PATCH_SHA,'checks':{}};counts=out['checks']
 def check(k,v):assert v,k;counts[k]=counts.get(k,0)+1
 k=load(root/'code/tree_kernel.py','tree_kernel_review_original')
 e=k.Evaluation();check('original_negative_argument',e.app(0,-1)==-1)
 e=k.Evaluation();e.app(0,True);e.app(0,1);check('original_boolean_cache_pollution',not k.valid_domain(k.certificate(e,(0,1)),0,1,3))
 with tempfile.TemporaryDirectory(prefix='eager-review-') as tmp:
  fixed=Path(tmp)/'fixed';shutil.copytree(root,fixed)
  subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(patch.resolve())],cwd=fixed,check=True,capture_output=True,timeout=240)
  q=load(fixed/'code/tree_kernel.py','tree_kernel_review_fixed');out['patched_source_sha256']=sha(fixed/'code/tree_kernel.py')
  for bad in (-1,True,1.0):
   for slot in (0,1):
    for warm in (False,True):
     e=q.Evaluation()
     if warm:e.app(1,1)
     args=[1,1];args[slot]=bad
     try:e.app(*args)
     except ValueError:check('patched_input_rejections_before_cache',True)
     else:raise AssertionError('invalid natural code accepted')
     check('valid_reuse_after_rejection',e.app(0,1)==3 and q.valid_domain(q.certificate(e,(0,1)),0,1,3))
  rng=random.Random(9901)
  for N in range(1,7):
   for case in range(12):
    rows=[]
    for i in range(N):
     r={f:rng.randrange(8) for f in q.SCALARS};r['t']=[rng.randrange(3) for _ in range(5)];r['pointers']=[[rng.randrange(3) for _ in range(N)] for s in range(3)];rows.append(r)
    pub=[rng.randrange(8) for _ in range(3)];result=q.polynomial(rows,*pub);rs=manual(rows,*pub)
    check('all_tuple_residual_identity',result['residuals']==rs and result['value']==sum(x*x for x in rs))
    check('literal_paid_counts',result['witnesses']==3*N*N+19*N and result['residual_count']==23*N+3 and result['polynomial_gates']=={'M':12*N*N+56*N+3,'A':15*N*N+69*N+5})
  for x in range(20):
   for y in range(9):
    old=k.Evaluation();e=q.Evaluation();z=e.app(x,y);check('valid_generator_unchanged',old.app(x,y)==z and k.certificate(old,(x,y))==q.certificate(e,(x,y)))
    rows=q.certificate(e,(x,y));check('manual_sound_zero',not any(manual(rows,x,y,z)))
    tree,h=q.structural_app(q.decode(x),q.decode(y),[10000]);check('independent_structural_result',q.encode(tree)==z and h==rows[0]['h'])
  # The public polynomial boundary rejects mutations of every numeric category.
  e=q.Evaluation();e.app(10,10);rows=q.certificate(e,(10,10))
  for field in q.SCALARS:
   for bad in (-1,True,1.0):
    altered=copy.deepcopy(rows);altered[0][field]=bad
    check('polynomial_bad_scalar_rejected',not q.valid_domain(altered,10,10,10))
  for category in ('t','pointers'):
   for bad in (-1,True,1.0):
    altered=copy.deepcopy(rows)
    if category=='t':altered[0]['t'][0]=bad
    else:altered[0]['pointers'][0][0]=bad
    check('polynomial_bad_selector_rejected',not q.valid_domain(altered,10,10,10))
  for output in (0,1,1014,10**80):
   rows=q.cyclic_counterfeit(output);rs=manual(rows,1014,1014,output)
   check('cyclic_counterfeit_independent',sum(t*t for t in rs)==81 and [t for t in rs if t]==[-9])
  # Read literal constructor DAGs independently and propagate rigorous intervals.
  out['literal_programs']={}
  for filename,expected in [('literal_universal_tree.json',175),('shared_compression_program.json',108)]:
   d=json.loads((root/'code'/filename).read_text());bounds=[];exact=[];sizes=[];tags={}
   for i,row in enumerate(d['nodes']):
    tag,*children=row;assert tag in ('L','S','F') and len(children)=={'L':0,'S':1,'F':2}[tag]
    assert all(type(j) is int and 0<=j<i for j in children);tags[tag]=tags.get(tag,0)+1
    if tag=='L':v=0;lo=hi=0
    elif tag=='S':
     lo,hi=[a+1 for a in bounds[children[0]]];v=None if exact[children[0]] is None else 2*exact[children[0]]+1
    else:
     lo=max(2,2*max(bounds[j][0] for j in children)-1);hi=2*max(bounds[j][1] for j in children)+3
     a,b=[exact[j] for j in children];v=None if a is None or b is None else (a+b)*(a+b+1)+2*b+2
    if v is not None:lo=hi=v.bit_length()
    exact.append(v if hi<=4096 else None);bounds.append((lo,hi));sizes.append(1+sum(sizes[j] for j in children))
   check('literal_dag_and_bit_interval',len(d['nodes'])==expected and exact[d['root']] is None)
   out['literal_programs'][filename]={'nodes':expected,'tags':tags,'expanded_size':sizes[d['root']],'hybrid_bit_interval':list(bounds[d['root']])}
  if authors:
   original=Path(tmp)/'original';shutil.copytree(root,original)
   subprocess.run([sys.executable,'verify_manifest.py'],cwd=original,check=True,capture_output=True,timeout=240)
   records=[]
   hashes={PINS['code/tree_kernel.py'],out['patched_source_sha256']}
   def norm(x):
    if isinstance(x,str) and x in hashes:return '<tree_kernel source digest>'
    if isinstance(x,dict):return {k:norm(v) for k,v in x.items()}
    if isinstance(x,list):return [norm(v) for v in x]
    return x
   for path in (original,fixed):
    subprocess.run([sys.executable,'reproduce.py','--symbolic'],cwd=path,check=True,capture_output=True,text=True,timeout=300)
    summary=json.loads((path/'replay-output/replay-summary.json').read_text());check('nineteen_author_scripts',len(summary)==19 and all(r['returncode']==0 for r in summary))
    records.append({f.name:norm(json.loads(f.read_text())) for f in sorted((path/'code').glob('*.json'))})
   archived={f.name:norm(json.loads(f.read_text())) for f in sorted((root/'code').glob('*.json'))}
   check('all_saved_json_reproduced',same(archived,records[0]));check('all_patched_json_semantics_unchanged',same(*records))
   out['author_json']=records[0]
   for f in ('identity_certificate.json','canonical_identity.json','canonical_projected_identity.json','literal_universal_tree.json','shared_symbolic_proofs.json','universal_code_circuit.json'):
    check('key_exports_byte_identical',(original/'code'/f).read_bytes()==(fixed/'code'/f).read_bytes()==(root/'code'/f).read_bytes())
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',required=True,type=Path);p.add_argument('--patch',required=True,type=Path);p.add_argument('--authors',action='store_true');p.add_argument('--output',required=True,type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=run(a.root,a.patch,a.authors)
 if a.expect and not same(r,json.loads(a.expect.read_text())):raise AssertionError('receipt mismatch')
 a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps(r['checks'],sort_keys=True))
if __name__=='__main__':main()
