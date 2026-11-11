from pathlib import Path
import hashlib,itertools,json,re,subprocess,sys
root=Path(__file__).resolve().parents[2];d=root/'research/nine-sharing-sign14-positive74-triple-quadratic-search'
pins={'README.md':'a96c9e2d6d81ffc79533ec1ca55e8ff66da3175cbf80165e9451ca9ca070adb6','search.py':'84cabb5ec32342c7fef1ce8041151334a5207a02726a128c9ec3e1dc67e31e14','result.json':'dd37cf70cf6240202d4ffce97e5ce2e2bd9f1e3cdfe076890eaa5b00b9916eac'}
for n,h in pins.items():assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h,n
result=json.loads((d/'result.json').read_text());actual=subprocess.check_output([sys.executable,'-I','-S','-B',str(d/'search.py')],cwd=root.parents[1]);assert json.loads(actual)==result
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-circuit-retry01-terminal-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
source=root/'research/nine-sharing-sign14-positive74-circuit-retry01-check/src/DiophantineConsistency/Sign14Positive74Circuit.lean';assert hashlib.sha256(source.read_bytes()).hexdigest()=='cdd4117cd0b8af7eefbca2d53388068350970f78dba7e73dc9be2fe1b51f105d';text=source.read_text().split('def gates : List Gate := [',1)[1].split(']\ndef parents',1)[0];g=re.findall(r'⟨\.(add|sub|mul), \.(var|port|lit|reg) (-?\d+), \.(var|port|lit|reg) (-?\d+)⟩',text);assert len(g)==74
roots=(23,41,48,61,64);assert all(g[i][0]=='sub' for i in roots)
for i,k in enumerate(roots):assert g[65+i]==('mul','reg',str(k),'reg',str(k))
assert g[70]==('add','reg','65','reg','66') and g[71]==('add','reg','70','reg','67') and g[72]==('add','reg','71','reg','68') and g[73]==('add','reg','72','reg','69')
# Independently check Sylvester minors and exact homogeneous quadratic coefficients.
forms=[];rejected=[];basis=[(1,0,0),(0,1,0),(0,0,1),(1,1,0),(1,0,1),(0,1,1)]
for b,c,d0 in itertools.product((-1,0,1),repeat=3):
 A=4-b*b;D=8-2*(b*b+c*c+d0*d0)+2*b*c*d0
 if D<=0:rejected.append((b,c,d0,D));continue
 assert 2>0 and A>0 and D>0
 for x,y,z in basis:
  Q=x*x+y*y+z*z+b*x*y+c*x*z+d0*y*z
  assert 4*A*Q==A*(2*x+b*y+c*z)**2+(A*y+(2*d0-b*c)*z)**2+2*D*z*z
 forms.append((b,c,d0))
assert len(forms)==23 and len(rejected)==4 and all(x[-1]==0 for x in rejected)
assert result['coefficient_forms']==23 and result['residual_triples']==10 and result['baseline_live_gates']==74 and result['search_stats']=={'form_tests':230,'matching_recipes':1053,'trees_counted':3159,'hits_under_74':0,'zero_sample_targets':0} and result['hits']==[]
print(json.dumps({'status':'PASS_INDEPENDENT_SEARCH_AUDIT','positive_definite_forms':23,'triples':10,'receipt_reproduced':True,'scope':'Bounded modular prefilter only; no global minimality, new Lean result or PDF binding'},indent=2))
