from pathlib import Path
import re,json,hashlib,shutil,graphlib
R=Path.cwd();D=R/'Computability/DiophantineConsistency/reviews/ipra-quartic-model-bridge-replay';roots=[R/'Computability/HilbertTenthProblem/Lean',R/'Computability/DiophantineConsistency/Lean']; names={'Diophantine.Common.PolynomialDegree','Diophantine.Common.PolynomialRenaming','Diophantine.Paper1982.Carries','Diophantine.Paper1982.Coding','Diophantine.Paper1982.Digits','Diophantine.Paper1982.Master1','Diophantine.Paper1982.Section4','Diophantine.Paper1984.Identities','Diophantine.Paper1984.Masking'}|{'DiophantineConsistency.'+n for n in ['SyntaxCoefficients','NaturalExpressionSemiring','QuarticCompilerCore','QuarticSyntaxCore','QuarticCompiler','GatesSemiring','QuarticSemiring','QuarticSyntax','IPRAQuarticModelBridge','IPRAQuarticModelBridgeChecks']}
def h(b):return hashlib.sha256(b).hexdigest()
sources={};graph={}
for n in names:
 ps=[r/(n.replace('.','/')+'.lean') for r in roots];p=next((p for p in ps if p.is_file()),None);assert p,n
 raw=p.read_bytes(); imports=re.findall(r'^import\s+([A-Z][\w.]*)',raw.decode(),re.M);graph[n]=[x for x in imports if x in names];dest=D/'sources'/(n.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw);sources[n]={'path':str(p.relative_to(R)),'sha256':h(raw),'imports':imports}
order=list(graphlib.TopologicalSorter({n:graph[n] for n in sorted(names)}).static_order()); assert len(order)==19 and 'DiophantineConsistency.IPRAQuarticModelBridgeChecks' in order
for n,v in sources.items():assert h((R/v['path']).read_bytes())==v['sha256']
manifest={'status':'FROZEN_FOCUSED_INPUT','sources':sources,'order':order,'boundary':'Source-directed focused compiler/refactor and model bridge; parent project, external transitive and dynamic import ancestry are inherited, not a complete current-source closure.'}
(D/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n');print('FROZEN',len(order),h((D/'manifest.json').read_bytes()),*order,sep='\n')
