from pathlib import Path
import re,json,hashlib,graphlib
R=Path.cwd();D=R/'Computability/DiophantineConsistency/reviews/ipra-quartic-native-generic-replay';root=R/'Computability/DiophantineConsistency/Lean';names={'DiophantineConsistency.'+n for n in ['PositiveOffsetCore','PositiveOffsetSyntaxDegree','PositiveOffsetSyntaxDegreeChecks','PositiveOffsetArithmetic','PositiveOffsetArithmeticChecks','IPRAQuarticExpressionCore','IPRAQuarticPositiveCore','IPRAQuarticExpressionBridge','IPRAQuarticExpressionBridgeChecks','IPRAQuarticPositiveBridge','IPRAQuarticPositiveBridgeChecks','IPRAQuarticDegree','IPRAQuarticDegreeChecks','HAExpressionNoZeroEquiv','PRAExpressionZFCStrict','IPRAExpressionNative','IPRAQuarticNativeBridge','IPRAQuarticNativeBridgeChecks']}
def h(b):return hashlib.sha256(b).hexdigest()
sources={};graph={}
for n in names:
 p=root/(n.replace('.','/')+'.lean');raw=p.read_bytes();imports=re.findall(r'^import\s+([A-Z][\w.]*)',raw.decode(),re.M);graph[n]=[x for x in imports if x in names];dest=D/'sources'/(n.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw);sources[n]={'path':str(p.relative_to(R)),'sha256':h(raw),'imports':imports}
order=list(graphlib.TopologicalSorter({n:graph[n] for n in sorted(names)}).static_order());assert len(order)==18 and len(set(order))==18
for n,v in sources.items():assert h((R/v['path']).read_bytes())==v['sha256']
prev=R/'Computability/DiophantineConsistency/reviews/ipra-quartic-model-bridge-replay-v2';prior=json.loads((prev/'manifest.json').read_text()); retained={n:v for n,v in prior['sources'].items() if n not in sources};assert len(retained)==19
for n,v in retained.items():assert h((R/v['path']).read_bytes())==v['sha256'],('retained source drift',n)
out={'status':'FROZEN_FOCUSED_INPUT','sources':sources,'order':order,'retained_parent_sources':retained,'parent_receipt_sha256':h((prev/'receipt.json').read_bytes()),'parent_observation_sha256':h((prev/'terminal-observation.json').read_bytes()),'boundary':'Focused source-directed suffix on the matched quartic-model peer; original-expression bridge is an explicit premise. Project, external transitive, dynamic import and 848-ancestor provenance remain inherited.'};(D/'manifest.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print('FROZEN',len(order),h((D/'manifest.json').read_bytes()),*order,sep='\n')
