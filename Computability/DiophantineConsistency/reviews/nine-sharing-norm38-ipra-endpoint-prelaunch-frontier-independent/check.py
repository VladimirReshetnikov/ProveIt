import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2]; p=D/'research/nine-sharing-norm38-ipra-endpoint-check'; old=D/'research/nine-sharing-norm38-ipra-endpoint-draft/Norm38IPRAEndpoint.lean'
def sha(q): return hashlib.sha256(q.read_bytes()).hexdigest()
pins={'run.py':'4633e1a32cf0ba7781591752a6ca787e810e435e1715426b6cbdbc452711514f','provider_survey.py':'8bd2615b3ea82c9af474d83355d17b4854d659c5dc358f21fbc7147d27122367','source-manifest.json':'ddb6795c743fe3a72e5c5426b0eb908519c8f541eebb21c761b20446fdc4f7ef','src/DiophantineConsistency/Norm38IPRAEndpoint.lean':'fe84dc25c6d4bb7c7ebfa06d1ff28d622f607c58dc1a4338214e0a40314a7f0c'}
for k,v in pins.items(): assert sha(p/k)==v,k
assert sha(old)==pins['src/DiophantineConsistency/Norm38IPRAEndpoint.lean']
manifest=json.loads((p/'source-manifest.json').read_text()); rows=manifest['rows']; assert len(rows)==1
imports=rows[0]['imports']; assert imports==['DiophantineConsistency.'+n for n in ['Norm38CurrentCastFreeIff','HACurrentEquation2011','IPRAExpressionNative','IPRAStandardTheory']]
survey=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60)); assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'; assert all(x in survey['selected'] for x in imports); assert len(survey['links'])==1162; assert not any(x.endswith('/Norm38IPRAEndpoint.olean') for x in survey['links'])
assert survey['selected'][imports[0]]['sha256']=='9a2021036f3598cccb7c9128f858544a33b985c5aa9f7463f39eefac430135f8'
pre=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60)); assert pre['status']=='PASS_NO_LEAN_PREFLIGHT' and pre['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','source_and_runner_pins':pins,'direct_producers':{x:survey['selected'][x] for x in imports},'overlay_link_count':len(survey['links']),'preflight':pre,'scope':'No Lean endpoint compilation, complete transitive trace, or literal equation/degree binding.'},indent=2,sort_keys=True))
