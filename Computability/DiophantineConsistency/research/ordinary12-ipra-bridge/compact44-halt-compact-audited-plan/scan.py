#!/usr/bin/env python3
"""Point-in-time source/guard scan of a six-child extension of the audited author suffix."""
import hashlib,json,os,re,sys
from pathlib import Path
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent; DC=HERE.parents[2]; ROOT=DC.parents[1]; SEED=Path('/tmp/ipra-marked-suffix-final-build-01'); PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'); HIST=DC/'reviews/ha87-isolated-full-author-pass';AUDIT=DC/'reviews/compact44-marked-suffix-final-author-artifact-independent-audit';sys.path.insert(0,str(HERE));import diagnostic_policy as policy
NAMES=list(policy.EXPECTED)+['CompactHaltWord']; CLIENT_SHA='063ddd79f856d3e33ad16a6274289f14625c3e3935b415703aa74afc76f9526c'; RESULT_SHA='861109aea9162f2ba0573c640a0ba4dc1658e290ea7a620cdda39f1587695068'; PREFLIGHT_SHA='e121b14ea08ad2f008ce9a85918704c419d5f6f6af0d58466dfc8be3e5f65495'; STATE_SHA='84c3bc6f6c34c47e67278c43df8580444d32e2946844a4c40c31cfd747f33a90'; AUDIT_PINS={'CHECK.json':'5e9daa236d9925f30789488f65d5ad9a89516147231a1810577f78f873351d0e','terminal-observation.json':'2cf9a92f1a0d0a290d35958b094afb586404b9926d427d18c2d149da0b0480b8','audit.py':'3ef691af68a3065919a1da67539100898891781a73935ee65b23354db43409dc'}; SUF=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def need(x,m):
 if not x:raise ValueError(m)
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def state(p):
 if not os.path.lexists(p):return None
 need(p.is_file(),('dangling or nonregular',str(p)));return {'realpath':str(p.resolve(strict=True)),'sha256':H(p)}
def slots(stem):return {str(Path(str(stem)+s)):state(Path(str(stem)+s)) for s in SUF}
def verify(g):
 for p,v in g.items():need(state(Path(p))==v,('recorded guard changed',p))
result=SEED/'RESULT.json';pre=SEED/'preflight.json';st=HIST/'state.json'
for p,h in [(result,RESULT_SHA),(pre,PREFLIGHT_SHA),(st,STATE_SHA)]+[(AUDIT/n,h) for n,h in AUDIT_PINS.items()]:need(p.is_file() and H(p)==h,('pin drift',str(p)))
r=json.loads(result.read_text());v=json.loads(pre.read_text());a=json.loads((AUDIT/'CHECK.json').read_text());obs=json.loads((AUDIT/'terminal-observation.json').read_text());need(r['status']=='PASS_AUTHOR_ONLY_MARKED_SUFFIX' and len(r['steps'])==22 and all(type(x['compiler_exit']) is int and x['compiler_exit']==0 and x['reason'] is None for x in r['steps']) and a['status']=='PASS_INDEPENDENT_AUTHOR_ONLY_FINAL_SUFFIX_ARTIFACT_AUDIT' and a['result_sha256']==RESULT_SHA and a['source_modules']==22 and a['lean_launched'] is False and type(obs['audit_exit']) is int and obs['audit_exit']==0 and obs['receipt_sha256']==RESULT_SHA and obs['lean_launched'] is False,'invalid parent boundary');verify(r['final_direct_and_output_slots']);verify(v['direct_companion_slots'])
records=json.loads(st.read_text())['records'];rows=[];produced=set();direct={};targets={};baselines={}
for name in NAMES:
 module='DiophantineConsistency.'+name;source=HERE/(name+'.lean') if name==NAMES[-1] else DC/'Lean/DiophantineConsistency'/(name+'.lean');pin=CLIENT_SHA if name==NAMES[-1] else policy.EXPECTED[name][0];need(source.is_file() and H(source)==pin,('source drift',name));imports=re.findall(r'^import\s+([\w.]+)',source.read_text(),re.M);need(imports,('no imports',name));rows.append({'module':module,'source':str(source.relative_to(ROOT)),'sha256':pin,'imports':imports})
 if name!=NAMES[-1]:
  matches=[x for x in records if x.get('module')==module and x.get('source_sha256')==pin and x.get('exit')==0 and x.get('verified') is True];need(len(matches)==1,('bad historical record',name));x=matches[0];log=HIST/'logs'/x['log_file'];need(log.is_file() and H(log)==policy.EXPECTED[name][1] and len(x['warning_lines'])==policy.EXPECTED[name][2],('bad baseline',name));baselines[name]={'historical_log':str(log.relative_to(ROOT)),'source_sha256':pin,'log_sha256':H(log),'warning_count':len(x['warning_lines']),'compiler_exit':0,'verified_record':True}
 for dep in ['Init']+imports:
  if dep in produced:continue
  need(dep not in ['DiophantineConsistency.'+n for n in NAMES],('source out of order',module,dep))
  if dep not in direct:
   rel=Path(*dep.split('.')); cs=[{'root':str(base),'slots':slots(base/rel)} for base in (SEED/'lib',PKG)];objs=[c['slots'][str(Path(c['root'])/rel)+'.olean'] for c in cs];live=[x for x in objs if x is not None];need(live and len({x['sha256'] for x in live})==1,('missing or conflicting direct input',dep));direct[dep]=cs
 rel=Path(*module.split('.'));ts=[{'root':str(base),'slots':slots(base/rel)} for base in (SEED/'lib',PKG)];need(all(v is None for c in ts for v in c['slots'].values()),('target collision',module));targets[module]=ts;produced.add(module)
print(json.dumps({'status':'PASS_POINT_IN_TIME_AUDITED_SUFFIX_HALT_SOURCE_SCAN','seed':str(SEED),'seed_result_sha256':RESULT_SHA,'seed_preflight_sha256':PREFLIGHT_SHA,'audit_pins':AUDIT_PINS,'history_state_sha256':STATE_SHA,'sources':rows,'diagnostic_baselines':baselines,'direct_candidates':direct,'target_slots':targets,'lean_launched':False,'scope':'single-author source/slot scan; audit is point-in-time; inherited package/transitive ancestry unauthenticated'},indent=2,sort_keys=True))
