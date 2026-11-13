#!/usr/bin/env python3
"""Point-in-time source/guard inventory for a proposed author-only six-child cut."""
import hashlib,json,os,re,sys
from pathlib import Path
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent; DC=HERE.parents[2]; ROOT=DC.parents[1]; SEED=Path('/tmp/ipra-supplied-marked-word-02'); OLD=Path('/tmp/ipra-marked-suffix-author-build-04'); PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'); HIST=DC/'reviews/ha87-isolated-full-author-pass';sys.path.insert(0,str(HERE));import diagnostic_policy as policy
NAMES=list(policy.EXPECTED)+['CompactHaltWordViaSupplied']; CLIENT_SHA='3594d4e2ac3a4e58aa45bf4a34766e39fed9e3361eefb19c3229ad2e1662072a'; RESULT_SHA='fa9e9981e46f620cabd851e478a69a57c2ba5f815084e9c8bf9ae6f82cdbd1ea'; PREFLIGHT_SHA='7cf9f43125da0e436bb74d15ce6399ad503b421bdb3135955ae972a0b18311f1'; STATE_SHA='84c3bc6f6c34c47e67278c43df8580444d32e2946844a4c40c31cfd747f33a90'; SUF=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
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
for p,h in [(result,RESULT_SHA),(pre,PREFLIGHT_SHA),(st,STATE_SHA)]:need(p.is_file() and H(p)==h,('pin drift',str(p)))
r=json.loads(result.read_text());v=json.loads(pre.read_text());need(r['status']=='PASS_SUPPLIED_MARKED_WORD_AUTHOR_EXPLORATION' and type(r['compiler_exit']) is int and r['compiler_exit']==0 and r['reason'] is None and v['parent_outer_exit']==1 and v['parent_accepted_children']==20 and v['parent_result_exists'] is False,'invalid parent boundary');verify(v['parent_output_guards']);verify(v['direct_slots'])
sup=SEED/'lib/DiophantineConsistency/SuppliedMarkedCompact.olean';need(sup.is_file() and H(sup)==r['object_sha256'],'supplied word object mismatch')
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
print(json.dumps({'status':'PASS_POINT_IN_TIME_HALT_COMPACT_SOURCE_SCAN','seed':str(SEED),'seed_result_sha256':RESULT_SHA,'seed_preflight_sha256':PREFLIGHT_SHA,'history_state_sha256':STATE_SHA,'sources':rows,'diagnostic_baselines':baselines,'direct_candidates':direct,'target_slots':targets,'lean_launched':False,'scope':'single-author source/slot scan; suffix parent failed at child 21; inherited package/transitive ancestry unauthenticated'},indent=2,sort_keys=True))
