#!/usr/bin/env python3
"""Point-in-time source/direct-object scan; no Lean and no replay authorization."""
import argparse,hashlib,json,os,re,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;DC=HERE.parents[2];REPO=DC.parents[1];P=HERE.parent/'compact44-graph-marked-join-plan'
SEED=Path('/tmp/ipra-wang-chunk-author-build-02/lib');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='f79b98bb500a0cf2af5dfda7f7341468348bfc4f53664d6e15fb804902a23a3d'
AUDIT=DC/'reviews/compact44-wang-chunk-author-artifact-independent-audit'
AUDIT_PINS={'CHECK.json':'59dd1eefe5fc2d46bbb0ca7b2d83e14bcc1de9b692da98e94c5598f17678945e','terminal-observation.json':'af62d28207cca0c6d6163b4f46731919031600bd69d5efddc1a41dbe509e6b9a','audit.py':'a48b7684dc27fff4705419d30fbf14a62fb99f9ac302edcd79b1d508bccbcda1'}
SUF=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
EXTRA=[('CompactLocalWord','compact44-local-compact-word-prototype/CompactLocalWord.lean','60b584bc4478933d69d364da81365e3bdb59af2689d7417ba74a47cec1508041'),('OldWordIdentification','compact44-local-compact-word-prototype/OldWordIdentification-DRAFT.lean','c2d46f266605b70c7be54fd5d919fb7233ac1eb92964ae4de128177ab2b4e519'),('FixedGraphMarkedHalt','compact44-marked-halt-open-exploration/no-check/FixedGraphMarkedHalt.lean','6d98a5ac6a8d892e2b6ee5e9fa908d276a52311cb4647a1a05350470f59ffcf2'),('MarkedSuffixInventory','compact44-marked-suffix-source-plan/MarkedSuffixInventory-DRAFT.lean','c27f0ea72f128425f74b789de203c8fee9e59d28721774a9f912c7acca0d703c')]
def require(v,msg):
 if not v:raise ValueError(msg)
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def record(p):
 if not os.path.lexists(p):return None
 require(p.is_file(),('dangling or nonregular candidate',str(p)))
 return {'realpath':str(p.resolve(strict=True)),'sha256':H(p)}
def slots(stem):return {str(Path(str(stem)+s)):record(Path(str(stem)+s)) for s in SUF}
def main():
 require(__debug__ and not sys.flags.optimize,'optimized Python rejected');ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 require(not os.path.lexists(args.output),'output exists');receipt=SEED.parent/'RESULT.json';require(H(receipt)==RECEIPT,'seed result drift')
 for name,sha in AUDIT_PINS.items():require(H(AUDIT/name)==sha,('audit pin drift',name))
 isolated=HERE.parent/'compact44-marked-halt-open-exploration/no-check';require(H(isolated/'terminal-observation.json')=='44376a536557d138dcad94e8515b9b69aea94659c292f5b36eaa5a2add745058' and H(isolated/'compile.log')=='30bddd6fecc5844fbc4602d711d0bdaa1bad4a5e88854efbaca7764b8a58f06e','isolated observation drift');io=json.loads((isolated/'terminal-observation.json').read_text());require(io.get('outer_exit')==0 and io.get('compiler_exit')==0 and io.get('source_sha256')=='6d98a5ac6a8d892e2b6ee5e9fa908d276a52311cb4647a1a05350470f59ffcf2' and io.get('axioms')==['propext','Classical.choice','Quot.sound'],'isolated observation mismatch')
 audit=json.loads((AUDIT/'CHECK.json').read_text());require(audit.get('status')=='PASS_INDEPENDENT_AUTHOR_ONLY_WANG_ARTIFACT_AUDIT' and audit.get('result_sha256')==RECEIPT,'audit schema mismatch')
 require(H(P/'busybeaver-source-scan.json')=='abe89bf1cf589a8146771707d322c663012e03e63a7e4e605df486b808f19846' and H(P/'source-scan.json')=='2aeb7400ef18c7cd4bc0c74b1ca09b53e0c685f6054e99d92617f3af9bab7cc6','prior source scans drift');a=json.loads((P/'busybeaver-source-scan.json').read_text())['ordered_sources'];b=json.loads((P/'source-scan.json').read_text())['ordered_sources'];allrows=a+b;require(len(allrows)==100,'prior source count')
 rows=[]
 for x in allrows[82:]:
  name=x['module'] if '.' in x['module'] else 'DiophantineConsistency.'+x['module'];p=REPO/x['source'];require(H(p)==x['sha256'],('prior source drift',str(p)));rows.append({'module':name,'source':str(p),'sha256':x['sha256']})
 for name,rel,sha in EXTRA:
  p=HERE.parent/rel;require(H(p)==sha,('extra source drift',str(p)));rows.append({'module':'DiophantineConsistency.'+name,'source':str(p),'sha256':sha})
 require(len(rows)==22,'candidate count');names=[x['module'] for x in rows];require(len(set(names))==len(names),'duplicate module')
 produced=set();direct={};target_slots={};unresolved=[];conflicts=[];collisions=[]
 for x in rows:
  imports=re.findall(r'^import\s+([\w.]+)',Path(x['source']).read_text(),re.M);x['imports']=imports
  for root in (SEED,PKG):
   stem=root/Path(*x['module'].split('.'));rr=slots(stem);target_slots.update(rr)
   if any(v is not None for v in rr.values()):collisions.append({'module':x['module'],'root':str(root)})
  for dep in ['Init']+imports:
   if dep in produced:continue
   if dep in names:unresolved.append([x['module'],dep,'out of order']);continue
   rel=Path(*dep.split('.')); candidates=[]
   for root in (SEED,PKG):
    stem=root/rel;rr=slots(stem);candidate=record(Path(str(stem)+'.olean'));candidates.append({'root':str(root),'object':candidate,'slots':rr})
   present=[c for c in candidates if c['object'] is not None]
   if not present:unresolved.append([x['module'],dep,'missing']);continue
   if len({c['object']['sha256'] for c in present})!=1:conflicts.append([x['module'],dep])
   direct[dep]={'chosen_root':present[0]['root'],'candidates':candidates}
  produced.add(x['module'])
 for row in rows:require(H(Path(row['source']))==row['sha256'],('late source drift',row['module']))
 require(H(receipt)==RECEIPT,'late receipt drift')
 for name,sha in AUDIT_PINS.items():require(H(AUDIT/name)==sha,('late audit pin drift',name))
 result={'status':'PASS_SOURCE_ONLY_SUFFIX_SCAN' if not (unresolved or conflicts or collisions) else 'FAIL_SOURCE_ONLY_SUFFIX_SCAN','scope':'point-in-time direct candidates; no Lean, recursive provider authentication, or replay','seed':str(SEED),'seed_result_sha256':RECEIPT,'author_audit_pins':AUDIT_PINS,'sources':rows,'direct_candidates':direct,'target_slots':target_slots,'target_collisions':collisions,'conflicting_direct_objects':conflicts,'unresolved':unresolved}
 args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':result['status'],'modules':len(rows),'direct_seeds':len(direct),'target_collisions':len(collisions),'conflicts':len(conflicts),'unresolved':len(unresolved)},sort_keys=True));require(result['status']=='PASS_SOURCE_ONLY_SUFFIX_SCAN','scan failed')
if __name__=='__main__':main()
