#!/usr/bin/env python3
"""Fail-closed direct-name observation only. Never invokes Lean or writes objects."""
from pathlib import Path
from hashlib import sha256
from collections import defaultdict
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize
D=Path('research/current2011-shear72-latest-bounded-provider-inventory')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
selection=json.loads(Path('research/current2011-shear72-local-nozero-bridge-selection/selection.json').read_text())
roots=json.loads((D/'roots.json').read_text());assert len(roots)==len(set(roots))
for n,i in selection['drafts'].items():
 p=Path(i['path']);assert sha256(p.read_bytes()).hexdigest()==i['sha256'],n
 assert re.findall(r'^import\s+(\S+)',p.read_text(),re.M)==i['imports'],n
for n,i in selection['frontier'].items():
 if i['kind']!='external-unexamined':assert sha256(Path(i['path']).read_bytes()).hexdigest()==i['sha256'],n
# Duplicate simple declaration names in first explicit namespace only; not a Lean parser.
decls=defaultdict(list)
for n,i in selection['drafts'].items():
 text=Path(i['path']).read_text();ns=re.search(r'^namespace\s+(\S+)',text,re.M)
 assert ns,n
 for kind,name in re.findall(r'^(?:private\s+)?(theorem|lemma|def|abbrev)\s+(\w+)',text,re.M):decls[ns.group(1)+'.'+name].append(n)
duplicates={k:v for k,v in decls.items() if len(v)>1}
# Explicit bounded roots, not a claim about any actual future LEAN_PATH.
names=sorted(set(selection['drafts'])|set(selection['frontier'])|{'Shear72Literal'})
observed={}
for n in names:
 rel=n.replace('.','/')+'.olean';hits=[]
 for root in roots:
  p=Path(root)/rel
  if p.is_file():
   hits.append({'path':str(p),'realpath':str(p.resolve()),'sha256':sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size,'companions':{s:Path(str(p)+s).is_file() for s in ['.private','.server']}})
 observed[n]=hits
# Observe competing research snapshots by basename, not Lean resolution.
byname=defaultdict(list)
for p in Path('research').rglob('*.lean.src'):
 stem=p.name[:-9]
 if stem in {n.rsplit('.',1)[-1] for n in selection['drafts']}:
  byname[stem].append({'path':str(p),'sha256':sha256(p.read_bytes()).hexdigest()})
source_alternatives={k:sorted(v,key=lambda i:i['path']) for k,v in byname.items() if len(v)>1}
historical_expected={'OrdinarySphere7160IPRA':'652809cc682ad29cc7ed71fcdd008514c7b6d9438a59ff221d80a9e61ae71256','OrdinarySphere7160Model':'dcf62bccbeb5ef8303104411996eba3d3798784cdc6fa9b40040e4a9d6d135e2','OrdinarySphere7160Generic':'73a022ff49f38e554c0ece51601aba36cd11931fceb2e020493fb5dd09127c2b','OrdinarySphere7160Literal':'b4386569a433cc7a0e2033368a9167081bb5e6e50ee8fd867df1938c01ed4e60'}
historical_match={n:any(h['sha256']==v for h in observed[n]) for n,v in historical_expected.items()}
missing_drafts=[n for n in sorted(selection['drafts']) if not observed[n]]
missing_frontier=[n for n in sorted(selection['frontier']) if not observed[n]]
shadows={n:{'paths':len(h),'realpaths':len({x['realpath'] for x in h}),'hashes':len({x['sha256'] for x in h})} for n,h in observed.items() if len(h)>1}
# Even a favorable local observation is never enough to approve a build.
blockers=['selected draft sources are unelaborated', 'transitive, package and runtime ancestry is not authenticated', 'actual future search path and collision policy are not fixed', 'no complete source-to-object producer validation']
if missing_drafts:blockers.append('selected draft objects unobserved in bounded roots')
if missing_frontier:blockers.append('direct frontier objects unobserved in bounded roots')
if duplicates:blockers.append('duplicate lexical declarations in selected draft snapshots')
extraction=selection['frontier']['DiophantineConsistency.ArithmeticCarrier94Extraction']
assert extraction['kind']=='historical-private-source-frontier'
assert extraction['sha256']=='415e74a23218889f43159a8e96915be93ca54446b3dd3ad69927ac492b16a83d'
prior=json.loads(Path('research/current2011-shear72-private-extraction-source-selection/selection.json').read_text())
delta={'removed':sorted(set(prior['frontier'])-set(selection['frontier'])),'added':sorted(set(selection['frontier'])-set(prior['frontier']))}
assert delta=={'removed':['DiophantineConsistency.HAExpressionNoZeroEquiv','DiophantineConsistency.ModelCarrierSpheres'], 'added':['DiophantineConsistency.Carrier65','Mathlib.Tactic.ByContra','Mathlib.Tactic.Linarith']}
result={'frontier_delta_from_private_extraction_selection':delta,'status':'NOT_READY','selection_sha256':sha256(Path('research/current2011-shear72-local-nozero-bridge-selection/selection.json').read_bytes()).hexdigest(),'root_count':len(roots),'roots_present':{r:Path(r).is_dir() for r in roots},'selected_draft_count':len(selection['drafts']),'observed':observed,'unobserved_selected_drafts':missing_drafts,'unobserved_direct_frontier':missing_frontier,'multiple_path_observations':shadows,'same_basename_draft_alternatives':source_alternatives,'lexical_duplicate_declarations':duplicates,'historical_object_hash_matches_only':historical_match,'extraction_selected_private_sha256':extraction['sha256'],'extraction_workspace_sha256':sha256(Path('Lean/DiophantineConsistency/ArithmeticCarrier94Extraction.lean').read_bytes()).hexdigest(),'blockers':blockers,'lean_executed':False,'ready_for_build':False}
print(json.dumps(result,sort_keys=True,indent=2))
if sys.argv[1:]==['--require-ready']:sys.exit(2)
if sys.argv[1:]:raise SystemExit('unsupported arguments')
