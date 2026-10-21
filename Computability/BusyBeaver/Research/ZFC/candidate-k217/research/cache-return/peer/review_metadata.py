"""Own literal/data review; no supplied imports, checker execution or simulation."""
from pathlib import Path
import json,hashlib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');C=R/'Computability/BusyBeaver/Research/ZFC/candidate-k217';W=Path('/tmp/k217-cache-return');O=Path('/tmp/k217-cache-return-peer')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
d=load(W/'run2/composition.json');old=load(C/'sites217.json');new=load(W/'run2/sites.json')
def table(p):return {(int(q),int(b)):(int(x),m,int(t))for line in p.read_text().splitlines()if line and not line.startswith('#')for q,b,x,m,t in[line.split()]}
t=table(C/'k217.native.tm');n=table(W/'run2/candidate.native.tm');root='111111';ref=d['source_replacement']['reference_path']
checks=[]
def need(ok,label):
 if not ok:raise AssertionError(label)
 checks.append(label)
need([x for x in new if not x[0].startswith(root)]==[x for x in old if not x[0].startswith(root)],'all leaves outside substituted subtree identical')
need([x for x in new if x[0].startswith(root)]==[[root+'0','CD',4],[root+'10','CI',5],[root+'11','CC',2]],'exact new3-leaf transfer')
need([[x[0][len(ref):],*x[1:]]for x in old if x[0].startswith(ref)]==[['0','CD',4],['10','CI',5],['11','CC',2]],'selected old reference is same3-leaf transfer')
need(root[-1]==ref[-1]=='1','same immediate preceding prefix marker1')
need({k:(t.get(k),n.get(k))for k in t.keys()|n.keys()if t.get(k)!=n.get(k)}=={(164,1):((1,'R',98),(1,'R',130))},'only intended physical row changes')
need(len(new)==4728 and sum(2 if x[1]=='CD'else 1 for x in new)==6146,'new leaf/guard counts')
need(len([x for x in old if x[0].startswith(root)])==26,'removed26-leaf interval')
need(len(n)==434 and len({q for q,b in n})==217,'same217/434 state census')
need(sha(W/'run2/candidate.native.tm')==d['table_sha256'] and sha(W/'run2/sites.json')==d['source_sha256'],'root record source/table binding')
need(d['status']=='CACHE_RETURN_217_SOURCE_AND_STARTUP_PASS' and d['all_retained_CFG_edges']==6141 and d['startup_steps']==312617 and d['entire_startup_trace_unchanged'],'root record precise scope')
files=[W/'compose.py',W/'compose-v1.py',W/'run1.stderr',W/'run2/composition.json',W/'run2/candidate.native.tm',W/'run2/sites.json',C/'k217.native.tm',C/'sites217.json',R/'Computability/BusyBeaver/Research/ZFC/k218-quantifier-stability/pricing/source_language.py',R/'Computability/BusyBeaver/Research/ZFC/k218-quantifier-stability/pricing/build221.py']
receipt={'status':'FOCUSED_SOURCE_AND_LITERAL_METADATA_PEER_CLEAN','reviewer':'drop_contract','root_author':'root','source_read':'Full compose.py/v1 delta; relevant entire source-language and decoder-map helper definitions. No supplied invocation.','scope':'Exact source replacement/selected prior role, decoder-binding/retained CFG algorithm, literal table/source metadata and root recorded complete unchanged startup. This is not an independent replay of312617 transitions or full primitive runtime.','own_literal_checks':checks,'findings':[],'role_correction':'V1 asserted a unique subtree at130; v2 retains both old roles and selects the exact existing transfer subtree, then checks all expected prefix and leaf-action bindings. Matching preceding marker1 is preserved.','mathematical_boundary':'New transfer changes command semantics. Its ordinary cache-return/compiler proof is separately Reflection-reviewed. Both outgoing effects and all new primitive runtime obligations remain separate; exact matching leaf entry actions alone do not discharge them.','inherited_algorithm_observations':['decoder_map checks known prefixes only, unchanged tape and advancement before recursing; compose additionally checks intended state relation and every leaf entry.','Both CFG resolvers agree for each tree; retained edges may enter removed region only at its first ordinal. Removed internal semantics is covered only by the separate command proof.','Original full startup trace is checked row by row against old and new tables; no new row is permitted to differ on that trace.','No <=216 or formal-kernel claim follows.'],'files':[{'path':str(p),'sha256':sha(p)}for p in files],'own_reader_history':'history/metadata-draft1.txt','own_reader_sha256':sha(Path(__file__))}
(O/'review.json').write_text(json.dumps(receipt,indent=2)+'\n');print(sha(O/'review.json'))
