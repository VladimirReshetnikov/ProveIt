"""Owned, inert source-text review. Never imports or executes any reviewed source."""
from pathlib import Path
import ast, hashlib, json, re
D=Path(__file__).resolve().parent
m=json.loads((D/'sources.json').read_text())
def sha(b): return hashlib.sha256(b).hexdigest()
def read(label,name):
 p=next(x['path'] for x in m['files'] if Path(x['path']).name==name)
 b=(D/label/p).read_bytes()
 assert sha(b)==next(x[label]['sha256'] for x in m['files'] if x['path']==p)
 return b.decode()
def uncomment(s):
 # Nested Lean comment eraser, retaining line boundaries for source-only census.
 out=[]; i=0; depth=0
 while i<len(s):
  if s[i:i+2]=='/-': depth+=1; i+=2
  elif depth and s[i:i+2]=='-/': depth-=1; i+=2
  elif depth: out.append('\n' if s[i]=='\n' else ' '); i+=1
  elif s[i:i+2]=='--':
   j=s.find('\n',i); j=len(s) if j<0 else j;out.append(' '*(j-i));i=j
  else: out.append(s[i]);i+=1
 assert not depth
 return ''.join(out)
def decls(s):
 s=uncomment(s)
 starts=list(re.finditer(r'(?m)^(?:private\s+)?(?:noncomputable\s+)?(theorem|def|abbrev|inductive|structure)\s+(\S+)',s))
 out={}
 for i,x in enumerate(starts):
  block=s[x.start():starts[i+1].start() if i+1<len(starts) else len(s)]
  if x.group(1)=='theorem':
   header=block.split(':=',1)[0]
   header=re.split(r'(?m)^\s*\|',header,1)[0]
   # Same headers can span end directives when the theorem is equation-style.
   header=re.split(r'(?m)^\s*(?:end|#print|variable|include|section|namespace)\b',header,1)[0]
   out[x.group(2)]=' '.join(header.split())
 return out
headers=[]
for x in m['files']:
 name=Path(x['path']).name
 if name.endswith('.lean'):
  before=decls(read('before',name));after=decls(read('after',name))
  delta={k:{'before':before.get(k),'after':after.get(k)} for k in before.keys()|after.keys() if before.get(k)!=after.get(k)}
  if delta:headers.append({'file':name,'changes':delta})
# Exact computed-tree change boundaries after ignoring comment text.
trees={
 'KSource215Program.lean':{'t215':'ptree p215'},
 'KSource215Data.lean':{'tD':'ptree pathDagPerm'},
 'KSource217.lean':{'t217':'ptree p217','tD':'ptree pathDagDom'},
 'KSource218.lean':{'t218':'ptree p218','tD':'ptree pathDag219'},
 'KSource219.lean':{'t219':'ptree p219','tD':'ptree pathDag219'},
 'KSource221.lean':{'t221':'ptree p221','tD':'ptree pathDag222'},
 'KSource225.lean':{'t225':'ptree p225','t230':'ptree p230'},
}
treechecks=[]
for name,ds in trees.items():
 before=read('before',name); after=read('after',name)
 for n,body in ds.items():
  before,count=re.subn(r'(def '+n+r' : Tree :=)\n  [^\n]+',r'\1 '+body,before)
  assert count==1,(name,n,count)
 assert ''.join(uncomment(before).split())==''.join(uncomment(after).split()),name
 treechecks.append({'file':name,'trees':ds,'all_noncomment_remaining_bytes_equal_after_whitespace_normalization':True})
# Literal-only AST reads for synchronization relations. No reviewed Python is executed.
def constants(name):
 tree=ast.parse(read('after',name));result={}
 for node in tree.body:
  if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
   try: result[node.targets[0].id]=ast.literal_eval(node.value)
   except (ValueError,TypeError):pass
 return result
const=constants('generate_l2k222.py')
forks=[]
for src,dst in [('L2Lib254','L2Lib222'),('L2Macros254','L2Macros222'),('L2Control254','L2Control222')]:
 text=read('after',src+'.lean')
 for a,b in const['SUBS']:text=text.replace(a,b)
 if src=='L2Control254':
  assert text.count(const['OLD_136'])==1
  text=text.replace(const['OLD_136'],const['NEW_136'])
  anchor='/-! ## Fetch, MP and NIP -/'
  assert text.count(anchor)==1;text=text.replace(anchor,const['LOOP136']+anchor)
 head='/- Forked by Research/ZFC/k225-formal/generate_l2k222.py from '+src+'.lean for dag222 (Elliot Glazer\'s Dag230 with the 222\'s AX node). -/\n'
 assert head+text==read('after',dst+'.lean'),dst
 forks.append({'source':src+'.lean','target':dst+'.lean','literal_substitution_relation_exact':True})
# The actual AX source word is the unchanged projection of its old paired word.
ax=[];template=constants('generate_l2axiomsdom.py')['PERM_TEMPLATE']
for variant in ['Dom','Perm']:
 name='L2Axioms'+variant+'.lean';before=read('before',name);after=read('after',name)
 old=re.search(r'def axWord : List \(AXAtom × Nat\) := \[(.*?)\]\n',before,re.S).group(1)
 new=re.search(r'def axWord : List AXAtom := \[\n(.*?)\]\n',after,re.S).group(1)
 atoms=re.findall(r'\(\.(\w+), (\d+)\)',old)
 assert [a for a,_ in atoms]==re.findall(r'\.(\w+)',new)
 t=template.replace('@WORD@',new+']')
 for i,n in enumerate([457,458,459,460]):t=t.replace('@G'+str(i)+'@',str(n))
 if variant=='Dom':
  for a,b in [('dagPerm','dagDom'),('DagPerm','DagDom'),('L2Perm','L2Dom'),('EnumPerm','EnumDom')]:t=t.replace(a,b)
 assert t==after,name
 ax.append({'file':name,'atom_projection_identical':True,'atom_count':len(atoms),'final_old_successor':int(atoms[-1][1]),'producer_literal_template_exact_given_same_word':True})
# Check producer output expressions as inert constant strings.
producer=[]
for k in ['215','217','218','219','221','225']:
 name='generate_source'+k+'_lean.py';s=read('after',name)
 target='pathDagPerm' if k=='215' else 'pathDagDom' if k=='217' else 'pathDag219' if k in ['218','219'] else 'pathDag222' if k=='221' else 'p230'
 assert 'def t'+k+' : Tree := ptree p'+k+'\\n' in s
 assert ('def t230' if k=='225' else 'def tD')+' : Tree := ptree '+target+'\\n' in s
 producer.append({'file':name,'source_tree':'ptree p'+k,'target_tree':'ptree '+target,'literal_output_expressions_present':True})
# Scan for trust enlargements, with comments removed. This is a census, not a compiler claim.
trust=[]
for x in m['files']:
 name=Path(x['path']).name
 if name.endswith('.lean'):
  old=uncomment(read('before',name));new=uncomment(read('after',name))
  pats=r'\b(?:sorry|admit|axiom|unsafe|native_decide|run_tac|implemented_by)\b'
  oldtokens=re.findall(pats,old);newtokens=re.findall(pats,new)
  if oldtokens!=newtokens:trust.append({'file':name,'before':oldtokens,'after':newtokens})
assert not trust,trust
out={'status':'PASS_SOURCE_TEXT_INVARIANTS_NOT_A_PROOF_BUILD','sources_sha256':sha((D/'sources.json').read_bytes()),'theorem_header_deltas':headers,'computed_tree_boundaries':treechecks,'macro_fork_relations':forks,'ax_template_relations':ax,'computed_tree_producer_expressions':producer,'changed_trust_tokens':trust,'compiler_invoked':False,'reviewed_python_imported_or_executed':False}
(D/'static-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
