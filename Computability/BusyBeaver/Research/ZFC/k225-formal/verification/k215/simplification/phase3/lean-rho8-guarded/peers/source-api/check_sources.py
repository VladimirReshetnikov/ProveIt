"""Own inert declaration/provenance check; executes no producer or proof code."""
from pathlib import Path
from functools import cache
import hashlib,json,re

base=Path('/tmp/k215-domrho8-conceptual-survey')
repo=Path('/home/codex/.codex/worktrees/ec20/Proofs')
plain=base/'Plain.lean'
original=repo/'Computability/BusyBeaver/Research/ZFC/k225-formal/lean217/dominated_rho8_full_certificate.json'
cd=Path('/tmp/zfc-intake191/K218_Dominated_Rho8_2026-10-20/K218_Dominated_Rho8_2026-10-20/theory/evidence/CD230.v')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
s=plain.read_text();d=json.loads(original.read_text())

def normalize(t):
 if not isinstance(t,tuple):return t
 a,b=map(normalize,t)
 return 'T' if a==b=='T' else (a,b)

def parse(text):
 tokens=re.findall(r'\(|\)|[^\s()]+',text);i=0
 def one():
  nonlocal i
  t=tokens[i];i+=1
  if t!='(':
   assert t=='0' or re.fullmatch('v[0-9]+',t),t
   return 'T' if t=='0' else int(t[1:])
  assert tokens[i]=='wim';i+=1
  a,b=one(),one();assert tokens[i]==')';i+=1
  return (a,b)
 out=one();assert i==len(tokens)
 return normalize(out)

@cache
def term(i):
 t=d['term_table'][i]
 if isinstance(t,list):return normalize((term(t[0]),term(t[1])))
 return t['var'] if isinstance(t,dict) else t

bootstrap={int(m[1]):parse(m[2]) for m in re.finditer(r'(?m)^private theorem b(\d+).*? : T (.*?) :=\n',s)}
assert set(bootstrap)==set(range(61))
assert all(bootstrap[i]==term(d['nodes'][i]['term']) for i in bootstrap)
old_cd={int(m[1]):parse(m[2]) for m in re.finditer(r'Lemma cd_(\d+) \(.*? : nat\) : thm230 (.*?)\.\s*Proof\.',cd.read_text(),re.S)}
assert len(old_cd)==107
new_cd={int(m[1]):parse(m[2]) for m in re.finditer(r'(?m)^private theorem cd(\d+).*? :\n    T (.*?) := by',s)}
assert len(new_cd)==81 and all(new_cd[i]==old_cd[i] for i in new_cd)
guards={int(m[1]):m[2] for m in re.finditer(r'(?m)^private theorem cd(\d+).*?\(hb0 : (.*?)\) :',s)}
assert set(guards)=={0,46,47,52,54,60,66,76}
assert re.findall(r'^import (.+)',s,re.M)==['BusyBeaver.ZFC.Code254']
assert not re.search(r'\b(sorry|axiom|native_decide|implemented_by|unsafe)\b',s)
baseline=repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DomRho8.lean'
strip=lambda t:re.sub(r'\s+','',t)
dom=lambda t:re.search(r'structure DomImp.*?(?=\ntheorem le_l)',t,re.S)[0]
assert strip(dom(s))==strip(dom(baseline.read_text()))
target='theorem rho8_all (a b c u : Nat) : T (Code254.rho8 a b c u) :='
assert target in s and target in baseline.read_text()
actual=json.loads((base/'run4/result.json').read_text())
snapshot=base/'run4/PlainWithAudit.lean';log=base/'run4/compiler.log'
assert actual['status']=='PASS' and actual['exit_code']==0 and not actual['timed_out']
assert sha(snapshot)==actual['source_sha256'] and sha(log)==actual['log_sha256']
assert snapshot.read_text().startswith(s)
assert (base/'PlainWithAudit.lean').read_bytes()==snapshot.read_bytes()
client=snapshot.read_text()[len(s):]
assert len(re.findall(r'^example\b',client,re.M))==5
reports=re.findall(r'depends on axioms: \[([^]]*)\]',log.read_text())
assert reports==['propext, Quot.sound']*4
assert 'warning:' not in log.read_text() and 'error:' not in log.read_text()
result={'status':'PASS_INERT_SOURCE_AND_SAVED_AUDIT_CHECK','source':str(plain),'source_sha256':sha(plain),
 'bytes':plain.stat().st_size,'lines':len(s.splitlines()),'bootstrap':{'original_nodes':61,'exact_normalized_conclusions':61,'source':str(original),'sha256':sha(original)},
 'cd_templates':{'retained':81,'original':107,'exact_normalized_conclusions':81,'explicit_guard_ids':sorted(guards),'source':str(cd),'sha256':sha(cd)},
 'unchanged_api':['DomImp','rho8_all'], 'only_import':'BusyBeaver.ZFC.Code254',
 'saved_actual':{'path':str(base/'run4/result.json'),'sha256':sha(base/'run4/result.json'),'source_sha256':sha(snapshot),'seconds':actual['seconds'],'typed_clients':5,'axiom_reports':reports,'warnings':0},
 'scope':'Own declaration/provenance check and saved audit acknowledgment, no producer or Lean invocation; full ordinary source review is separate prose.'}
Path(__file__).with_name('source-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
