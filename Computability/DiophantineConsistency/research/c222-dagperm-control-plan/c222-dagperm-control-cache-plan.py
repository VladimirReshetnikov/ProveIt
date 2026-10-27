from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';B=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(x):assert sha(x['path'])==x['sha256'],x['path']
base=D/'research/c222-runtime215-cache-audit-20261026.json';packet=D/'reviews/arithmetic-dag-loops-replay.json'
assert sha(base)=='ede63a0d00714e349b52b667f5f2610c481cb3d206ca6d61364effef9769eb48'
assert sha(packet)=='26c0ebcee1bad71b6b613a4ffeda3e4e912299bfbf71679104a79421087ee0e5'
a=json.loads(base.read_text());p=json.loads(packet.read_text());mods={m['module']:m for m in a['modules']}
for r in p['records']:
 if r['module'].endswith('Checks'):continue
 n=r['module'];check(r['source']);check(r['object'])
 if n in mods:
  assert mods[n]['source']==r['source'];m=mods[n]
  m['historical_refresh_provenance']={k:m[k]for k in ['historical_record','historical_excluded_object','reason']}
  m['action']='REUSE_EXPLICIT_CURRENT_CLOSURE_REFRESH_PENDING_INDEPENDENT_ACCEPTANCE';m['objects']=[r['object']];m['provider']=rec(packet)
 else:
  assert n=='BusyBeaver.ZFC.ArithmeticDagLoops'
  mods[n]=dict(module=n,source=r['source'],objects=[r['object']],imports=['Init',*p['source_imports']],provider=rec(packet),action='REUSE_FROZEN_NEW_LEAF_PENDING_INDEPENDENT_ACCEPTANCE')
n='BusyBeaver.ZFC.PackedTables';assert n not in mods
mods[n]=dict(module=n,source=rec(B/'PackedTables.lean'),imports=['Init','BusyBeaver.ZFC.ArithmeticControlBisim'],action='PROPOSED_SINGLE_UNCHANGED_NON_FOUNDATION_FRESH_PREREQUISITE',reason='No authenticated PackedTables provider found in the consulted active Diophantine review inventories; no arbitrary existing olean selected.')
roots=['BusyBeaver.ZFC.ArithmeticDagLoops','BusyBeaver.ZFC.PackedTables'];order=[];active=set();done=set();ext=set()
def visit(n):
 if n not in mods:ext.add(n);return
 if n in done:return
 assert n not in active;active.add(n)
 for k in mods[n]['imports']:visit(k)
 active.remove(n);done.add(n);order.append(n)
for n in roots:visit(n)
assert done==set(mods);assert ext=={e['module']for e in a['external']}
pins=[rec(base),rec(packet),p['bundle_manifest'],rec(D/'reviews/arithmetic-dag-loops-author.md'),rec(__file__),a['compiler']]
for n in order:
 m=mods[n];pins.append(m['source']);pins.extend(m.get('objects',[]))
for e in a['external']:
 if 'path'in e:pins.append(dict(path=e['path'],sha256=e['sha256']))
 else:pins.extend([e['object'],*e['companions'],e['observed_source']])
for x in pins:check(x)
counts=dict(custom=len(order),Foundation=sum(n.startswith('Foundation.')for n in order),reuse=sum('objects'in mods[n]for n in order),artifacts=sum(len(mods[n].get('objects',[]))for n in order),fresh_unchanged=1,external=len(ext))
assert counts==dict(custom=138,Foundation=95,reuse=137,artifacts=422,fresh_unchanged=1,external=39)
out=dict(status='READ_ONLY_PROPOSAL_NO_COMPILATION',direct_imports=roots,counts=counts,modules=[mods[n]for n in order],external=a['external'],pins=pins,refresh_order=['BusyBeaver.ZFC.PackedTables'],compiler=a['compiler'],acceptance_boundary='Six refreshed generic objects and new DagLoops frozen by author; root independent review pending. This plan records that status and must select any later accepted provider by an explicit supplement.',scope='Actual parameter-free4751-row DagPerm control table and whole root occurrence proposed; no whole scheduler or literal215 simulation proved.')
target=D/'research/c222-dagperm-control-cache-plan-20261026.json';target.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(path=str(target),sha256=sha(target),counts=counts,pins=len(pins))))
