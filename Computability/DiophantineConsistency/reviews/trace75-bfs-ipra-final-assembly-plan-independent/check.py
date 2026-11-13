from pathlib import Path
import hashlib,json,os,re,subprocess,sys
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-ipra-final-assembly-plan';plan=h/'plan.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(plan)=='04559737ca02dc639ea0ac3a24bfd72997a9bae1f38c6d42b4da944b6a751dd6' and sha(h/'verify_sources.py')=='d76a6c00602fa038eac41f2def7803b57bb0a2b828bcf9685ee391e0fe801bd2'
p=json.loads(plan.read_text());assert p['status']=='HELD_AWAITING_FORWARD_RESULT_AND_OUTER_EXIT' and p['parent_result_sha256']==p['parent_outer_sha256']=='TO_BE_PINNED_AFTER_TERMINAL_AND_AUDIT'
stages=p['stages'];names=[x['module'] for x in stages];assert len(names)==len(set(names))==5
for i,row in enumerate(stages):
 s=root/row['source'];assert sha(s)==row['sha256'];imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',s.read_text(),re.M);assert imports==row['imports'] and not (set(imports)&set(names[i:]));assert len(re.findall(r'^#print axioms\s+',s.read_text(),re.M))==[1,1,1,6,5][i]
 print('stage',i+1,row['module'],'imports',', '.join(imports))
canonical=root/p['canonical_syntax_source'];assert sha(canonical)==p['canonical_syntax_sha256'] and (root/stages[0]['source']).read_bytes()==canonical.read_bytes()+b'\n#print axioms DiophantineConsistency.TenPositiveTrace75.evalRing_expression\n'
base=Path('/tmp/trace75-compatible-reverse-uy7s6cau/lib');pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');forward={r['module'] for r in json.loads((root/'research/trace75-bfs-compatible-forward-plan/observations/plan-attempt01/result.json').read_text())['stages']}
for n in names:assert not os.path.lexists(base/(n.replace('.','/')+'.olean')) and n not in forward
external=sorted({n for row in stages for n in row['imports']}-set(names));assert len(external)==8
for n in external:
 matches=[p/(n.replace('.','/')+'.olean') for p in (base,pack,core) if os.path.lexists(p/(n.replace('.','/')+'.olean'))]
 if n=='Trace75BFSModelHalt':assert not matches and n in forward;print(n,'absent in reverse base; planned forward stage')
 else:assert matches and matches[0].is_file();print(n,'reverse-base first',matches[0],sha(matches[0]))
r=subprocess.run([sys.executable,'-I','-S','-B',str(h/'verify_sources.py')],capture_output=True,text=True);assert r.returncode==0 and json.loads(r.stdout)['status']=='PASS'
print('PASS 5 source hashes/import order/report counts, 7 reverse-base direct providers, 1 planned forward provider and namespace-output vacancy; no Lean run')
