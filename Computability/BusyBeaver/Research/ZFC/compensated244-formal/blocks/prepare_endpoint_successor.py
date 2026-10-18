from pathlib import Path
import hashlib,json,re,difflib
H=Path(__file__).parent;sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();old=H/'history/unexecuted-seven-pair-draft';D=json.loads(Path('/tmp/zfc244-248bc05936-inspection/zfc244-compensated-routing-20261018/runtime/contextual_fold_proof.json').read_text())
s=(old/'Compensated244Blocks.lean').read_text();a=(old/'Audit.lean').read_text()
# Precompiler style corrections; every nontrivial head arithmetic proof is retained.
s=re.sub(r', \(show h ([+-]) 1 = \(h \1 1\) by omega\)','',s)
start=s.index('private theorem enter92_from81_one_new');end=s.index('\ntheorem enter92_from81_one',start)
t=s[start:end];assert t.count('(hm2 :')==1 and t.count('hm2')==1;s=s[:start]+t.replace('(hm2 :','(_hm2 :')+s[end:]
pos=lambda k:'h'if k==0 else f'(h + {k})'if k>0 else f'(h - {-k})';hn=lambda k:'h0'if k==0 else f'hp{k}'if k>0 else f'hm{-k}';bo=lambda b:'true'if b else'false';wrappers=[]
for c in D['macro_families']:
 name=c['name'];window={int(k):v for k,v in c['known_input_cells'].items()};prem='\n'.join(f'    ({hn(k)} : Tape.read t {pos(k)} = {bo(v)})'for k,v in sorted(window.items()));args=' '.join(hn(k)for k in sorted(window));tp='(Tape.write (Tape.write t h false) (h - 1) false)'if name=='enter92_from81_one'else't'
 sig=f'(h : Int) (t : Tape)\n{prem} :\n    machineCompensated244.runFrom (cfgNew {c["start"]} h t) {c["new_steps"]} =\n      cfgNew {c["end_state"]} {pos(c["end_head"])} {tp}'
 proof=f'{name}_new h t {args}'
 wrappers.append(f'\ntheorem {name}_new_endpoint {sig} :=\n  {proof}\n')
 a+=f'\n#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Blocks.{name}_new_endpoint\nexample {sig} :=\n  {name}_new_endpoint h t {args}\n'
s=s.replace('\nend SetTheory.BusyBeaver.ZFC.Compensated244Blocks\n',''.join(wrappers)+'\nend SetTheory.BusyBeaver.ZFC.Compensated244Blocks\n');(H/'Compensated244Blocks.lean').write_text(s);(H/'Audit.lean').write_text(a)
(H/'endpoint-wrapper.diff').write_text(''.join(difflib.unified_diff((old/'Compensated244Blocks.lean').read_text().splitlines(True),s.splitlines(True),fromfile='draft7/source',tofile='final14/source')))
o=dict(status='SOURCE_ONLY',source=dict(path=str(H/'Compensated244Blocks.lean'),sha256=sha(H/'Compensated244Blocks.lean')),audit=dict(path=str(H/'Audit.lean'),sha256=sha(H/'Audit.lean')),predecessor=dict(path=str(old/'source-inventory.json'),sha256=sha(old/'source-inventory.json')),generator=dict(path=str(Path(__file__).resolve()),sha256=sha(__file__)),probes=14,callers=14,scope='Adds seven public exact-new-endpoint wrappers to the seven paired block equalities; removes tautological arithmetic simp arguments and renames one unused private premise before any proof run. Existing pair statements unchanged; no compiler/simulator invoked.')
(H/'source-inventory.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o))
