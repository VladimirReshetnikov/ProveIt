from pathlib import Path
import hashlib,importlib.util,json,re,sys
repo=Path('/home/codex/.codex/worktrees/ec20/Proofs')
formal=repo/'Computability/BusyBeaver/Research/ZFC/k225-formal'
lean=repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
base=Path('/tmp/k215-offset-symmetry');dst=base/'candidate';dst.mkdir(exist_ok=False)
py=dst/'Computability/BusyBeaver/Research/ZFC/k225-formal';py.mkdir(parents=True);out=dst/'lean';out.mkdir()
# The standalone tested proof becomes three generic symmetry lemmas plus the iff wrapper.
proof=(base/'OffsetSymmetry.lean').read_text()
delta=proof[proof.index('@[simp] theorem delta_neg'):proof.index('/-- Reverse both')]
symmetry=proof[proof.index('/-- Reverse both'):proof.index('/-- A single checked')]
iff=proof[proof.index('/-- A single checked'):proof.index('#print axioms')]
s=(lean/'RMOffsetBisim.lean').read_text()
s=s.replace('two directions are separate checks (`omirror` negates the offsets).','semantic relation is symmetric: swapping the sites and negating offsets gives\nthe converse, so one checked certificate establishes halting equivalence.')
s=s.replace('/-- Register files related by offset',delta+'/-- Register files related by offset')
s=s.replace('section Sound',symmetry+'section Sound',1)
s=s.replace('\nend SetTheory.BusyBeaver.ZFC.RMOffsetBisim','\n'+iff+'end SetTheory.BusyBeaver.ZFC.RMOffsetBisim')
(out/'RMOffsetBisim.lean').write_text(s)
# Forward-only emission uses exactly the original forward entries and kernel checker.
s=(formal/'generate_source215_lean.py').read_text()
s=s.replace('4,744-leaf','4,751-leaf').replace('2,237 entries','2,240 entries').replace('DAG219_NODES_JSON DAG219_SITES_JSON','DAGPERM_NODES_JSON DAGPERM_SITES_JSON')
s=s.replace('    mirror = [(b, a, -z, j, k) for a, b, z, j, k in entries]\n','')
s=s.replace('in chunks, with its mirror for the converse.','once in chunks; generic offset-bisimulation symmetry supplies the converse.')
s=s.replace("The 219's", "The 215's").replace('219 → dagPerm','215 → dagPerm')
s=s.replace('    out += "\\n/-! ## Mirrored certificate (dagPerm → 219) -/\\n\\n" + cert_block("bwd", mirror, "tD", "t215")\n','')
s=re.sub(r'\ntheorem bwd_start\' :.*?(?=\n/-- \*\*The 215)', '\n', s, flags=re.S)
s=s.replace("⟨ocheck_halts fwd_start' fwd_all' R, ocheck_halts bwd_start' bwd_all' R⟩", "ocheck_halts_iff fwd_start' fwd_all' R")
assert 'bwd' not in s and 'mirror' not in s
(py/'generate_source215_lean.py').write_text(s)
s=(formal/'partition_source215_lean.py').read_text()
s=s.replace('and its unchanged facade.','and its facade.').replace('fw=s.index(\'theorem fwd_start :\');mirror=s.index(\'/-! ## Mirrored certificate\');bw=s.index(\'theorem bwd_start :\')', "fw=s.index('theorem fwd_start :')")
s=s.replace('common=s[:fw]+s[mirror:bw]+end','common=s[:fw]+end').replace("for direction in ['fwd','bwd']:","for direction in ['fwd']:").replace('facade=s[fw:mirror]+s[bw:]','facade=s[fw:]').replace('len(mapping)==32 and len(order)==34','len(mapping)==16 and len(order)==18')
(py/'partition_source215_lean.py').write_text(s)
s=(formal/'prepare_k215.py').read_text()
s=s.replace('2. `generate_boot215_lean.py`, `generate_source215_lean.py` (p215 against dagPerm),\n   `generate_sites215_lean.py` and `generate_dense215_lean.py`, by checked substitutions in the\n   221/219 generators.','2. `generate_boot215_lean.py`, `generate_sites215_lean.py` and\n   `generate_dense215_lean.py`, by checked substitutions in the 221/219 generators.\n\nThe forward-only `generate_source215_lean.py` is maintained directly; the generic\noffset-bisimulation symmetry theorem supplies its reverse implication.')
s=re.sub(r'derive\("generate_source219_lean.py", "generate_source215_lean.py", \[.*?\n\]\)\n\n','',s,flags=re.S)
assert 'derive("generate_source219' not in s
(py/'prepare_k215.py').write_text(s)
# Execute only the reviewed pure source generator, redirecting all outputs to scratch.
sys.path[:0]=[str(py),str(formal)]
partspec=importlib.util.spec_from_file_location('partition_source215_lean',py/'partition_source215_lean.py');partmod=importlib.util.module_from_spec(partspec);partspec.loader.exec_module(partmod);sys.modules['partition_source215_lean']=partmod
spec=importlib.util.spec_from_file_location('source215_candidate',py/'generate_source215_lean.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
mod.REPO=repo;mod.TARGET=out/'KSource215.lean';mod.SITES215=formal.parent/'candidate-k215/sites215.json'
sys.argv=[str(py/'generate_source215_lean.py'),str(formal/'lean215/dagperm_nodes.json'),str(formal/'lean215/dagperm_sites.json')]
mod.main()
# Every forward check statement/proof and every surviving data declaration must be exact.
for i in range(16):
 name=f'KSource215FwdCheck{i:02d}.lean'
 assert (out/name).read_bytes()==(lean/name).read_bytes(),name
print(json.dumps({'lean_files':len(list(out.glob('*.lean'))),'removed_backward_checks':16,
 'old_data_bytes':(lean/'KSource215Data.lean').stat().st_size,'new_data_bytes':(out/'KSource215Data.lean').stat().st_size,
 'old_data_lines':len((lean/'KSource215Data.lean').read_text().splitlines()),'new_data_lines':len((out/'KSource215Data.lean').read_text().splitlines())},indent=2))
