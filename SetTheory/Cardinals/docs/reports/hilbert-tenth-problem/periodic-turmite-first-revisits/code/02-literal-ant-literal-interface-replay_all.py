#!/usr/bin/env python3
"""Fresh-directory reproduction of the complete own-code proof packet.
No upstream code, external executable, network request, or dense ant tile is used.
"""
if not __debug__:raise RuntimeError('Assertions required')
import ast,hashlib,json,pathlib,shutil,subprocess,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parent
COMMANDS=[
 'nand/build_nand.py','not/build_not.py','copy/build_normalized_copy_family.py','copy/build_delayed_copy.py','copy/build_pair_instructions.py',
 'strip/build_periodic_benchmark.py','strip/verify_periodic_benchmark.py',
 'copy/verify_copy_family.py','copy/verify_delayed_copy.py','copy/verify_pair_instructions.py','copy/audit_atlas_compatibility.py',
 'copy/build_marker_variants.py','copy/build_initial_anchor.py','copy/verify_marker_variants.py','copy/verify_marker_neighbors.py','copy/verify_header_entry_only.py','copy/translate_anchor.py',
 'ca/build_ca_circuit.py','ca/verify_complete_tables.py','ca/physical_program.py','ca/verify_program_ledger.py',
 'copy/program_audit/verify_program_index_bounds.py','copy/review_global_generator.py',
 'plans/boolean_word_programs.py','atlas/check_initialization_observer.py','atlas/verify_observer_polarity.py','atlas/quantitative_ledger.py','atlas/compile_input.py --selfcheck']
OUTPUTS=['nand/nand_macro.json','not/normalized_not.json','strip/periodic_benchmark.json','strip/independent_cycle_certificate.json',
 'copy/delayed_copy.json','copy/independent_family_receipt.json','copy/delayed_copy_receipt.json','copy/pair_instruction_receipt.json','copy/atlas_compatibility_receipt.json',
 'copy/marker_left_start.json','copy/marker_right_stop.json','copy/left_start_anchor.json','copy/marker_variants_receipt.json','copy/marker_neighbors_receipt.json','copy/header_entry_only_receipt.json','copy/fixed_initial_anchor_patch.json','copy/global_generator_review.json',
 'copy/program_audit/receipt.json','copy/program_audit/node_bounds.json',
 'ca/fixed_ca_cell.json','ca/radius_one_32_table.bin','ca/radius_half_11_table_le.bin','ca/complete_table_verification.json','ca/physical_program.json','ca/program_ledger.json',
 'receipts/boolean_word_programs.json','atlas/initialization_observer_receipt.json','atlas/observer_polarity_receipt.json','atlas/quantitative_ledger.json','atlas/empty_input_example.json','atlas/input_loader_receipt.json']
OUTPUTS += ['copy/normalized_'+s+'.json'for s in['copy','moved_copy_left','moved_copy_right','fanout2','fanout3']]
OUTPUTS += ['copy/pair_'+s+'.json'for s in['dup','move_left','move_right']]

def main():
 assert hashlib.sha256((ROOT/'common/primitive_maps.json').read_bytes()).hexdigest()=='fb2e7245f325bfbbe8a6d59e0ac1a3c63e4e73c0fb523d4738ea9c661c3d1add'
 assert hashlib.sha256((ROOT/'ca/u15_table.json').read_bytes()).hexdigest()=='0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a'
 with tempfile.TemporaryDirectory(prefix='literal-universal-ant-replay-')as tmp:
  fresh=pathlib.Path(tmp)/'packet'
  shutil.copytree(ROOT,fresh,ignore=shutil.ignore_patterns('__pycache__','preliminary','.git','fresh_replay.json'))
  commands=[]
  for rel in COMMANDS:
   parts=rel.split();done=subprocess.run([sys.executable,str(fresh/parts[0]),*parts[1:]],cwd='/',capture_output=True,text=True)
   if done.returncode:raise RuntimeError({'script':rel,'stdout':done.stdout[-2000:],'stderr':done.stderr[-2000:]})
   scope=(ast.get_docstring(ast.parse((fresh/parts[0]).read_text())) or '').split('\n')[0]
   commands.append({'script':rel,'scope':scope,'returncode':0,'stdout_sha256':hashlib.sha256(done.stdout.encode()).hexdigest()})
   print('PASS',rel,flush=True)
  outputs=[]
  for rel in OUTPUTS:
   b=(fresh/rel).read_bytes();old=(ROOT/rel).read_bytes()
   if b!=old:raise AssertionError(('exact regeneration mismatch',rel,hashlib.sha256(old).hexdigest(),hashlib.sha256(b).hexdigest()))
   outputs.append({'file':rel,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
  guards=[]
  for rel in COMMANDS+['replay_all.py']:
   parts=rel.split();source=(fresh/parts[0]).read_text()
   if 'not __debug__'not in source:
    guards.append({'script':rel,'optimized_mode':'unsupported_not_run_no_explicit_guard'});continue
   test=subprocess.run([sys.executable,'-O',str(fresh/parts[0]),*parts[1:]],cwd='/',capture_output=True,text=True)
   assert test.returncode!=0 and 'RuntimeError'in test.stderr,(rel,'optimization guard failed')
   guards.append({'script':rel,'optimized_mode':'rejected_as_required','returncode':test.returncode})
  result={'status':'PASS_FRESH_FULL_PROOF_PACKET_REPLAY','cwd':'/','commands':commands,'byte_exact_outputs':outputs,'optimized_mode_guards':guards,
   'upstream_code_executed':False,'network_used':False,'dense_ant_tile_materialized':False,'physical_601m_row_program_expanded':False,
   'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
  (ROOT/'atlas/fresh_replay.json').write_text(json.dumps(result,indent=2)+'\n')
  print(json.dumps({'status':result['status'],'own_scripts':len(commands),'byte_exact_outputs':len(outputs)}),flush=True)
if __name__=='__main__':main()
