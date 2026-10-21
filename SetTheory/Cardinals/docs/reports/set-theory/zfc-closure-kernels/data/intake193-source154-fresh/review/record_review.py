from pathlib import Path
import json,hashlib
P=Path('/tmp/zfc-intake193/large/extracted/ZFC_218_Research_2026-10-20')
O=Path('/tmp/zfc-intake193-large-peer')
def desc(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'lines':len(b.splitlines())}
files=['README.md','NOTICE.md','PROVENANCE.json','receipts/README.md']
files += ['report/'+x for x in ('report.tex','overview.tex','theory_results.tex','encoding_results.tex','machine_results.tex','root_results.tex','reproduction.tex','inverse_mp_research.tex','rab_conditional_appendix.tex')]
files += [str(p.relative_to(P)) for p in sorted((P/'research').rglob('*')) if p.suffix in ('.md','.tex')]
code=['portable/construct.py','portable/canonicalize.py','portable/verify_runtime.py','portable/reproduce.py']
code += ['research/theory/'+x for x in ('check_mp_conventions.py','check_shifted_even_codec.py','check_boot_permutations.py','check_membership_blind_detachment.py','check_negative_atoms_core_matrix.py','check_t_template.py')]
code += ['research/encoding/theory_audit/audit_t_native.py']
# Equal duplicate report includes are checked as bytes, not counted as new proof reads.
pairs=[('report/theory_results.tex','research/theory/theory_results.tex'),('report/encoding_results.tex','research/encoding/final_encoding_summary.tex'),('report/inverse_mp_research.tex','research/encoding/inverse_mp_research.tex'),('report/rab_conditional_appendix.tex','research/theory_late/rab_conditional_appendix.tex')]
dups=[{'left':a,'right':b,'identical':(P/a).read_bytes()==(P/b).read_bytes()} for a,b in pairs]
assert [x['identical'] for x in dups] == [True,True,False,True]
dups[2]['reviewed_difference']='Only three LaTeX pathname renderings: path versus escaped texttt; identical mathematical statements.'
base=Path('/tmp/zfc-intake192/fresh1')
libs=[('research/machine/vendor/K221_minimal/portable/source_language.py',base/'packet/code/vendor/source_language.py'),('research/machine/vendor/K221_minimal/portable/build221.py',base/'packet/code/vendor/build221.py'),('research/machine/vendor/K221_minimal/portable/runtime/vendor/symbolic_runtime.py',base/'parent/K218_Dominated_Rho8_2026-10-20/binary/code/runtime/symbolic_runtime.py'),('research/machine/vendor/K221_minimal/portable/runtime/vendor/independent_runtime.py',base/'parent/K218_Dominated_Rho8_2026-10-20/binary/code/runtime/independent_runtime.py'),('research/machine/vendor/K221_minimal/portable/runtime/reference_results/legacy_mapping.json',base/'parent/K218_Dominated_Rho8_2026-10-20/binary/code/inputs/legacy_mapping.json')]
identities=[]
for rel,old in libs:
 p=P/rel
 identities.append({'candidate':desc(p),'prior_accepted_input':desc(old),'identical':p.read_bytes()==old.read_bytes()})
record={'status':'SOURCE_API_REVIEW_COMPLETE','arrival_commit':'1e87618cf2','source_number':154,'reviewer_role':'Independent mathematical/source reviewer; authored earlier omit-zero compiler transfer and current cache-to-dominated transfer, not the submitted Source154 packet. No candidate execution or independent full search replay.','proof_and_report_reads':[desc(P/f) for f in dict.fromkeys(files)],'selected_code_reads':[desc(P/f) for f in code],'duplicate_include_identity':dups,'selected_existing_library_identities':identities,'own_reviewer':desc(Path(__file__)),'execution':{'supplied_code':False,'Coq':False,'Lean':False,'candidate_runtime':False,'manifest_validation':False},'limits':['No independent rerun or audit of all finite search streams.','Supplied historical PASS receipts are evidence attributed to the archive, not fresh root results.','Historical report target218 is superseded by current accepted217 and goal216.','No new state reduction follows from the positive theory calibrations.','Late RAB extraction is conditional; existing unconditional RAB obstructions remain decisive.'],'findings':[]}
(O/'read-inventory.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'documents':len(record['proof_and_report_reads']),'selected_code':len(code),'library_identities':[{'path':x['candidate']['path'],'identical':x['identical']}for x in identities]},indent=2))
