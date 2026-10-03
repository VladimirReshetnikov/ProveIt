"""Run the complete standard-library verification bundle."""
from pathlib import Path
import subprocess,sys,json
root=Path(__file__).resolve().parents[1]
for script in ('verify_gadget_identity.py','verify_unit_witness.py'):
    subprocess.run([sys.executable,str(root/'code'/script)],check=True,capture_output=True,text=True)
g=json.loads((root/'data'/'gadget_identity_verification.json').read_text())
a=json.loads((root/'data'/'unit_rank3450_witness.json').read_text())
b=json.loads((root/'data'/'unit_deficiency_one_witness.json').read_text())
D=160160547610973088925200
assert list(map(int,a['tail_coefficients_r_rminus1_rminus2']))==[455*D*191**4,3020455956*D*191**3,10022638278784267*D*191**2]
assert int(a['endpoint_gap'])==-314102056577041236*D*D*191**6
D1=8567325
assert list(map(int,b['tail_coefficients_r_rminus1_rminus2']))==[69*D1*4181**22,61945839672*D1*4181**21,27806230344578726426*D1*4181**20]
assert int(b['endpoint_gap'])==-415296714996000603216*D1*D1*4181**42
assert a['all_vertex_activities']==b['all_vertex_activities']==1
assert a['matching_and_cover_verified'] and b['matching_and_cover_verified']
assert b['smaller_shore_deficiency']==1
out={'gadget_identity_checks':g['independent_exact_support_checks'],'main_witness_rank':a['matching_rank'],
     'main_witness_vertices':a['vertices'],'main_witness_edges':a['edges'],
     'deficiency_one_rank':b['matching_rank'],'all_vertex_activities_one':True,
     'both_endpoint_margins_negative':True,'printed_factored_certificates_verified':True,
     'matching_and_cover_certificates_verified':True,'all_checks_passed':True}
(root/'data'/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
