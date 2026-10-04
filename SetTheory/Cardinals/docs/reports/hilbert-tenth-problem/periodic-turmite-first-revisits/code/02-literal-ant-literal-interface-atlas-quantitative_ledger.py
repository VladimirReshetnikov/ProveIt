#!/usr/bin/env python3
"""Explicit conservative geometric/work ledger; no arithmetic-circuit cost claim."""
if not __debug__:raise RuntimeError('Assertions required')
import hashlib,json,pathlib
from generator import Atlas
R=pathlib.Path(__file__).resolve().parents[1]
a=Atlas();p=a.program
owned={k:len(v)for k,v in a.maps.items()};M=2*max(owned.values())
C=(a.R+1)*(a.K+4)*M+(a.K+a.W+8)*M+2*a.F+2396
obs=p['observer_local_head_state'];clauses=[(obs[0],obs[1],2),((obs[0]+a.S//2)%a.S,obs[1]+a.V,2)]
normalized=[((y-75)%(2*a.V),(288650-x)%a.S,1)for x,y,h in clauses]
assert normalized==[(240606225575,317948,1),(481225262775,29948,1)]
assert all((x+y)%2==1 for x,y,h in normalized)
result={'status':'EXACT_CONSERVATIVE_GEOMETRIC_LEDGER_PENDING_FINAL_GATE','template_owned_cells':owned,
 'per_finite_resource_history_bound':M,'basis':'At most two departures at each owned cell; this maximum covers all finite template pieces, including marker joints and row turns.',
 'program_instruction_rounds':a.R,'active_storage_columns':a.K,'all_storage_columns_in_CA_copy_sweep':a.W,
 'cell_width':a.S,'cell_height':a.V,'rectangular_period':[a.S,2*a.V],
 'normal_C_margin_route_departures':2*a.F+2396,'C_control_departure_upper_bound':C,
 'C_control_bound_formula':'(R+1)(K+4)M+(K+W+8)M+2F+2396; intentionally overcounts shared marker/header pieces and complete resource histories.',
 'CA_rounds_to_C_count':'T(m+1)+T(T-1)/2, where m=len(left)+len(right)+1',
 'TM_halt_step_to_ant_departures':'For a U15 halt at t>=1, at most [2t(m+1)+t(2t-1)]*C_control_departure_upper_bound ant departures are needed to reach an accepting port.',
 'input_support_cells':'2812+4*(popcount(left)+popcount(right))',
 'input_support_box':{'x_min':288617,'x_max':'576000*m+264705','y_min':-144,'y_max':76},
 'input_source_word':'reverse(left), A0, right; each argument is a finite nearest-head-first bit list, including explicit zero-only lengths',
 'coordinate_bound_through_T_CA_rounds':{'absolute_x':'576000*(m+T+2)','y_min':-144,'y_max':'240619037200*(T+1)+659'},
 'coordinate_bit_budget':'Signed O(log(m+T+2)+39) bits; all template/program data are fixed constants',
 'random_access_coloring':'A fixed finite template family plus958 compressed-program records; row lookup uses binary searches and a24-operation SWAP grammar. No iteration through601547591 rows or dense tile materialization is required.',
 'fixed_initial_head':[288650,75,1],'acceptance_clauses':clauses,'pre_departure':True,'stencil':[],
 'normalized_north_start':{'transform':['X=y-75','Y=288650-x'],'head':[0,0,0],'period':[2*a.V,a.S],
  'acceptance_clauses':normalized,'accepting_checkerboard':'odd, hence white','174_heading_port':'FinalSignPlus=1 gives incoming E at these white sites'},
 'arithmetic_operations_added_to_174':'NOT_COUNTED_OR_CLAIMED',
 'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
(R/'atlas/quantitative_ledger.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'M':M,'C_departure_bound':C,'period':[a.S,2*a.V],'input_count':result['input_support_cells']}))
if __name__=='__main__':pass
