"""Exact outer/native-AND semantics for deletion of the recoder geometry.
No complete Pell witness or universal-history zero is materialized.
"""
import argparse
from functools import lru_cache
from pathlib import Path
import hashlib
import json

DIRECTORY = Path(__file__).resolve().parent
LOCAL_DEPENDENCIES = (
    'affine_history_linear_forms.py',
    'binary_tag_four_tile_history.py',
    'complete75_bounded_packing_elimination105.py',
    'complete75_bounded_projection_elimination99.py',
    'complete75_coupled_index_linear88.py',
    'complete75_gamma_dominance_elimination102.py',
    'complete75_half_binomial.py',
    'complete75_half_binomial_compiler.py',
    'complete75_norm_product89.py',
    'complete75_norm_product90.py',
    'complete75_norm_product91.py',
    'complete75_normalized_strong87.py',
    'complete75_positive_elimination.py',
    'complete75_positive_root89.py',
    'complete75_reversed_auxiliary89.py',
    'complete75_signed_projection_elimination101.py',
    'explore_one_field_half_mask.py',
    'gpcp_bracket_anchored_history.py',
    'gpcp_checksum_global_units771.py',
    'gpcp_complete_fixed_program.py',
    'gpcp_complete_fixed_program_units.py',
    'gpcp_coupled_index_units754.py',
    'gpcp_first_padding_units763.py',
    'gpcp_fixed_program_input_bridge.py',
    'gpcp_index_linear_units757.py',
    'gpcp_normalized_strong_compiler.py',
    'gpcp_ordered_sparse_tm.py',
    'gpcp_positive_bound_units767.py',
    'gpcp_shared_selectors774.py',
    'gpcp_slope_class_compiler.py',
    'gpcp_sparse_tm_compiler.py',
    'gpcp_state_free_copies.py',
    'gpcp_upper_transport_unit765.py',
    'group_linked_binary_geometry47.py',
    'native_binary_input_dilation129.py',
    'native_binary_input_dilation130.py',
    'native_binary_input_dilation132.py',
    'native_binary_input_dilation_unit179.py',
    'native_binary_masked_selection63.py',
    'native_binary_masked_selection65.py',
    'native_binary_three_row_fifo58.py',
    'native_controller_binary_selector56.py',
    'native_controller_three_selector_53.py',
    'neary_woods_explicit_universal_tm.py',
    'neary_woods_prefix_universal.py',
    'pcp_affine_factored_transports.py',
    'pcp_affine_slope_class_history.py',
    'pcp_normalized_strong_history_units.py',
    'pcp_uniform_affine_pair_history.py',
    'pcp_uniform_affine_pair_units.py',
    'pell_kernel_half_binomial42.py',
    'pell_kernel_power_two43.py',
    'sparse_tm_rewriting.py',
)
DEPENDENCY_MANIFEST_SHA256 = '1bf4ae94bb2db40242baf547b78ac715aedf28592cc2d4108dff76f7a82bc00c'

def source_guard():
    manifest = {name: hashlib.sha256((DIRECTORY/name).read_bytes()).hexdigest()
                for name in LOCAL_DEPENDENCIES}
    digest = hashlib.sha256(json.dumps(manifest,sort_keys=True,separators=(',', ':')).encode()).hexdigest()
    assert digest == DEPENDENCY_MANIFEST_SHA256, 'frozen local dependency source mismatch'
    return manifest


source_guard()
import native_binary_input_dilation129 as width2
import gpcp_fixed_program_input_bridge as bridge
import gpcp_index_linear_units757 as current757
import gpcp_coupled_index_units754 as current754


@lru_cache(None)
def _packet(k, compiled_stage):
    source_guard()
    return ((current757 if compiled_stage == 757 else current754).build()
            if compiled_stage is not None else width2.build() if k == 2 else bridge.recoder(k))


def subset(source, values, targets):
    assert type(source) is list and type(values) is dict and type(targets) is list and targets
    assert all(type(n) is str and type(value) is int for n,value in values.items())
    assert all(type(n) is str for n in targets)
    assert all(type(row) is tuple and len(row)==4 and type(row[0]) is str
        and type(row[1]) is str and row[1] in ('+', '-', '*')
        and all(type(value) in (int, str) for value in row[2:]) for row in source)
    by = {n: (op, a, b) for n, op, a, b in source}
    assert len(by) == len(source), 'duplicate literal register'
    available = set()
    for n, op, a, b in source:
        # Only demanded rows need their leaves supplied, but source definitions
        # cannot be forward references or cyclic references to another row.
        assert all(type(v) is int or v not in by or v in available for v in (a,b))
        available.add(n)
    need = set(); todo = list(targets)
    while todo:
        n = todo.pop()
        if not isinstance(n, str) or n in need: continue
        need.add(n)
        if n in by: todo.extend(by[n][1:])
        else: assert n in values, ('missing literal-source leaf', n)
    env = dict(values); used = []
    for n, op, a, b in source:
        if n not in need: continue
        x = env[a] if isinstance(a, str) else a
        y = env[b] if isinstance(b, str) else b
        env[n] = x+y if op == '+' else x-y if op == '-' else x*y
        used.append((n, op, a, b))
    return env, used


def digest(n):
    assert type(n) is int and n >= 0
    return dict(bits=n.bit_length(), population=n.bit_count(),
        sha256_unsigned_big_endian=hashlib.sha256(n.to_bytes((n.bit_length()+7)//8, 'big')).hexdigest())


def fixture(k, a, h=1, compiled_stage=None):
    assert type(k) is type(a) is type(h) is int and (k == 2 or k >= 4) and a >= k and h in (0, 1)
    assert compiled_stage is None or type(compiled_stage) is int and compiled_stage in (757,754)
    assert compiled_stage is None or k == 64
    x = 1; q = 1 << a; Q = 1 << (k*a); b = k*a+k-1; B = 1 << b
    t = a+h*(b+1); m = a+h*b
    P = 1 << (b*t); S = 1 << (a+b*t)
    J, rem = divmod(P-1, B-1); assert rem == 0
    K, rem = divmod(S-1, 2*B-1); assert rem == 0
    assert a+b*t == (b+1)*m
    A = J & K
    expected_A = 1 if h == 0 else 1+(1 << (b*(b+1)))
    assert A == expected_A
    z = A % (Q-1)
    expected_z = 1 if h == 0 else 1+(1 << (k*(k-1)))
    assert z == expected_z and 0 < z < Q-1
    mistaken_input = 1 if h == 0 else 1+(1 << (k-1))
    assert z == bridge.spread(mistaken_input, k)
    assert (z == bridge.spread(x, k)) == (h == 0)
    quotient, rem = divmod(A-z, Q-1); assert rem == 0
    v = dict(x=x,z=z,q=q,P=P,J=J,K=K,Ahat=A+1,quotient_hat=quotient+1,
             input_slack=q-x,output_slack=Q-z)
    assert all(n > 0 for n in v.values())
    assert J > B and J > q and J >= 9 and J % 2 == 1
    assert J.bit_count() == t
    assert (q == 1 << J.bit_count()) == (h == 0)
    assert 0 < J < S and 0 < K < S and S & (S-1) == 0
    F = [16*(S-1-(J|K))+1, 16*(J-A)+4, 16*(K-A)+2, 16*A+8]
    assert all(f > 0 for f in F)
    assert sum(F)+1 == 16*S
    assert F[1]+F[3] == 16*J+12 and F[2]+F[3] == 16*K+10
    v.update({f'and__F{i}':F[i] for i in range(3)})
    packet = _packet(k,compiled_stage)
    if compiled_stage is not None:
        assert [row for row in packet['source'] if row[0]=='B'] == [('B','*',1 << 63,'Q')]
        # This paid input-word repunit is independent of the deleted geometry.
        v['input_repunit'], rem = divmod(Q-1, (1 << 64)-1); assert rem == 0
        pairs = [('mask_scale','scale'),('congruence_left','congruence_right'),
                 ('output_bound','Q'),('input_repunit_power','Q'),('and__input_B','and__padded_B')]
        assert all(pair in packet['comparisons'] for pair in pairs)
        target_names = [n for pair in pairs for n in pair]+['input_bound','repunit_P','B',
            'and__q','and__F3','and__input_A','and__padded_A','and__bs_q','and__first_padding_unit']
        env, rows = subset(packet['source'],v,target_names)
        assert env['input_bound']==q and env['repunit_P']==P
        assert env['and__bs_q']==env['and__first_padding_unit']==1
        assert env['and__padded_A']-env['and__input_A']==1
    else:
        pairs = packet['comparisons'][:5]
        target_names = [n for pair in pairs for n in pair]+[
            'and__q','and__F3','and__input_A','and__padded_A','and__input_B','and__padded_B','and__bs_q','B']
        env, rows = subset(packet['source'],v,target_names)
        assert env['and__input_A']==env['and__padded_A']
        assert env['and__input_B']==env['and__padded_B']
        assert env['and__bs_q']==env['and__q']
    assert all(env[a]==env[b] for a,b in pairs)
    assert env['B']==B and env['and__q']==16*S and env['and__F3']==F[3]
    result = dict(width=k, exponent=a, extra_period=h, log2_B=b, repunit_duration=t,
        mask_duration=m, wrong_input=mistaken_input, outer_source_rows=len(rows),
        literal_comparisons_checked=pairs, compiled_stage=compiled_stage, outer_source=rows,
        values={n:digest(value) for n,value in dict(v,Q=Q,B=B,S=S,A=A).items() if not n.startswith('and__')},
        and_truth_fields=[digest(f) for f in F], geometry_population=J.bit_count(),
        geometry_required_population=a, geometry_rejected=(h==1),
        source_sha256=hashlib.sha256(json.dumps(packet['source'],separators=(',',':')).encode()).hexdigest())
    if k==2 and a==2:
        result['exact_small_values']={n:v[n] for n in ('x','z','q','P','J','K','Ahat','quotient_hat','input_slack','output_slack')}
        result['exact_small_fields']=F
    return result


def guards():
    count=0
    def reject(fn):
        nonlocal count
        try:fn()
        except (AssertionError,KeyError,TypeError,ValueError):count+=1
        else:raise AssertionError('malformed caller accepted')
    for args in ((True,2),(2.0,2),(2,True),(2,2.0),(1,2),(3,3),(4,3),
                 (2,2,True),(2,2,0.0),(2,2,-1),(2,2,2)):
        reject(lambda args=args:fixture(*args))
    for stage in (True,754.0,756,'754'):
        reject(lambda stage=stage:fixture(64,64,compiled_stage=stage))
    reject(lambda:fixture(2,2,compiled_stage=754))
    for value in (True,1.0,-1,'1',None):reject(lambda value=value:digest(value))
    good=[('y','+', 'x',1),('z','*','y',2)]
    for rows in (tuple(good),[list(good[0]),good[1]],good+[good[0]],
                 [('y','/', 'x',1)], [('y','+','x',True)], [('y','+','x',1.0)],
                 [(1,'+','x',1)], [('y','+','z',1),('z','*','y',2)]):
        reject(lambda rows=rows:subset(rows,{'x':1},['y']))
    for values in ({'x':True},{'x':1.0},{1:1},[],{}):
        reject(lambda values=values:subset(good,values,['z']))
    reject(lambda:subset([('y','+','z',1),('z','*','y',2)],{'z':1},['y']))
    for targets in ((),[],['missing'],[1],[True]):
        reject(lambda targets=targets:subset(good,{'x':1},targets))
    # Returned guard manifests cannot poison the fixed source comparison.
    damaged=source_guard();damaged.clear();assert len(source_guard())==len(LOCAL_DEPENDENCIES)
    assert subset(good,{'x':1},['z'])[0]['z']==4
    return count


def verify():
    cases=[]
    for k in (2,4,5,8,16):
        for a in range(k,k+4):
            for h in (0,1): cases.append(fixture(k,a,h))
    for stage in (757,754):
        for h in (0,1): cases.append(fixture(64,64,h,stage))
    assert all(cases[-4+i]['outer_source']==cases[-2+i]['outer_source'] for i in (0,1))
    congruences=0
    for k in range(2,17):
        for a in range(k,k+5):
            b=k*a+k-1
            for t in range(1,3*(b+1)):
                # Exponent divisibility iff the literal second repunit is integral.
                # Use modular exponentiation to avoid huge numerals in this sweep.
                integral=pow(2,a+b*t,(1 << (b+1))-1)==1
                assert integral == ((t-a) % (b+1)==0)
                congruences+=1
    return dict(status='PASS_RECODER_GEOMETRY_DELETION_ALIAS',cases=cases,
        exact_exponent_congruence_cases=congruences,
        source_files=source_guard(), dependency_manifest_sha256=DEPENDENCY_MANIFEST_SHA256,
        rejected_callers=guards(),
        scope='Exact imported outer-DAG and prescribed-AND semantic fixtures. Complete positive AND extension follows from its retained theorem; no Pell witness, deleted-kernel complete polynomial, or universal-history false zero is materialized.')

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result, 'receipt mismatch'
    print(result['status'])
    print({k:v for k,v in result.items() if k not in ('cases','source_files')})
