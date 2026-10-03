"""Audit the bounded dependency guards without changing arithmetic sources.

For a fixed watched set W, (A union B) intersect W equals
(A intersect W) union (B intersect W). Input singleton projection and
induction over the unchanged source therefore give exactly the original
queried intersections at every register. Both implementations retain all
register keys, so missing-name behavior is unchanged. Dependency storage
is O(|W|N), with |W|=2 for scale and5 for normalized strong auxiliaries.

The original full-set functions below differ only in their initialization.
This regression compares complete returned packets and adversarial guard
outcomes, plus every register's dependency intersection. The bounded worker also materializes a complete fixed-machine Wang source
and its framed ordinary-input composition. Frozen arithmetic receipts
remain separate and unchanged.
"""
import argparse
from collections import Counter
import hashlib
import inspect
import json
from pathlib import Path
import random
import subprocess
import sys
import native_binary_norm_units as units
import wang_b_packed_program as program
scale=units.scale

def original(fn,old,new):
 s=inspect.getsource(fn)
 assert s.count(new)==1
 s=s.replace(new,old)
 ns=dict(fn.__globals__);exec(s,ns)
 return ns[fn.__name__]
oldnorm=original(units.normalize,"deps={name:{name} for name in old['parameters']+old['auxiliaries']}","deps={name:({name} if name in rebuilt else set())\n          for name in old['parameters']+old['auxiliaries']}")
oldscale=original(scale.rewrite,"dependencies={n:{n} for n in old['parameters']+old['auxiliaries']}","dependencies={n:({n} if n in {w,beta} else set())\n                  for n in old['parameters']+old['auxiliaries']}")

def deps_audit(p,watched):
 full={n:{n} for n in p['parameters']+p['auxiliaries']}
 thin={n:({n} if n in watched else set()) for n in full}
 for n,_,a,b in p['source']:
  full[n]=(full[a] if isinstance(a,str) else set())|(full[b] if isinstance(b,str) else set())
  thin[n]=(thin[a] if isinstance(a,str) else set())|(thin[b] if isinstance(b,str) else set())
  assert thin[n]==full[n]&watched
 assert all(len(x)<=len(watched) for x in thin.values())
 return len(full)

def status(fn,p):
 try:return ('ok',fn(p))
 except (AssertionError,KeyError) as exc:return (type(exc).__name__,)

def small_audit():
    hosts=[]
    for context in ('and','motion','toggle'):
     for scaled in (False,True):
      for computed in ('four','six'):
       hosts.append(units.build(context,scaled=scaled,computed=computed,normalized=False))
    for instructions in [('M',),(('J',1),),('M','R',('J',1),'L')]:
     for literal in (False,True):
      hosts.append(program.build(instructions,literal,'units')['normalized_parent'])
    registers=accepted=rejected=scale_rejections=0
    for p in hosts:
     q=units.normalize(p);r=oldnorm(p);assert q==r
     pre=p['core_prefix'];watch={pre+k for k in ('f','i','j','o','y_aux')}
     registers+=deps_audit(p,watch)
     safe=next(n for n in p['parameters']+p['auxiliaries'] if n not in watch)
     for name in list(watch)+[safe]:
      pp=scale.metadata(dict(p,source=p['source']+[
       ('audit_path0','-',name,name),('audit_path1','+',safe,'audit_path0')],
       public_registers={'nested':{'port':['audit_path1']}}))
      a,b=status(units.normalize,pp),status(oldnorm,pp)
      assert a==b
      registers+=deps_audit(pp,watch)
      if name in watch:assert a[0]!='ok';rejected+=1
      else:assert a[0]=='ok';accepted+=1
    # Independent scale callers, including their actual larger exported DAGs.
    rawhosts=[units.fields.scale.build()['positive_scale_parent']]
    for instructions in [('M',),(('J',1),),('M','R',('J',1),'L')]:
     for literal in(False,True):rawhosts.append(program.compile_raw(instructions,literal))
    for p in rawhosts:
     prefix='native__' if 'native__q' in {r[0] for r in p['source']} else ''
     fn=lambda x:scale.rewrite(x,prefix);old=lambda x:oldscale(x,prefix)
     assert fn(p)==old(p)
     watch={prefix+'w',prefix+'bound_beta'}
     registers+=deps_audit(p,watch)
     # Added paths violate the private-consumer contract in both versions;
     # all projected dependency values are also compared before rejection.
     for name in watch:
      pp=dict(p,source=p['source']+[("audit_scale_path0",'+',name,1),('audit_scale_path1','*','audit_scale_path0',2)])
      registers+=deps_audit(pp,watch)
      a,b=status(fn,pp),status(old,pp)
      assert a==b and a[0]!='ok'
      scale_rejections+=1
     # Synthetic arbitrary DAGs audit both queried sets, including cancellation.
    rng=random.Random(527)
    for width in (2,5):
     for trial in range(32):
      inputs=[f'i{x}' for x in range(30)];known=list(inputs);src=[]
      for j in range(150):
       a=rng.choice(known);b=rng.choice(known+[0,1]);n=f'n{j}'
       src.append((n,rng.choice(('+','-','*')),a,b));known.append(n)
      pp=dict(parameters=inputs,auxiliaries=[],source=src)
      registers+=deps_audit(pp,set(inputs[:width]))
    return dict(actual_norm_hosts=len(hosts),actual_scale_hosts=len(rawhosts),dependency_register_checks=registers,adversarial_rejections=rejected,scale_adversarial_rejections=scale_rejections,benign_extensions=accepted,random_DAGs=64,all_returned_normalized_packets_equal=True)


def execute(source, values):
    env = dict(values)
    for name, op, a, b in source:
        x = env[a] if isinstance(a, str) else a
        y = env[b] if isinstance(b, str) else b
        env[name] = x+y if op == '+' else x-y if op == '-' else x*y
    return env


def close_source(source, output, parameters, auxiliaries):
    scale.checked_source(source, parameters, auxiliaries)
    rows = {n: (a, b) for n, _, a, b in source}
    seen, todo = set(), [output]
    while todo:
        v = todo.pop()
        if not isinstance(v, str) or v not in rows or v in seen:
            continue
        seen.add(v)
        todo.extend(rows[v])
    assert seen == set(rows)
    return len(seen)


def large_audit():
    import resource
    import signal
    import time
    # Limits contain accidental regressions. Observed timing/RSS is printed
    # separately and is deliberately not part of the deterministic receipt.
    resource.setrlimit(resource.RLIMIT_AS, (3584*1024**2, 3584*1024**2))
    resource.setrlimit(resource.RLIMIT_CPU, (150, 155))
    signal.alarm(180)
    import wang_b_erasing_bridge_compiler as records
    bridge = records.bridge
    started = time.monotonic()
    bt, _, macro = records.binary(records.DEFAULT)
    assert len(bt) == 1481 and len(macro) == 42
    child = bridge.build(bt, ordinary_input=False)
    child_source, child_out = bridge.polynomial_source(child)
    child_ledger = bridge.ledger(child)
    child_degree = units.degree_bound(child)['degree_upper_bound']
    assert child_degree <= child_ledger['degree_upper_bound']
    child_closure = close_source(child_source, child_out, child['parameters'], child['auxiliaries'])
    child_hash = hashlib.sha256(repr(child_source).encode()).hexdigest()
    assert child_hash == 'ea40aeb6c0aeb08000c1f9fc38ea91174d4b5276e9ec31c6a8a69319207693b5'
    assert (len(child_source), child['operations'], child['equations'], child['witnesses']) == (312749, 312723, 9, 23725)
    loader = records.loader()
    loader_source, loader_out = records.recoder.polynomial_source(loader)
    assert len(loader_source) == 190
    rn = lambda v: ('x' if v == 'x' else 'rec__'+v) if isinstance(v, str) else v
    wn = lambda v: ('rec__frame_input' if v == 'input' else 'wang__'+v) if isinstance(v, str) else v
    rename = lambda rows, f: [(f(n), op, f(a), f(b)) for n, op, a, b in rows]
    source = rename(loader_source, rn)+rename(child_source, wn)
    source += [('complete_recoder_square', '*', rn(loader_out), rn(loader_out)),
               ('complete_wang_square', '*', wn(child_out), wn(child_out)),
               ('complete_output', '+', 'complete_recoder_square', 'complete_wang_square')]
    aux = [rn(v) for v in loader['auxiliaries']]+[wn(v) for v in child['auxiliaries']]
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    closure = close_source(source, 'complete_output', ['x'], aux)
    assert len(source) == 312942 and counts == {'M': 118706, 'A': 194236}
    assert len(aux) == len(set(aux)) == 23763
    identities = 0
    max_output_bits = 0
    for case, x in enumerate((1, 2, 5, 9)):
        values = dict.fromkeys(aux, 1)
        values.update(x=x, rec__frame_repunit=1+case%2, rec__z=1+case%2)
        lv = {v: values[rn(v)] for v in loader['parameters']+loader['auxiliaries']}
        le = execute(loader_source, lv)
        cv = {v: values[wn(v)] for v in child['auxiliaries']}
        cv['input'] = le['frame_input']
        # Every action word is0, hence the supplied-history P is1 even
        # off zero. This avoids giant powers in a huge-index finite audit.
        ce = execute(child_source, cv)
        env = execute(source, values)
        assert env['complete_output'] == le[loader_out]**2+ce[child_out]**2
        assert all(env[rn(n)] == le[n] for n, _, _, _ in loader_source)
        assert all(env[wn(n)] == ce[n] for n, _, _, _ in child_source)
        max_output_bits = max(max_output_bits, abs(env['complete_output']).bit_length())
        identities += 1
    observed = dict(elapsed_seconds=round(time.monotonic()-started, 3),
                    peak_RSS_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                    address_space_limit_MiB=3584, cpu_soft_limit_seconds=150,
                    wall_alarm_seconds=180)
    result = dict(table_nonhalting_states=len(bt), block_control_states=len(macro),
        child_ledger=child_ledger, child_guarded_degree_upper_bound=child_degree,
        child_source_sha256=child_hash, child_output_ancestors=child_closure,
        complete=dict(certificate=child['operations']+loader['operations'],
            polynomial=len(source), M=counts['M'], A=counts['A'], comparisons=25,
            witnesses=len(aux), parameters=1, degree_upper_bound=2*max(child_degree, 402),
            source_sha256=hashlib.sha256(repr(source).encode()).hexdigest(),
            output_ancestors=closure),
        namespace_output_identities=identities, maximum_audited_output_bits=max_output_bits,
        scope='Actual materialized fixed-example sources; no universal table or full positive Pell zero.')
    return result, observed


OBSERVED = None


def verify():
    global OBSERVED
    small = small_audit()
    worker = subprocess.run([sys.executable, str(Path(__file__).resolve()), '--large-worker'],
                            check=True, capture_output=True, text=True, timeout=185)
    result, OBSERVED = json.loads(worker.stdout)
    return dict(status='PASS_NATIVE_DEPENDENCY_PROJECTION_AND_LITERAL_WANG',
                dependency_audit=small, literal_source_audit=result,
                guard_widths=dict(positive_scale=2, strong_normalization=5),
                arithmetic_source_and_frozen_receipts_unchanged=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--large-worker', action='store_true')
    args = parser.parse_args()
    if args.large_worker:
        print(json.dumps(large_audit()))
    else:
        result = verify()
        path = Path(__file__).with_suffix('.json')
        if args.write:
            path.write_text(json.dumps(result, indent=2)+'\n')
        else:
            assert json.loads(path.read_text()) == result, 'receipt mismatch'
        print(result['status'])
        print(result['literal_source_audit']['complete'])
        print('Observed resources, not a portability bound:', OBSERVED)
