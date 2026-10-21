"""Veroff-style proof shortening: rerun the hinted search without one hint at a time.

  python shrink.py START.txt BEST.txt ROUNDS     (env MAXW, TMO, CPEN, JOBS, EXE; NOZ and GOALS reach cdr)

Hints are the formulas of the current best proof; random perturbations add a few
formulas from the file named by EXTRA (say, the statements of an earlier derivation).  Untrusted."""
import subprocess, sys, os, random, concurrent.futures as cf, shutil

EXE = os.environ.get('EXE') or os.path.join(os.path.dirname(os.path.abspath(__file__)), 'target', 'release', 'cdr')
W = int(os.environ.get('MAXW', '40'))
TMO = int(os.environ.get('TMO', '25'))
CPEN = os.environ.get('CPEN', '3')

def formulas(path):
    lines = open(path).read().split('\n')
    i0 = next(i for i, l in enumerate(lines) if l.startswith('PROOF'))
    return [l.split(' ')[3] for l in lines[i0 + 1:] if l.strip() and not l.startswith('#') and l.split(' ')[3] != 'Z']

def run(hints, tag):
    hp = 'tmp/h_%s.txt' % tag
    op = 'tmp/o_%s.txt' % tag
    open(hp, 'w').write('\n'.join(hints) + '\n')
    try:
        subprocess.run([EXE, str(W), '1', '3000000', CPEN, hp, '1'], stdout=open(op, 'w'),
                       stderr=subprocess.DEVNULL, timeout=TMO)
    except subprocess.TimeoutExpired:
        return None, op
    first = open(op).readline()
    if first.startswith('PROOF'):
        return int(first.split()[1]), op
    return None, op

def main(start, out, rounds):
    os.makedirs('tmp', exist_ok=True)
    best = start
    bestn = int(open(best).readline().split()[1]) if open(best).readline().startswith('PROOF') else 10**9
    extra = [l.strip() for l in open(os.environ['EXTRA']) if l.strip()] if 'EXTRA' in os.environ else []
    for rd in range(rounds):
        hs = formulas(best)
        cands = []
        for i in range(len(hs)):
            cands.append(hs[:i] + hs[i + 1:])
        for _ in range(len(hs) // 2):
            cands.append([h for h in hs if random.random() > 0.15] + random.sample(extra, min(3, len(extra))))
        improved = False
        with cf.ThreadPoolExecutor(int(os.environ.get('JOBS', '6'))) as ex:
            futs = [ex.submit(run, c, '%d_%d_%d' % (os.getpid(), rd, k)) for k, c in enumerate(cands)]
            for f in cf.as_completed(futs):
                n, op = f.result()
                if n is not None and n < bestn:
                    bestn = n
                    shutil.copy(op, out)
                    best = out
                    improved = True
                    print('round', rd, 'new best', n, flush=True)
        print('round', rd, 'best', bestn, flush=True)
        if not improved:
            break

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]))
