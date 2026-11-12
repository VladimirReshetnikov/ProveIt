"""Untrusted checked proof translations between three equivalent interfaces.

Usage: python3 translate.py SOURCE TARGET INPUT.json OUTPUT.json
SOURCE/TARGET are seed, step, or control. The final formula is unchanged.
"""
import importlib.util
import json
from pathlib import Path
import sys

from proofs import Builder

ROOT = Path(__file__).resolve().parent
FILES = {'seed': 'checker.py', 'step': 'control_step.py',
         'control': 'control_computation_transport.py'}


def kernel(mode):
    path = ROOT / FILES[mode]
    spec = importlib.util.spec_from_file_location('kernel_' + mode, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def transform(proof, source_mode, target_mode, context=(), scope=0):
    source = kernel(source_mode)
    builder = Builder(target_mode)

    def visit(p, retained, count):
        if p[0] == 'r':
            return (builder.comp(*p[1:]) if source_mode == 'control'
                    else builder.refl(p[1]))[2]
        if p[0] == 'x':
            if source_mode == 'control':
                template, major, minor = p[1:]
            else:
                major, minor = p[1:]
            left = source.derive(major, retained, count)
            right = source.derive(minor, retained, count)
            q = (*left[1:], visit(major, retained, count))
            r = (*right[1:], visit(minor, retained, count))
            if source_mode == 'control':
                return builder.transport(q, r, template)[2]
            return (builder.seed(q, r) if source_mode == 'seed'
                    else builder.step(q, r))[2]
        if p[0] == 'u':
            return ['u', p[1], p[2], visit(p[3], retained, count)]
        tag, goal, data, branch = p
        fresh = -count - 1
        if tag == 'e':
            paired = source.derive(data, retained, count)
            body = source.opening(paired[1], fresh, 1)
            clause = (source.opening(body, 0), body)
            out_data = visit(data, retained, count)
        elif tag == 'i':
            body = source.opening(goal[1], data, 1)
            eta = fresh if goal[1][0] == '=' and data == 0 else 0
            clause = (['=', 0, 0], source.opening(body, eta))
            out_data = data
        else:
            raise ValueError('Unknown source proof tag')
        return [tag, goal, out_data, visit(branch, retained + [clause], count + 1)]

    return visit(proof, list(context), scope)


def translate_certificate(certificate, source_mode, target_mode):
    kernel(source_mode).verify(certificate)
    result = {'goal': certificate['goal'],
              'proof': transform(certificate['proof'], source_mode, target_mode)}
    kernel(target_mode).verify(result)
    return result


if __name__ == '__main__':
    if len(sys.argv) != 5:
        raise SystemExit(__doc__)
    source_mode, target_mode, source_path, output_path = sys.argv[1:]
    certificate = json.loads(Path(source_path).read_text())
    result = translate_certificate(certificate, source_mode, target_mode)
    Path(output_path).write_text(json.dumps(result, separators=(',', ':')) + '\n')
