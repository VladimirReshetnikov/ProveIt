from pathlib import Path
ROOT=Path(__file__).resolve().parent
BASE=ROOT/'reference/scalar_shared.py'
s=BASE.read_text()
s=s.replace('def rec(n, a, h):\n    return [n, a, h]', 'def rec(n, a, h):\n    return a if n == 0 else [n, a, h]')
# The old scalar validator has a separate unary-successor branch.
s=s.replace('(len(t) == 3 and term(t[0], n)', '(len(t) == 3 and t[0] != 0 and term(t[0], n)')
a=s.index("    if tag == 'z'")
b=s.index("    if tag == 'x'", a)
s=s[:a]+s[b:]
a=s.index('def reverse(')
b=s.index('\n\ndef derive(',a)
s=s[:a]+s[b+2:]
s=s.replace('return reverse(subst(closure[1], [witness]))', 'return subst(closure[1], [witness])')
a=s.index("    if tag == 'x'")
b=s.index("    if tag == 'q'",a)
prefix,suffix=s[:a],s[b:]
common='''        equation = derive(major, context, scope)
        if equation[0] != '=':
            fail()
        previous = derive(minor, context, scope)
'''
old='''    if tag == 'x' and len(proof) == 4:
        template, major, minor = proof[1:]
        if not term(template, scope + 1):
            fail()
'''+common+'''        if previous[0] != '=' or previous[1] != subst(template, [equation[1]]):
            fail()
        return ['=', previous[2], subst(template, [equation[2]])]
'''
new='''    if tag == 'x' and len(proof) == 3:
        equation = derive(proof[1], context, scope)
        previous = derive(proof[2], context, scope)
        if equation[0] != '=' or previous[0] != '=':
            fail()
        source, target = equation[1:]
        left, right = previous[1:]
        if left != source:
            if type(left) is not list or len(left) != 3 or left[1] != source:
                fail()
            target = rec(left[0], target, left[2])
        return ['=', right, target]
'''

old = old.replace("        equation = derive(major, context, scope)\n        if equation[0] != '=':\n            fail()\n        previous = derive(minor, context, scope)\n        if previous[0] != '=' or previous[1] != subst(template, [equation[1]]):\n            fail()\n        return ['=', previous[2], subst(template, [equation[2]])]", "        _, source, target = derive(major, context, scope)\n        _, left, right = derive(minor, context, scope)\n        if left != subst(template, [source]):\n            fail()\n        return ['=', subst(template, [target]), right]")
new = new.replace("return ['=', right, target]", "return ['=', target, right]")
explicit = new
new = new.replace("type(left) is not list or len(left) != 3 or left[1] != source", "left[1] != source").replace("rec(left[0], target, left[2])", "[left[0], target, left[2]]")
new = new.replace("        equation = derive(proof[1], context, scope)\n        previous = derive(proof[2], context, scope)\n        if equation[0] != '=' or previous[0] != '=':\n            fail()\n        source, target = equation[1:]\n        left, right = previous[1:]", "        _, source, target = derive(proof[1], context, scope)\n        _, left, right = derive(proof[2], context, scope)")
for name, branch, title in [('general_context', old, 'General one-context ordinary transport'),('seed_checked',explicit,'Template-free transport with explicit shape checks'),('seed_only',new,'Template-free transport using proved-term invariants')]:
 out=prefix+branch+suffix
 first=out.index('"""')
 last=out.index('"""',first+3)+3
 out='"""'+title+'''.
Strict six-rule zero-canonical scalar arithmetic; ordinary Q elimination.
The entire command-line checker is contained in this one module.
"""'''+out[last:]
 (ROOT/(name+'.py')).write_text(out)
