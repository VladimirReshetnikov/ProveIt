"""Untrusted proof-producing equality compiler for root_seed_checker.py."""
import root_seed_checker as kernel


def S(term):
    return ['S', term]


def I(counter, seed, binder, update):
    return ['I', counter, seed, binder, update]


def Eq(left, right):
    return ['=', left, right]


class Producer:
    def __init__(self, reserved=()):
        self.used = set(reserved)
        self.serial = 0

    def fresh(self):
        while True:
            result = '_p' + str(self.serial)
            self.serial += 1
            if result not in self.used:
                self.used.add(result)
                return result

    def refl(self, term):
        zero_box = I(0, term, self.fresh(), 0)
        computation = ['comp', zero_box]
        return ['root', computation, computation]

    def sym(self, proof, context=(), scope=frozenset()):
        result = kernel.infer(proof, context, scope)
        assert result[0] == '='
        return ['root', proof, self.refl(result[1])]

    def trans(self, first, second, context=(), scope=frozenset()):
        return ['root', self.sym(first, context, scope), second]

    def congruence(self, equality, template, variable, context=(), scope=frozenset()):
        _, left, right = kernel.infer(equality, context, scope)
        self.used |= kernel.names(template) | kernel.names(left) | kernel.names(right) | set(scope)
        binder = self.fresh()
        body = kernel.substitute(template, variable, binder)
        left_box = ['comp', I(S(0), left, binder, body)]
        right_box = ['comp', I(S(0), right, binder, body)]
        reversed_result = ['root', right_box, ['seed', equality, left_box]]
        return self.sym(reversed_result, context, scope)

    def transport(self, equality, proof, template, variable, context=(), scope=frozenset()):
        _, old, new = kernel.infer(equality, context, scope)
        self.used |= kernel.names(template) | kernel.names(old) | kernel.names(new) | set(scope)
        template = self.alpha_away(template, set(scope) | {variable})
        assert kernel.same(kernel.infer(proof, context, scope),
                           kernel.substitute(template, variable, old))
        target = kernel.substitute(template, variable, new)
        count = len(context)
        if template[0] == '=':
            left_eq = self.congruence(equality, template[1], variable, context, scope)
            right_eq = self.congruence(equality, template[2], variable, context, scope)
            changed = ['root', left_eq, proof]
            return self.trans(changed, right_eq, context, scope)
        if template[0] == 'D':
            _, first, second, body = template
            witness, step = self.fresh(), self.fresh()
            source_body = kernel.substitute(body, variable, old)
            source_closure = ['Q', second, kernel.substitute(source_body, first, witness)]
            target_body = kernel.substitute(target[3], first, witness)
            base = kernel.substitute(target_body, second, 0)
            extended = (*context, source_closure, base)
            extended_scope = scope | {witness, step}
            equation = weaken(equality, count, 2)
            base_template = kernel.substitute(kernel.substitute(body, first, witness), second, 0)
            reverse_eq = self.sym(equation, extended, extended_scope)
            source_base = self.transport(reverse_eq, ['hyp', count + 1],
                                         base_template, variable, extended, extended_scope)
            source_successor = ['qelim', ['hyp', count], source_base, S(step)]
            successor_template = kernel.substitute(kernel.substitute(body, first, witness),
                                                   second, S(step))
            successor = self.transport(equation, source_successor, successor_template,
                                       variable, extended, extended_scope)
            introduced = ['intro', target, witness, step, 'case', successor]
            return ['delim', proof, witness, introduced]
        assert template[0] == 'Q'
        _, second, body = template
        witness_binder, step, opened = self.fresh(), self.fresh(), self.fresh()
        base = kernel.substitute(target[2], second, 0)
        extended = (*context, base)
        extended_scope = scope | {step}
        equation = weaken(equality, count, 1)
        base_template = kernel.substitute(body, second, 0)
        source_base = self.transport(self.sym(equation, extended, extended_scope),
                                     ['hyp', count], base_template, variable,
                                     extended, extended_scope)
        source_successor = ['qelim', weaken(proof, count, 1), source_base, S(step)]
        successor_template = kernel.substitute(body, second, S(step))
        successor = self.transport(equation, source_successor, successor_template,
                                   variable, extended, extended_scope)
        paired_goal = ['D', witness_binder, second, target[2]]
        introduced = ['intro', paired_goal, 0, step, 'case', successor]
        return ['delim', introduced, opened, ['hyp', count]]

    def alpha_away(self, expression, avoid):
        if type(expression) is not list:
            return expression
        tag = expression[0]
        if tag in ('I', 'Q', 'D'):
            if tag == 'I':
                prefix = ['I', self.alpha_away(expression[1], avoid),
                          self.alpha_away(expression[2], avoid)]
                binders, body = [expression[3]], expression[4]
            elif tag == 'Q':
                prefix, binders, body = ['Q'], [expression[1]], expression[2]
            else:
                prefix, binders, body = ['D'], expression[1:3], expression[3]
            for index, binder in enumerate(binders):
                if binder in avoid:
                    fresh = self.fresh()
                    body = kernel.substitute(body, binder, fresh)
                    binders[index] = fresh
            return prefix + binders + [self.alpha_away(body, avoid | set(binders))]
        return [tag, *(self.alpha_away(child, avoid) for child in expression[1:])]

    def ordinary_successor(self, counter, seed, binder, update, context=(), scope=frozenset()):
        """Derive the unsplit IS schema without changing passive parameters."""
        generic, unused, step, opened = (self.fresh() for _ in range(4))
        old_value = I(generic, seed, binder, update)
        matrix = Eq(I(S(generic), seed, binder, update),
                    kernel.substitute(update, binder, old_value))
        base_direct = ['comp', I(S(0), seed, binder, update)]
        zero_direct = ['comp', I(0, seed, binder, update)]
        base_congruence = self.congruence(zero_direct, update, binder, context, scope)
        base = self.trans(base_direct, self.sym(base_congruence, context, scope), context, scope)
        paired = ['D', unused, generic, matrix]
        successor = ['comp', I(S(S(step)), seed, binder, update)]
        introduced = ['intro', paired, 0, step, 'case', successor]
        conclusion = ['qelim', ['hyp', len(context)], weaken(base, len(context), 1), counter]
        return ['delim', introduced, opened, conclusion]


def weaken(proof, original_context_length, added):
    """Insert new retained formulas before all local binders of a proof."""
    rule = proof[0]
    if rule == 'hyp':
        index = proof[1]
        return ['hyp', index + added if index >= original_context_length else index]
    if rule == 'comp':
        return proof
    if rule in ('root', 'seed'):
        return [rule, *(weaken(child, original_context_length, added) for child in proof[1:])]
    if rule == 'intro':
        return [*proof[:-1], weaken(proof[-1], original_context_length, added)]
    if rule == 'qelim':
        return ['qelim', weaken(proof[1], original_context_length, added),
                weaken(proof[2], original_context_length, added), proof[3]]
    if rule == 'delim':
        return ['delim', weaken(proof[1], original_context_length, added), proof[2],
                weaken(proof[3], original_context_length, added)]
    raise ValueError('unknown proof')


def nodes(proof):
    rule = proof[0]
    if rule in ('hyp', 'comp'):
        return 1
    if rule in ('root', 'seed'):
        return 1 + nodes(proof[1]) + nodes(proof[2])
    if rule == 'intro':
        return 1 + nodes(proof[-1])
    if rule in ('qelim', 'delim'):
        return 1 + nodes(proof[1]) + nodes(proof[2] if rule == 'qelim' else proof[3])
    raise ValueError('unknown proof')
