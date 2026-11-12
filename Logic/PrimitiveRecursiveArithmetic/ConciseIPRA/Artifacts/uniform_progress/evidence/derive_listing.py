def derive(proof, context=(), scope=0):
    require(type(proof) is list and proof)
    rule, *args = proof
    if rule == "hyp":
        index, = args
        require(type(index) is int and 0 <= index < len(context))
        return context[index]
    if rule == "zero":
        seed, body = args
        require(term(seed, scope) and term(body, scope + 1))
        return ["=", ["i", 0, seed, body], seed]
    if rule == "succ":
        counter, seed, body = args
        require(term(counter, scope) and term(seed, scope) and term(body, scope + 1))
        return ["=", ["i", ["s", counter], seed, body], instance(body, ["i", counter, seed, body])]
    if rule == "tr":
        matrix, major, minor = args
        require(formula(matrix, scope + 1) and matrix[0] == "=")
        equality = derive(major, context, scope)
        require(equality[0] == "=")
        require(derive(minor, context, scope) == instance(matrix, equality[1]))
        return instance(matrix, equality[2])
    if rule == "use":
        source, seed, major, minor = args
        require(term(source, scope) and term(seed, scope))
        closure = derive(major, context, scope)
        require(closure[0] == "q")
        matrix = closure[1]
        source = source if matrix[0] == "=" else 0
        require(derive(minor, context, scope) == instance(matrix, source))
        return instance(matrix, ["i", source, seed, ["s", ["v", 0]]])
    if rule == "elim":
        conclusion, major, continuation = args
        require(formula(conclusion, scope))
        paired = derive(major, context, scope)
        require(paired[0] == "d")
        local = (["q", paired[1]],) + tuple(lift(item) for item in context)
        require(derive(continuation, local, scope + 1) == lift(conclusion))
        return conclusion
    if rule == "intro":
        matrix, witness, premise = args
        require(formula(matrix, scope + 2) and term(witness, scope))
        body = substitute(matrix, 1, lift(witness))
        source = ["v", 0] if body[0] == "=" else 0
        local = (fresh_instance(body, source),) + tuple(lift(item) for item in context)
        require(derive(premise, local, scope + 1) == fresh_instance(body, ["s", ["v", 0]]))
        return ["d", matrix]
    raise ValueError("Unknown inference rule")
