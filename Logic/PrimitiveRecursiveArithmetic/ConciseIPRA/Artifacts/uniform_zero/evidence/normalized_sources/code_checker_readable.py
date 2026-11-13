import json

def verify(goal, assumptions, floor=0):

    def opened(expression, replacement=0j, depth=0):
        if isinstance(expression, list):
            child_depth = depth + 5 - len(expression)
            return [opened(child, replacement, child_depth) for child in expression]
        if floor <= expression < depth:
            return expression or 1
        if depth % 2:
            return opened(replacement, depth=3)
        return 0
    if opened(goal) in assumptions:
        return
    major, source, target, template = next_packet()
    if major:
        if source:
            major = [source, target]
        elif template:
            major = [template] * 3
        verify(major, assumptions, floor)
        if opened(template, target) == goal:
            previous_goal = opened(template, source)
            if previous_goal:
                goal = previous_goal
    hypothesis = major * 3
    if not hypothesis:
        if target:
            counter = source and [source]
            recursive_call = [source, target, template]
            result = opened(template, recursive_call, 3) if source else target
            hypothesis = [[counter, target, template], result]
        else:
            goal = opened(*goal, template, 2)
            hypothesis = goal
    floor -= 1
    assumption_image = (major or len(goal) % 2 == major) and floor
    next_goal = opened(goal, [floor])
    next_context = assumptions + [opened(hypothesis, assumption_image)]
    verify(next_goal, next_context, floor)
next_packet = json.load(open(0)).pop
verify(next_packet(), [])
print('ACCEPT')
