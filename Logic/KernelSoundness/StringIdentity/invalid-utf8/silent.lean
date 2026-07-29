-- A theorem about a string literal that got corrupted in transit ...
theorem claim : "aí €b".length = 3 := rfl
-- ... is literally the same theorem as this one:
theorem claim2 : "aï¿½b".length = 3 := rfl
-- and the two literals are definitionally equal:
example : ("aí €b" = "aï¿½b") := rfl
