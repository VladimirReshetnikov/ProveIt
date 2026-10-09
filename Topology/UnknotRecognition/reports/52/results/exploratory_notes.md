# Excluded exploratory measurement

Before the final completed benchmark, an exploratory variant used the 32-block
translation chain with block length 2^128 and eight disjoint ports, with the
classical AHT periodic rule. The combined experiment process hit this session's
200-second execution limit before it wrote a complete benchmark JSON file.
It is not used in the article's tables or the delivered final benchmark JSON.
The final driver explicitly uses the 16-block workload and completed all seven
measured rounds plus warmup.

The printed partial exploratory timings were not retained as a complete paired
measurement and are not presented as final evidence. This does not constitute
a claim that the 32-block input is intractable or that it has a particular
asymptotic runtime. It only records why that case is not in the completed table.
