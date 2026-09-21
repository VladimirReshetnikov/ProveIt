Get[FileNameJoin[{DirectoryName[$InputFileName], "HahnRational.wl"}]];
Clear[u,t];
a = HCreate[{u,t}, 1/(1-t) + u];
b = HCreate[{u,t}, 1/(1-t)];
Print["Valuation after cancellation: ", HValuation[HAdd[a,HScale[b,-1]]]];
Print["u compared with t^100: ", HCompare[HCreate[{u,t},u],HCreate[{u,t},t^100]]];
z = HCreate[{u,t},t+I u];
Print["Squared modulus: ", HExpression[HNormSquared[z]]];
Print["Standard part: ", HStandardPart[HCreate[{u,t},(2+3 I+t)/(1-u)]]];
