src = open(__file__.replace("model_t_chain.py", "model_s_chain.py")).read().split("if __name__")[0]
src = '\n'.join(l for l in src.split('\n') if not l.startswith('report('))
exec(src)
T = {1: 17, 2: 49, 3: 85, 4: 136, 5: 210, 6: 326, 7: 524, 8: 881, 9: 1550, 10: 2841, 11: 5371, 12: 10375}
tDeg = lambda k: T[k] if k in T else (17 if k == 0 else 4 * 2 ** k + 3 * (k + 4) ** 2 + 32)
assert all(tDeg(k) <= tDeg(k + 1) for k in range(0, 40))
pg, gx = chain(tDeg, False, 30)
for k in range(2, 16):
    x = 2 ** k
    print(k, 'poly', pg[k], '128x-1-pg', 128 * x - 1 - pg[k], ' 64x-1-pg', 64 * x - 1 - pg[k],
          ' Tx', gx[k], '128x-(gx+2(k+4)+14)', 128 * x - gx[k] - 2 * (k + 4) - 14,
          ' inv128', 128 * x - pg[k] - 4 * k - 128, ' inv64', 64 * x - pg[k] - 4 * k - 128,
          ' invTx', 128 * x - gx[k] - 4 * k - 128)
# check 3(k+4)^2 <= fixDegQ k + 64
fixDegQ = lambda k: 2 ** (max(k - 1, 0) + 5) + 7
print(all(3 * (k + 4) ** 2 <= fixDegQ(k) + 64 for k in range(0, 60)))
