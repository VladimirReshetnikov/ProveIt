# Local Euler factor readout

Run `OPENBLAS_NUM_THREADS=1 python3 local_readout.py` with NumPy and SciPy. The text file `output.txt` records one run. Computation takes about 20 seconds on one core.

The three input functions are the Riemann zeta function, the odd real character modulo four, and the odd quartic character modulo five with value $i$ at two. The character tables are used to evaluate the functions and generate their zeros independently of the estimator. The estimator takes the resulting zero list, the common conductor bound, the height and a probe prime. Its gamma correction uses even parity for all three functions.

At each critical-line evaluation, the program computes the Dirichlet function as a linear combination of Hurwitz zeta values, using eight Euler--Maclaurin correction terms. It applies the gamma and root-number phase to make the value real and locates sign changes with Brent's method on two different grids. An independent check counts zeros in each of the twelve windows by evaluating the change of argument along horizontal lines at both endpoints. The sample points used on each horizontal line are concentrated near the critical line. Both horizontal discretizations must give the same count as the sign scan.

The kernel uses the normalized four-fold convolution of uniforms on $[-8p,8p]$, convolved with the normalized analytic kernel specified in the paper. The code evaluates the uniform convolution and its derivative as cardinal splines. Gaussian quadrature uses two degrees as a consistency check, with the analytic kernel truncated at $[-7,7]$ for floating-point evaluation. Simpson quadrature evaluates the gamma correction.

All quantities in this experiment use ordinary floating-point arithmetic. The two meshes, argument check and quadrature comparison provide numerical cross-checks. Rigorous enclosure of the zeros and quadratures would require interval arithmetic and validated integral remainders.

The last experiment pools the zeta list with two copies of the quartic list and discards their labels. Four zero-only measurements distinguish the planted product among all 20 products of degrees zero through three formed from the three test functions. The degree is inferred in this search.
