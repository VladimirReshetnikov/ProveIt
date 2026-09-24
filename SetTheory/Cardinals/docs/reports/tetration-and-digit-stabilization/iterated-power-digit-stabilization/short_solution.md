# A counterexample to the uniform trailing-digit threshold

Let

    a = 3*2^99 + 1 = 1901475900342344102245054808065.

Since 2^99 = 13 (mod 25), a = 15 (mod 25), and therefore v_5(a)=1.
Also v_2(a-1)=99 and v_2(a+1)=1.

For b >= 2, factor

    a^(10^(b+1)) - a^(10^b)
      = a^(10^b) * (a^(9*10^b)-1).

The 5-adic valuation is 10^b, because the second factor is -1 modulo 5.
By the binary lifting-the-exponent identity, the 2-adic valuation is

    v_2(a-1) + v_2(a+1) + v_2(9*10^b) - 1 = b+99.

Thus

    S_a(b) = min(10^b, b+99),
    S_a(2)=100, S_a(3)=102, and D_a(3)=2.

So the proposed universal threshold is false.

In fact, no fixed threshold works for every base. For a=5^K+1, one has
v_2(a)=1 and v_5(a^4-1)=K, hence S_a(b)=min(10^b,b+K).
Setting K=10^m-m+1 gives D_a(m+1)=2 for every m>=2.

The full article proves that 3*2^99+1 is the smallest counterexample, derives
the exact onset for every admissible base, and determines the least
counterexample at each later stage.

Source of the question: Marco Ripà, Mathematics Stack Exchange question
5103929, posted 24 October 2025, retrieved page checked 19 September 2026:
https://math.stackexchange.com/q/5103929
