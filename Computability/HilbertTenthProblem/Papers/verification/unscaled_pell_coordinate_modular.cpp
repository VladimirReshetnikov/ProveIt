// Exact prime-power Horner evaluation of the canonical Pell/binomial Y.
// No huge binomial coefficient, U, or Y is materialized.
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>

using Integer = std::int64_t;

Integer power_mod(Integer base, Integer exponent, Integer modulus) {
    Integer result = 1;
    while (exponent != 0) {
        if ((exponent & 1) != 0) result = result * base % modulus;
        base = base * base % modulus;
        exponent >>= 1;
    }
    return result;
}

Integer inverse_mod(Integer value, Integer modulus) {
    Integer a = modulus, b = value, t = 0, s = 1;
    while (b != 0) {
        const Integer quotient = a / b;
        const Integer remainder = a - quotient * b;
        a = b;
        b = remainder;
        const Integer next = t - quotient * s;
        t = s;
        s = next;
    }
    if (a != 1) throw std::runtime_error("nonunit modular denominator");
    t %= modulus;
    return t < 0 ? t + modulus : t;
}

Integer canonical_y_mod(Integer r, Integer prime, Integer exponent) {
    if (r < 1 || r > 100000000 || (prime != 2 && prime != 7) || exponent < 1)
        throw std::runtime_error("unsupported input");
    Integer modulus = 1;
    for (Integer i = 0; i < exponent; ++i) {
        if (modulus > 2000000000 / prime)
            throw std::runtime_error("modulus exceeds verified integer bound");
        modulus *= prime;
    }
    // Every modular product is below 4*10^18; unit*numerator is below
    // 4*10^17. Both bounds are strictly below signed64's maximum.
    const Integer U = power_mod(3, 2 * r + 1, modulus);
    Integer unit = 1, valuation = 0, result = 1;
    for (Integer k = 1; k <= r; ++k) {
        Integer numerator = 2 * r - k + 1, denominator = k;
        while (numerator % prime == 0) { numerator /= prime; ++valuation; }
        while (denominator % prime == 0) { denominator /= prime; --valuation; }
        if (valuation < 0) throw std::runtime_error("negative binomial valuation");
        unit = unit * numerator % modulus * inverse_mod(denominator % modulus, modulus) % modulus;
        const Integer coefficient = valuation >= exponent ? 0 :
            unit * power_mod(prime, valuation, modulus) % modulus;
        result = (result * U + coefficient) % modulus;
    }
    return result;
}

void emit(Integer r, Integer prime, Integer exponent) {
    std::cout << r << ' ' << prime << ' ' << exponent << ' '
              << canonical_y_mod(r, prime, exponent) << '\n';
}

int main(int argc, char** argv) {
    try {
        if (argc == 2 && std::string(argv[1]) == "--batch") {
            Integer r, prime, exponent;
            while (std::cin >> r >> prime >> exponent) emit(r, prime, exponent);
            if (!std::cin.eof()) throw std::runtime_error("malformed batch input");
        } else if (argc == 4) {
            emit(std::stoll(argv[1]), std::stoll(argv[2]), std::stoll(argv[3]));
        } else {
            throw std::runtime_error("usage: helper r prime exponent, or helper --batch");
        }
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return EXIT_FAILURE;
    }
}
