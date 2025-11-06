import argparse

def create_polynomial_ring(varlist, order='lex', base_ring=QQ):
    if not isinstance(varlist, list):
        raise ValueError("varlist must be a list of strings")

    if not all(isinstance(var, str) for var in varlist):
        raise ValueError("All elements in varlist must be strings")

    if not varlist:
        raise ValueError("varlist cannot be empty")

    a = type(varlist)
    print(f"[AAAAA]: {a}")
    print(f"[DEBUG]: {varlist}")

    if order == 'lex':
        R = PolynomialRing(base_ring, varlist, order='lex')
    elif order == 'degrevlex':
        R = PolynomialRing(base_ring, varlist, order='degrevlex')
    elif order == 'deglex':
        R = PolynomialRing(base_ring, varlist, order='deglex')
    else:
        raise ValueError(f"Unsupported order: {order}")

    return R

def polynomial_division_multivariate(f, divisors, ring):

    # Check divisors
    if not divisors:
      raise ValueError("divisors can not be Empty")

    for divisor in divisors:
      if divisor == 0:
        raise ValueError("divisor can not be 0")

    # initialize the ring
    r = ring.zero()
    p = f
    quotients = [ring.zero() for _ in divisors]

    step = 0
    while p != 0:
        step += 1
        # print(f"Step : {step}:")
        # print(f"  p = {p}")

        divided = False
        for i, divisor in enumerate(divisors):
            lt_p = p.lt()  # leading term of p
            lt_divisor = divisor.lt()  # leading term of divisor

            # Check if divisible
            if lt_p != 0 and lt_divisor.divides(lt_p):
                quotient_term = lt_p // lt_divisor

                quotients[i] += quotient_term
                p -= quotient_term * divisor
                divided = True
                break

        if not divided:
            # Move to remainder
            lt_p = p.lt()
            # print(f"    Can't calc, remove {lt_p} to remainder")
            r += lt_p
            p -= lt_p

    # verification
    verification = r + sum(quotients[i] * divisors[i] for i in range(len(divisors)))
    if f == verification:
      return quotients, r
    else:
      raise ValueError("Verification of the result failed")

def s_polynomial(f, g):

    LT_f = f.lt()  # leading term of f
    LT_g = g.lt()  # leading term of g

    LC_f = LT_f.lc()  # leading coefficient of f
    LM_f = LT_f / LC_f  # leading monomial of f

    LC_g = LT_g.lc()  # leading coefficient of g
    LM_g = LT_g / LC_g  # leading monomial of g

    L = lcm(LT_f, LT_g)

    s_poly = (L / LM_f) * f * LC_g  - (L / LM_g) * g * LC_f

    return s_poly

# Example 1
print("Let's test Isremainder")
R.<X_0,X_1,X_2,X_3> = PolynomialRing(QQ, order='lex')
f = (((X_0^2 + X_1^3) + X_2^4) + X_3^5)
divisors = [X_0, X_1, X_2, X_3]
quotients, remainder = polynomial_division_multivariate(f, divisors, R)
print(quotients)
print(remainder)
