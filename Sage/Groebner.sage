import argparse

def create_polynomial_ring(varlist, order='lex', base_ring=QQ):

    if not isinstance(varlist, list):
        raise ValueError("varlist must be a list of strings")

    if not all(isinstance(var, str) for var in varlist):
        raise ValueError("All elements in varlist must be strings")

    if not varlist:
        raise ValueError("varlist cannot be empty")

    var_string = ','.join(varlist)
    print(f"[DEBUG]: {var_string}")

    if order == 'lex':
        R = PolynomialRing(base_ring, var_string, order='lex')
    elif order == 'degrevlex':
        R = PolynomialRing(base_ring, var_string, order='degrevlex')
    elif order == 'deglex':
        R = PolynomialRing(base_ring, var_string, order='deglex')
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
# print("Let's test Isremainder")
# R.<x,y,z> = PolynomialRing(QQ, order='lex')
# f = x^3*y + x^2*y^2 + y^2
# divisors = [x*y - 1, y^2 - 1]
# quotients, remainder = polynomial_division_multivariate(f, divisors, R)

# Example 2
# R.<x,y,z> = PolynomialRing(QQ, order='degrevlex')

# print("Let's test Spoly")
# f1 = x^2*y + x*y^2 + y^2
# g1 = x*y^2 - x
# print(f"f = {f1}")
# print(f"g = {g1}")
# S1 = s_polynomial(f1, g1)
# print(f"S(f,g) = {S1}")

# f1 = x
# g1 = x^2
# print(f"f = {f1}")
# print(f"g = {g1}")
# S1 = s_polynomial(f1, g1)
# print(f"S(f,g) = {S1}")


if __name__ == "__main__":
  parser = argparse.ArgumentParser(description = "Calc Remainder")

  group = parser.add_mutually_exclusive_group()
  group.add_argument('-r', '--remainder', action='store_true',
                    help='work with remainder')
  group.add_argument('-b', '--basis', action='store_true',
                    help='work with groebner basis')

  parser.add_argument('-p', '--polynomial', type = str,
                      help='the polynomial to be remainder')

  parser.add_argument('-v', '--varlist', type = list, help='the remainder varlist')

  args = parser.parse_args()

  if args.remainder:
    ring = create_polynomial_ring(args.varlist)
    quotients, remainder = polynomial_division_multivariate(args.polynomial, args.varlist, ring)
    print(f"[DEBUG] Quotients: {quotients}")
    print(f"[DEBUG] varlist: {varlist}")