import argparse
import re
import sys
import json
from sage.all import PolynomialRing, QQ


def extract_vars(combined_str):
    """
    Extract variables from input strings to ensure the Ring covers all symbols.
    """
    tokens = re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*', combined_str)
    seen = set()
    ordered_vars = []
    for var in tokens:
        if var not in seen:
            seen.add(var)
            ordered_vars.append(var)
    return ordered_vars

def create_polynomial_ring(vars_list, order='lex', base_ring=QQ):
    if order not in ['lex', 'degrevlex', 'deglex']:
        raise ValueError(f"Unsupported order: {order}")
    R = PolynomialRing(base_ring, vars_list, order=order)
    return R


def solve_radical(poly_str, set_str):
    all_text = poly_str + " " + set_str
    vars_list = extract_vars(all_text)

    if 't' not in vars_list:
        vars_list.append('t')
    else:
        raise ValueError(f"Your vars_list: {vars_list} contains `t`, you need to change the var added")
    if not vars_list:
        raise ValueError("No variables found in input.")

    R = create_polynomial_ring(vars_list, order='lex') 
    t_index = vars_list.index('t')
    t = R.gens()[t_index]

    try:
        f = R(poly_str)
    except TypeError:
        raise ValueError(f"Could not parse polynomial: {poly_str}")

    cleaned_set_str = set_str.strip()

    for char in ['{', '}', '[', ']']:
        cleaned_set_str = cleaned_set_str.replace(char, '')
    
    if not cleaned_set_str.strip():
        gens = []
    else:
        gen_strs = [s.strip() for s in cleaned_set_str.split(',') if s.strip()]
        gens = [R(g) for g in gen_strs]
    
    I1 = R.ideal(gens)
    B_list = gens    
    B_list.append(1 - t*f)
    I2 = R.ideal(B_list)
    
    poly_1 = R(1)

    if (poly_1 in I2):
        try:

            coeffs = I2.lift(poly_1)
            
        except AttributeError:

            I_sing = I2._singular_()
            poly_sing = poly_1._singular_()

            lift_result_matrix = I_sing.lift(poly_sing)
            coeffs = [R(lift_result_matrix[i+1, 1]) for i in range(len(B_list))]

        check_sum = sum(coeffs[i] * B_list[i] for i in range(len(B_list)))

        if check_sum == poly_1:

            max_t_degree = 1

            for coeff in coeffs:
                t_degree = coeff.degree(t) 
                
                if t_degree > max_t_degree:
                    max_t_degree = t_degree

            f_pow_n = f**max_t_degree
            if f_pow_n in I1:
                return max_t_degree
            else:
                raise ValueError(f"The `n` you obtained does not satisfy f in the radical ideal")
        else:
            raise ValueError(f"The Check Sum: {check_sum} is not equal 1")


   
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = "Find n such that f^n in Ideal, and return n.")
    
    parser.add_argument('-p', '--poly', type=str, required=True, help="Polynomial f")
    parser.add_argument('-s', '--set', type=str, required=True, help="Generators of Ideal")

    args = parser.parse_args()

    try:
        result = solve_radical(args.poly, args.set)
        print(result)
        
    except Exception as e:
        sys.stderr.write(f"\n[!!! Radical Error !!!] : {e}\n")
        sys.exit(1)