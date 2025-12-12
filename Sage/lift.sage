import argparse
import re
import sys
import json
from sage.all import PolynomialRing, QQ

def main():
    R = PolynomialRing(QQ, names='x,y,z,t', order='lex')
    x, y, z, t = R.gens()

    poly = y - x**2 + 1
    poly_1 = R(1)  
    
    B_list = [t*poly - 1, x*y**2 + 2*y**2, x**4 - 2*x**2 + 1]
    
    I = R.ideal(B_list)

    is_contained = (1 in I)

    print(f"1 是否属于理想 B: {is_contained}")

    if is_contained:
        try:

            coeffs = I.lift(poly_1)
            
        except AttributeError:

            I_sing = I._singular_()
            poly_sing = poly_1._singular_()

            lift_result_matrix = I_sing.lift(poly_sing)
            coeffs = [R(lift_result_matrix[i+1, 1]) for i in range(len(B_list))]

        for i, coeff in enumerate(coeffs):
            print(f"  B[{i}] corff: {coeff}")
        check_sum = sum(coeffs[i] * B_list[i] for i in range(len(B_list)))


    else:
        print("1 is not in ideal")

if __name__ == "__main__":
    main()