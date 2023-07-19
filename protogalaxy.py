# Implementation of ProtoGalaxy described https://eprint.iacr.org/2023/1106.pdf by Liam Eagen and Ariel Gabizon
#
# Implementation by Thor Kamphefner
# 2023-07-19

import sage.all
from sage.all import IntegerMod, PolynomialRing, Polynomial

class Prover:
    v_delta: list[IntegerMod] = []
    F: Polynomial = None
    v_beta_star: list[IntegerMod] = []
    F_alpha: IntegerMod = -1
    gamma: IntegerMod = -1
    e_star: IntegerMod = -1
    alpha: IntegerMod = -1

    def __init__(self, witness):
        self.w = witness

class Verifier:
    v_delta: list[IntegerMod] = []
    non_constant_F_coeffs = []
    v_beta_star: list[IntegerMod] = []
    F_alpha: IntegerMod = -1
    gamma: IntegerMod = -1
    e_star: IntegerMod = -1
    alpha: IntegerMod = -1

class Protocol:
    def __init__(self, security_param: int, phi: list[int], e: int, v_phi: list[int], v_w: list[int]):
        # Generate fields/groups
        prime = sage.all.random_prime(
            2**security_param, lbound=2**(security_param - 1))
        Field = sage.all.FiniteField(prime)
        Group = Field  # tmp

        # Generate parameters
        n = 2**security_param
        t = sage.all.log(n, 2)
        # print(t)
        beta: tuple = Field.random_element()
        v_beta = [beta ** (2 ** i) for i in range(t)]

        # Define public parameters
        public_params = {"Field": Field, "Group": Group, "n": n, "t": t,
                         "security_param": security_param, "v_beta": v_beta,
                         "phi": phi, "e": e, "v_phi": v_phi, "v_w": v_w, }

        # Instantiate prover and verifier
        witness = [Field.random_element() for _ in range(n)]
        self.prover = Prover(witness)
        self.verifier = Verifier
        self.pparams = public_params

    def run(self):
        self.r_1_2()
        self.r_3_4()
        # self.r_5_6()
        # self.r_7()
        # self.r_8()
        # self.r_9_10()
        # self.r_11()
        # self.r_12()
        # print(self.prover_output())
        # print(self.verifier_output())

    def r_1_2(self):
        """Verifier sends challenge delta, both parties compute v_delta"""

        # Verifier computes and sends delta
        delta: IntegerMod = self.pparams["Field"].random_element()
        v_delta = [delta ** (2 ** i) for i in range(self.pparams["t"])]

        # both compute v_delta
        self.prover.v_delta = v_delta
        self.verifier.v_delta = v_delta

    def r_3_4(self):
        """P computes the polynomial:
        F(X) = sum_{i=0}^{n-1} pow_i(v_beta + X * v_delta)*f_i(w)
        and sends the non-constant coefficients
        """
        # Prover computes F(X)
        coeffs = [0] * (self.pparams["t"] - 1)
        # F_of_X = sum[]

        # Multivariate polynomial ring
        R = PolynomialRing(self.pparams["Field"], 'X')
        X = R.gens()[0]

        # compute argument to pow_i
        v_beta_plus_x_delta: list[Polynomial] = [R(self.pparams["v_beta"][j]) +
                                                 self.prover.v_delta[j] * X for j in range(self.pparams["t"])]

        # list of monovariate polynomials in the same variable X
        v_pow_eval: list[Polynomial] = [self.pow_i(
            i, v_beta_plus_x_delta[i]) for i in range(self.pparams["n"])]

        # evaluate f
        f_evaluated: list[IntegerMod] = self.pparams["f"](self.prover.w)

        # finally, construct F
        polynomial_F: Polynomial = sum([v_pow_eval[i] * f_evaluated[i]
                                        for i in range(self.pparams["n"])])

        # Prover sends coefficients to verifier
        self.prover.F = polynomial_F
        # verifier doesn't get the zeroeth coefficient, which is e
        self.verifier.non_constant_F_coeffs = polynomial_F.coefficients()[1:]

    def pow_i(self, i: int, v: list[int]) -> sage.all.Polynomial:
        """pow_i(X_1, ..., X_n) = Prod_{l in S} X_l
        Where S is the set of non-zero indices in the binary decomposition of i
        """
        i_bin = bin(i)[2:]  # binary representation of i
        S = [j for j in range(len(i_bin)) if i_bin[j] == "1"]

        # Multivariate polynomial ring
        R = sage.all.PolynomialRing(
            self.pparams["Field"], self.pparams["t"], 'X')
        X = R.gens()  # List of variables X_1, X_2, ...
        polynomial = sage.all.prod(X[j] for j in S)
        return polynomial

    def r_5_6(self):
        """Verifier computes and sends challenge alpha
        all parties compute F(alpha) = e + sum_{i <= t} alpha^i * F_i"""
        alpha = self.pparams["Field"].random_element()
        self.verifier.alpha = alpha
        self.prover.alpha = alpha

        # compute F(alpha)
        prover_F_alpha = self.prover.F(alpha)
        self.prover.F_alpha = prover_F_alpha

        v_coeffs = self.verifier.non_constant_F_coeffs  # shorten the next line
        verifier_F_alpha: IntegerMod = self.pparams["e"] + sum(
            [x * y for x, y in zip(v_coeffs, range(1, self.pparams["n"]))])

        self.verifier.F_alpha = verifier_F_alpha
        # print("prover F_alpha equal to verifier F_alpha? ", prover_F_alpha ==  verifier_F_alpha)

    def r_7(self):
        """all parties compute v_beta_star where 
        beta_star_i = beta_i+alpha*delta^{2^{i-1}}"""
        v_beta_star: list[IntegerMod] = [self.pparams["v_beta"][i] + self.verifier.alpha *
                                         self.pparams["v_delta"][i] for i in range(self.pparams["t"])]
        self.prover.v_beta_star = v_beta_star
        self.verifier.v_beta_star = v_beta_star

    def r_8(self):
        """Prover computes the polynomial:
        G(X) = sum_{i <= n} pow_i(beta_star_i)*f_i(L_0(X)*witness + sum_{j lt k} L_j(X)*witness_j)"""
        pass

    def r_9_10(self):
        """Prover computes the polynomial K(X) such that:
        G(X) = F(alpha)L_0(X) + Z(X)K(X)
        Prover sends the coefficients of K(X) to the verifierc"""
        pass

    def r_11(self):
        """Verifier sends challenge gamma"""
        gamma = self.pparams["Field"].random_element()
        self.verifier.gamma = gamma
        self.prover.gamma = gamma

    def r_12(self):
        """All parties compute e_star = F(alpha)L_0(gamma)+Z(gamma)K(gamma)"""

        self.prover.e_star = -1
        self.verifier.e_star = -1

    def verifier_output(self):
        """Verifier outputs the folded instance (phi_star, v_beta_star, e_star), where:
        phi_star = L_0(gamma)*phi + sum_{i <= k} L_i(gamma)*phi_i"""
        pass

    def prover_output(self):
        """Prover outputs the folded witness
        witness_star = L_0(gamma)*witness + sum_{i <= k} L_i(gamma)*witness_i"""
        pass

# todo: mock some data
# Protocol(...).run()