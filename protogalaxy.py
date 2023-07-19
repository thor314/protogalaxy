# Implementation of ProtoGalaxy described https://eprint.iacr.org/2023/1106.pdf by Liam Eagen and Ariel Gabizon
#
# Implementation by Thor Kamphefner
# 2023-07-19

import sage.all
from sage.all import IntegerMod, PolynomialRing, Polynomial

class Prover:
    v_delta: list[IntegerMod] = []
    v_beta_star: list[IntegerMod] = []
    F_alpha: IntegerMod = -1
    gamma: IntegerMod = -1
    e_star: IntegerMod = -1
    alpha: IntegerMod = -1
    polynomial_F: Polynomial = None
    polynomial_G: Polynomial = None
    polynomial_K: Polynomial = None

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
    polynomial_K_coeffs: list[IntegerMod] = []

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
        beta = Field.random_element()
        v_beta = [beta ** (2 ** i) for i in range(t)]

        # Define public parameters
        self.lagrange_basis, self.vanishing_polynomial = self.gen_lagrange_basis_and_vanishing()
        # self.vanishing_polynomial = self.lagrange_basis[0]*
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
        self.r_5_6()
        self.r_7_8()
        self.r_9_10()
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
        self.prover.polynomial_F = polynomial_F
        # verifier doesn't get the zeroeth coefficient, which is e
        self.verifier.non_constant_F_coeffs = polynomial_F.coefficients()[1:]

    def pow_i(self, i: int, v: list[int]) -> Polynomial:
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
        prover_F_alpha = self.prover.polynomial_F(alpha)
        self.prover.F_alpha = prover_F_alpha

        v_coeffs = self.verifier.non_constant_F_coeffs  # shorten the next line
        verifier_F_alpha: IntegerMod = self.pparams["e"] + sum(
            [x * y for x, y in zip(v_coeffs, range(1, self.pparams["n"]))])

        self.verifier.F_alpha = verifier_F_alpha
        # print("prover F_alpha equal to verifier F_alpha? ", prover_F_alpha ==  verifier_F_alpha)

    def r_7_8(self):
        """all parties compute v_beta_star where 
        beta_star_i = beta_i+alpha*delta^{2^{i-1}}.
        Then Prover computes the polynomial:
        G(X) = sum_{i <= n} pow_i(beta_star_i)*f_i(L_0(X)*witness + sum_{j lt k} L_j(X)*witness_j)"""
        v_beta_star: list[IntegerMod] = [self.pparams["v_beta"][i] + self.verifier.alpha *
                                         self.pparams["v_delta"][i] for i in range(self.pparams["t"])]
        self.prover.v_beta_star = v_beta_star
        self.verifier.v_beta_star = v_beta_star

        R = PolynomialRing(self.pparams["Field"], 'X')
        X = R.gens()[0]
        inner_sum: Polynomial = sum(self.lagrange_basis[j](X) * self.pparams["v_w"][j]
                                    for j in range(self.pparams["k"]))

        f_eval: list[Polynomial] = self.pparams["f"](
            self.lagrange_basis[0](X) * self.prover.w + inner_sum)

        v_pow_beta_star: list[Polynomial] = [self.pow_i(
            i, v_beta_star[i]) for i in range(self.pparams["n"])]

        # product of polynomials
        polynomial_G: Polynomial = sum(
            [v_pow_beta_star[i] * f_eval[i] for i in range(self.pparams["n"])])

        self.prover.polynomial_G = polynomial_G

    def r_9_10(self):
        """Prover computes the polynomial K(X) such that:
        G(X) = F(alpha)L_0(X) + Z(X)K(X)
        Prover sends the coefficients of K(X) to the verifierc"""
        R = PolynomialRing(self.pparams["Field"], 'X')
        X = R.gens()[0]
        polynomial_K: Polynomial = (self.prover.polynomial_G - self.prover.F_alpha *
                                    self.lagrange_basis[0]) / self.vanishing_polynomial(X)

        # Prover sends the coefficients of K(X)
        self.prover.polynomial_K = polynomial_K
        self.verifier.polynomial_K_coeffs = polynomial_K.coefficients()

    def r_11(self):
        """Verifier sends challenge gamma"""
        gamma = self.pparams["Field"].random_element()
        self.verifier.gamma = gamma
        self.prover.gamma = gamma

    def r_12(self):
        """All parties compute e_star = F(alpha)L_0(gamma)+Z(gamma)K(gamma)"""
        alpha = self.prover.alpha
        gamma = self.prover.gamma
        F = self.prover.polynomial_F
        K = self.prover.polynomial_K
        L0 = self.lagrange_basis[0]

        self.prover.e_star = F(alpha) * L0(gamma) + K(gamma) * K(gamma)
        # todo: lazy man's bug, make the verifier do work
        self.verifier.e_star = self.prover.e_star

    def verifier_output(self):
        """Verifier outputs the folded instance (phi_star, v_beta_star, e_star), where:
        phi_star = L_0(gamma)*phi + sum_{i <= k} L_i(gamma)*phi_i"""
        pass

    def prover_output(self):
        """Prover outputs the folded witness
        witness_star = L_0(gamma)*witness + sum_{i <= k} L_i(gamma)*witness_i"""
        pass

    def gen_lagrange_basis_and_vanishing(self) -> tuple[list[Polynomial], Polynomial]:
        """generate lagrange basis"""
        # todo: move generating lagrange basis into setup
        R = PolynomialRing(self.pparams["Field"], 'X')
        X = R.gens()[0]
        points = list(range(self.pparams["n"]))
        lagrange_basis = [0] * self.pparams["n"]
        for i in range(self.pparams["n"]):
            numerator = sage.all.prod(X - j for j in points if j != i)
            denominator = sage.all.prod(i - j for j in points if j != i)
            lagrange_basis[i] = numerator / denominator

        # L[0] vanishes everywhere over points
        vanishing = sage.all.prod(X - j for j in points)

        return (lagrange_basis, vanishing)

# todo: mock some data
# Protocol(...).run()
