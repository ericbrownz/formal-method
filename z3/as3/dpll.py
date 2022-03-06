import unittest
from typing import List

from z3 import *


# In this problem, you will implement the DPLL algorithm as discussed
# in the class.


# a utility class to represent the code you should fill in.
class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


########################################
# This bunch of code declare the syntax for the propositional logic, we
# repeat here:
'''
P ::= p
    | T
    | F
    | P /\ P
    | P \/ P
    | P -> P
    | ~P
'''


class Prop:
    def __repr__(self):
        return self.__str__()


class PropVar(Prop):
    def __init__(self, var):
        self.var = var

    def __str__(self):
        return self.var

    def __hash__(self):
        return hash(self.var)

    def __eq__(self, other):
        return other.__class__ == self.__class__ and self.var == other.var


class PropTrue(Prop):
    def __init__(self):
        pass

    def __str__(self):
        return "True"

    def __eq__(self, other):
        return other.__class__ == self.__class__


class PropFalse(Prop):
    def __init__(self):
        pass

    def __str__(self):
        return "False"

    def __eq__(self, other):
        return other.__class__ == self.__class__


class PropAnd(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} /\\ {self.right})"


class PropOr(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} \\/ {self.right})"


class PropImplies(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} -> {self.right})"


class PropNot(Prop):
    def __init__(self, p):
        self.p = p

    def __str__(self):
        return f"~{self.p}"


# we can convert the above defined syntax into Z3's representation, so
# that we can check it's validity easily:
def to_z3(prop):
    if isinstance(prop, PropVar):
        return Bool(prop.var)
    if isinstance(prop, PropImplies):
        return Implies(to_z3(prop.left), to_z3(prop.right))
    if isinstance(prop, PropOr):
        return Or(to_z3(prop.left), to_z3(prop.right))
    if isinstance(prop, PropNot):
        return Not(to_z3(prop.p))
    if isinstance(prop, PropAnd):
        return And(to_z3(prop.left), to_z3(prop.right))


#####################
# TODO: please implement the nnf(), cnf() and dpll() algorithm, as discussed
# in the class.
def nnf(prop: Prop) -> Prop:
    # C(p) = p
    if isinstance(prop, PropVar):
        return prop
    # C(P->Q) = ~C(P) \/ C(Q)
    if isinstance(prop, PropImplies):
        return PropOr(PropNot(nnf(prop.left)), nnf(prop.right))
    # C(P/\Q) = C(P) /\ C(Q)
    if isinstance(prop, PropAnd):
        return PropAnd(nnf(prop.left), nnf(prop.right))
    # C(P\/Q) = C(P) \/ C(Q)
    if isinstance(prop, PropOr):
        return PropOr(nnf(prop.left), nnf(prop.right))

    # ~(P)
    if isinstance(prop, PropNot):
        # is_atom include PropImplies()
        if is_atom(prop.p):
            # eliminate ~~(P)
            if isinstance(prop.p, PropNot):
                return nnf(prop.p.p)
            # ~(P -> Q)
            # nnf(prop.p) nnf # C(P->Q)
            # nnf( PropNot(nnf(prop.p)) ) recursion ~(~C(P) \/ C(Q))
            if isinstance(prop.p, PropImplies):
                return nnf(PropNot(nnf(prop.p)))
            # C(~p) = ~p
            return prop

        # De Morgan law
        else:
            if isinstance(prop.p, PropAnd):
                return PropOr(nnf(PropNot(prop.p.left)), nnf(PropNot(prop.p.right)))
            if isinstance(prop.p, PropOr):
                return PropAnd(nnf(PropNot(prop.p.left)), nnf(PropNot(prop.p.right)))


def is_atom(nnf_prop: Prop) -> bool:
    if isinstance(nnf_prop, PropOr) or isinstance(nnf_prop, PropAnd):  # PropImplies?
        return False
    return True


def cnf(nnf_prop: Prop) -> Prop:
    # is_atom p or ~p after nnf
    if is_atom(nnf_prop):
        if isinstance(nnf_prop, PropVar):
            return nnf_prop
        if isinstance(nnf_prop, PropNot):
            return PropNot(nnf_prop.p)
    else:
        if isinstance(nnf_prop, PropAnd):
            return PropAnd(cnf(nnf_prop.left), cnf(nnf_prop.right))
        # cnf_d
        if isinstance(nnf_prop, PropOr):
            return cnf_d(nnf_prop.left, nnf_prop.right)


# D lec07-17
def cnf_d(left: Prop, right: Prop) -> Prop:
    if isinstance(left, PropAnd):
        return PropAnd(cnf_d(left.left, right), cnf_d(left.right, right))
    if isinstance(right, PropAnd):
        return PropAnd(cnf_d(left, right.left), cnf_d(left, right.right))
    return PropOr(cnf(left), cnf(right))


def flatten(cnf_prop: Prop) -> List[List[Prop]]:
    """Flatten CNF Propositions to nested list structure .

    The CNF Propositions generated by `cnf` method is AST.
    This method can flatten the AST to a nested list of Props.
    For example: "((~p1 \\/ ~p3) /\\ (~p1 \\/ p4))" can be
    transfer to "[[~p1, ~p3], [~p1, p4]]".

    Parameters
    ----------
    cnf_prop : Prop
        CNF Propositions generated by `cnf` method.

    Returns
    -------
    List[List[Prop]
        A nested list of Props, first level lists are connected by `And`,
        and second level lists is connected by `Or`.

    """

    def get_atom_from_disjunction(prop: Prop) -> List[Prop]:
        if is_atom(prop):
            return [prop]

        if isinstance(prop, PropOr):
            return get_atom_from_disjunction(prop.left) + get_atom_from_disjunction(prop.right)

    if isinstance(cnf_prop, PropAnd):
        return flatten(cnf_prop.left) + flatten(cnf_prop.right)
    elif isinstance(cnf_prop, PropOr):
        return [get_atom_from_disjunction(cnf_prop)]
    elif is_atom(cnf_prop):
        return [[cnf_prop]]


def dpll(prop: Prop) -> dict:
    flatten_cnf = flatten(cnf(nnf(prop)))

    # implement the dpll algorithm we've discussed in the lecture
    # you can deal with flattened cnf which generated by `flatten` method for convenience,
    # or, as another choice, you can process the original cnf destructure generated by `cnf` method
    #
    # your implementation should output the result as dict like :
    # {"p1": True, "p2": False, "p3": False, "p4": True} if there is solution;
    # output "unsat" if there is no solution
    #
    # feel free to add new method.

    result = dict()

    for list_prop in flatten_cnf:
        for prop in list_prop:
            if isinstance(prop, PropVar):
                result[prop.var] = False
            if isinstance(prop, PropNot):
                result[prop.p.var] = False

    def select_atomic(P: List[List[Prop]]) -> Prop:
        for list_prop in P:
            for prop in list_prop:
                if isinstance(prop, PropVar):
                    return prop
                if isinstance(prop, PropNot):
                    return prop.p

    def is_sat(P):
        i_count = 0
        j_count = 0
        for i in range(len(P)):  # all P[i] at least one PropTrue
            for j in range(len(P[i])):
                if isinstance(P[i][j], PropTrue):
                    j_count += 1
            if j_count:
                i_count += 1
                j_count = 0

        if i_count == len(P):
            return True
        return False

    def is_unsat(P):
        j_count = 0
        for i in range(len(P)):
            for j in range(len(P[i])):  # P[i] all PropFalse
                if isinstance(P[i][j], PropFalse):
                    j_count += 1
            if j_count == len(P[i]):
                return True
            j_count = 0
        return False

    def check(P: List[List[Prop]]):
        if is_sat(P):  # P is sat
            return PropTrue()
        if is_unsat(P):  # P is unsat
            return PropFalse()
        return P

    def set_x_value(P: List[List[Prop]], x: Prop, setValue: PropTrue or PropFalse):
        for i in range(len(P)):
            for j in range(len(P[i])):
                if isinstance(P[i][j], PropVar):
                    if P[i][j].var == x.var:
                        P[i][j] = setValue
                if isinstance(P[i][j], PropNot):
                    if P[i][j].p.var == x.var:
                        if isinstance(setValue, PropTrue):
                            P[i][j] = PropFalse()
                        if isinstance(setValue, PropFalse):
                            P[i][j] = PropTrue()
        return check(P)

    def dpll_core(P: List[List[Prop]], setValue: Prop) -> Prop:
        if isinstance(P, PropTrue):
            return PropTrue()
        elif isinstance(P, PropFalse):
            return PropFalse()

        x = select_atomic(P)
        if isinstance(setValue, PropTrue):
            result[x.var] = True
        if isinstance(setValue, PropFalse):
            result[x.var] = False

        P_copy = copy.deepcopy(P)
        P = set_x_value(P, x, setValue)

        if isinstance(dpll_core(P, PropTrue()), PropTrue):
            return PropTrue()
        return dpll_core(P_copy, PropFalse())

    dpll_core(flatten_cnf, PropTrue())
    return result

    # result = dict()
    # for list_prop in flatten_cnf:
    #     for prop in list_prop:
    #         if isinstance(prop, PropVar):
    #             result[prop.var] = False
    #         if isinstance(prop, PropNot):
    #             result[prop.p.var] = False
    #
    # def select_atomic(prop: Prop) -> Prop:
    #     if isinstance(prop, PropVar):
    #         return prop
    #     if isinstance(prop, PropAnd) or isinstance(prop, PropOr):
    #         if not isinstance(select_atomic(prop.left), PropTrue) and not isinstance(select_atomic(prop.left),
    #                                                                                  PropFalse):
    #             return select_atomic(prop.left)
    #         if not isinstance(select_atomic(prop.right), PropTrue) and not isinstance(select_atomic(prop.right),
    #                                                                                   PropFalse):
    #             return select_atomic(prop.right)
    #     if isinstance(prop, PropNot):
    #         return select_atomic(prop.p)
    #
    # def set_var_value(prop: Prop, x: Prop, value: PropTrue or PropFalse):
    #     if isinstance(prop, PropVar):
    #         if prop.var == x.var:
    #             return value
    #     if isinstance(prop, PropNot):
    #         prop.p = set_var_value(prop.p, x, value)
    #         if isinstance(prop.p, PropTrue):
    #             return PropFalse()
    #         if isinstance(prop.p, PropFalse):
    #             return PropTrue()
    #     if isinstance(prop, PropOr):
    #         prop.left = set_var_value(prop.left, x, value)
    #         prop.right = set_var_value(prop.right, x, value)
    #         if isinstance(prop.left, PropTrue) or isinstance(prop.right, PropTrue):
    #             return PropTrue()
    #         if isinstance(prop.left, PropFalse):
    #             return prop.right
    #         if isinstance(prop.right, PropFalse):
    #             return prop.left
    #     if isinstance(prop, PropAnd):
    #         prop.left = set_var_value(prop.left, x, value)
    #         prop.right = set_var_value(prop.right, x, value)
    #         if isinstance(prop.left, PropFalse) or isinstance(prop.right, PropFalse):
    #             return PropFalse()
    #         if isinstance(prop.left, PropTrue):
    #             return prop.right
    #         if isinstance(prop.right, PropTrue):
    #             return prop.left
    #     return prop
    #
    # def prop_copy(prop):
    #     if isinstance(prop, PropVar):
    #         return PropVar(prop.var)
    #     if isinstance(prop, PropAnd):
    #         return PropAnd(prop_copy(prop.left), prop_copy(prop.right))
    #     if isinstance(prop, PropOr):
    #         return PropOr(prop_copy(prop.left), prop_copy(prop.right))
    #     if isinstance(prop, PropNot):
    #         return PropNot(prop_copy(prop.p))
    #
    # def dpll_core(prop: Prop, assignment: Prop) -> Prop:
    #     if isinstance(prop, PropTrue):
    #         return prop
    #     elif isinstance(prop, PropFalse):
    #         return prop
    #
    #     p = select_atomic(prop)  # set p value no worry for dpll recursion
    #     # if p is None:
    #     #     return prop
    #     if isinstance(assignment, PropTrue):
    #         result[p.var] = True
    #     elif isinstance(assignment, PropFalse):
    #         result[p.var] = False
    #
    #     prop_copied = prop_copy(prop)
    #     prop = set_var_value(prop, p, assignment)  # make all p in prop, value = assignment
    #
    #     if isinstance(dpll_core(prop, PropTrue()), PropTrue):
    #         return PropTrue()
    #     return dpll_core(prop_copied, PropFalse())
    #
    # newProp = cnf(nnf(prop))
    # dpll_core(newProp, PropTrue())
    # return result


#####################
# test cases:

# p -> (q -> ~p)
# p -> (q -> p) indeed
test_prop_1 = PropImplies(PropVar('p'), PropImplies(PropVar('q'), PropVar('p')))

# ~((p1 \/ ~p2) /\ (p3 \/ ~p4))
test_prop_2 = PropNot(PropAnd(
    PropOr(PropVar("p1"), PropNot(PropVar("p2"))),
    PropOr(PropVar("p3"), PropNot(PropVar("p4")))
))


# ~(p -> (q -> ~p))
# test_prop_3 = PropNot(PropImplies(PropVar('p'), PropImplies(PropVar('q'), PropNot(PropVar('p')))))


# #####################
class TestDpll(unittest.TestCase):

    def test_to_z3_1(self):
        self.assertEqual(str(to_z3(test_prop_1)), "Implies(p, Implies(q, p))")

    def test_to_z3_2(self):
        self.assertEqual(str(to_z3(test_prop_2)), "Not(And(Or(p1, Not(p2)), Or(p3, Not(p4))))")

    def test_nnf_1(self):
        self.assertEqual(str(nnf(test_prop_1)), "(~p \\/ (~q \\/ p))")

    def test_nnf_2(self):
        self.assertEqual(str(nnf(test_prop_2)), "((~p1 /\\ p2) \\/ (~p3 /\\ p4))")

    # def test_nnf_3(self):
    #     self.assertEqual(str(nnf(test_prop_3)), "(p /\\ (q /\\ p))")

    def test_cnf_1(self):
        self.assertEqual(str(cnf(nnf(test_prop_1))), "(~p \\/ (~q \\/ p))")

    def test_cnf_2(self):
        self.assertEqual(str(cnf(nnf(test_prop_2))),
                         "(((~p1 \\/ ~p3) /\\ (~p1 \\/ p4)) /\\ ((p2 \\/ ~p3) /\\ (p2 \\/ p4)))")

    def test_cnf_flatten_1(self):
        self.assertEqual(str(flatten(cnf(nnf(test_prop_1)))), "[[~p, ~q, p]]")

    def test_cnf_flatten_2(self):
        self.assertEqual(str(flatten(cnf(nnf(test_prop_2)))),
                         "[[~p1, ~p3], [~p1, p4], [p2, ~p3], [p2, p4]]")

    def test_dpll_1(self):
        s = Solver()
        res = dpll(test_prop_1)
        s.add(Not(Implies(res["p"], Implies(res["q"], res["p"]))))
        self.assertEqual(str(s.check()), "unsat")

    def test_dpll_2(self):
        s = Solver()
        res = dpll(test_prop_2)
        s.add(Not(Not(And(Or(res["p1"], Not(res["p2"])), Or(res["p3"], Not(res["p4"]))))))
        self.assertEqual(str(s.check()), "unsat")


if __name__ == '__main__':
    unittest.main()
