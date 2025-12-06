import z3


def get_qvars_from_clause(clause):
    '''
    A helper function that returns the set of unique quantified arguments from
    a list of instantiations (i.e. a set of App objects)
    '''
    res = []

    for app in clause:
        res += app.args

    return set(res)


class Relation():
    '''
    A wrapper class for representing a relation for describing protocol state.

    Class Fields:
        relation: A Z3 function describing the relation this instance represents
        prime: The primed variant of relation (if applicable), for representing post-states
            after transitions
        arg_sorts: A list of Z3 sorts desribing the sorts of the arguments for relation, in order.
        neg: Whether the relation is negated or not
        unique_args: A boolean flag that can be used to indicate that the relation should only take
            unique arguments. This restriction is used for optimizing the search space, as it eliminates
            redundant instantiations like `x == x`
        protocol: A boolean flag that can be used to indicate that the relation describes some "important"
            property of protocol state. This indicator is used for optimizing the search space. Specifically,
            the enumeration requires that every invariant contains at least one protocol relation to eliminate
            uninformative invariants like `Forall w x y z, w == x ==> y == z`
    '''
    def __init__(self, rel, arg_sorts, prime=None, neg=False, unique_args=False, protocol=False, is_eq=False):
        self.relation = rel
        self.prime = prime
        self.arg_sorts = arg_sorts
        self.neg = neg
        self.unique_args = unique_args
        self.protocol = protocol
        self.is_eq = is_eq

    def __eq__(self, other):
        if self.is_eq == other.is_eq:
            return (self.prime == other.prime and
                self.arg_sorts == other.arg_sorts and
                self.neg == other.neg and
                self.unique_args == other.unique_args and
                self.protocol == other.protocol)
        elif self.is_eq != other.is_eq:
            return False
        else:
            return (self.relation == other.relation and
                    self.prime == other.prime and
                    self.arg_sorts == other.arg_sorts and
                    self.neg == other.neg and
                    self.unique_args == other.unique_args and
                    self.protocol == other.protocol) 

    def is_negation(self, other):
        if self.is_eq == other.is_eq:
            return (self.prime == other.prime and
                self.arg_sorts == other.arg_sorts and
                self.neg != other.neg and
                self.unique_args == other.unique_args and
                self.protocol == other.protocol)
        elif self.is_eq != other.is_eq:
            return False
        else:
            return (self.relation == other.relation and
                    self.prime == other.prime and
                    self.arg_sorts == other.arg_sorts and
                    self.neg != other.neg and
                    self.unique_args == other.unique_args and
                    self.protocol == other.protocol) 


    def _validate_args(self, args):
        assert len(args) == len(self.arg_sorts), f"Incorect number of arguments. Expected {len(self.arg_sorts)} but got {len(args)}"
        for i in range(len(args)):
            if args[i].sort() != self.arg_sorts[i]:
                raise AssertionError(f"Incorrect sort of argument at position {i}. \
                                     Expected {self.arg_sorts[i]} but got {args[i].sort()}")

    def negate(self):
        return Relation(self.relation, self.arg_sorts, self.prime, (not self.neg), self.unique_args, self.protocol, self.is_eq)

    def instantiate(self, args, primed=False):
        self._validate_args(args)
        arity_zero = len(self.arg_sorts) == 0
        if primed:
            if self.prime is not None:
                app = self.prime if arity_zero else self.prime(*args)
            else:
                app = self.relation if arity_zero else self.relation(*args)
        else:
            app = self.relation if arity_zero else self.relation(*args)

        return z3.Not(app) if self.neg else app
    
class App():
    '''
    A class for representing a relation applied to some arguments, typically some
    quantified variables.

    Class Fields:
        relation: The relation being applied in this instance
        args: A list of Z3 terms/constants which the relation is being applied to
    '''
    def __init__(self, rel, args):
        self.relation = rel
        self.args = args

    def __eq__(self, other):
        return self.args == other.args and self.relation == other.relation
    
    def is_negation(self, other):
        return self.args == other.args and self.relation.is_negation(other.relation)

    def instantiate(self, primed=False):
        '''
        Return the Z3 term corresponding to the application of this instance's relation
        applied to its arguments.

        Inputs:
            primed: A boolean flag representing whether the primed version of the
                relation should be used or not (for representing post-states)
        '''
        return self.relation.instantiate(self.args, primed)


def eq_rel(sort):
    '''
    A utility function that returns a Relation object representing
    the equality relation over the given sort.

    input:
        sort: A Z3 Sort object
    output:
        A relation object r, where:
            r.relation(x, y) := x == y
            r.arity = 2
            r.arg_sorts = (sort, sort)
    '''
    def e(x, y):
        assert z3.is_eq(x == y), "expression {x} == {y} is not a z3 equality expression"
        return x == y
    
    return Relation(e, (sort, sort), unique_args=True, prime=None, neg=False, protocol=False, is_eq=True)


class Conj():
    '''
    A class for representing a conjunction of terms for invariants. Terms can be
    protocol relations or equality relations.

    Class Fields:
        _terms: A list of App objects representing the terms of the conjunction
        qvars: A python set containing the quantified variables contained in _terms
    '''
    def __init__(self, conj=[]):
        self._terms = conj
        self.qvars = get_qvars_from_clause(self._terms)

    def get_terms(self):
        return self._terms

    def formula(self, primed=False):
        '''
        Returns the Z3 formula represented by this conjunction

        Input:
            primed: A boolean to indicate whether the primed relation
                should be returned or not (for representing post-states)
        '''
        if len(self._terms) == 1:
            return self._terms[0].instantiate(primed)
        if len(self._terms) > 1:
            instantiated = [app.instantiate(primed) for app in self._terms]
            return z3.And(instantiated)
        else:
            return z3.BoolVal(True)


class Disj():
    '''
    A class for representing a disjunction of terms for invariants. Terms can be
    protocol relations or equality relations.

    Class Fields:
        _terms: A list of App objects representing the terms of the disjunction
        qvars: A python set containing the quantified variables contained in _terms
    '''
    def __init__(self, disj=[]):
        self._terms = disj
        self.qvars = get_qvars_from_clause(self._terms)

    def get_terms(self):
        return self._terms

    def formula(self, primed=False):
        '''
        Returns the Z3 formula represented by this disjunction

        Input:
            primed: A boolean to indicate whether the primed relation
                should be returned or not (for representing post-states)
        '''        
        if len(self._terms) == 1:
            return self._terms[0].instantiate(primed)
        if len(self._terms) > 0:
            instantiated = [app.instantiate(primed) for app in self._terms]
            return z3.Or(instantiated)
        else:
            return z3.BoolVal(False)


class Invariant():
    '''
    A class for representing an invariant in a simple grammar. Invariants are in the form:

        Forall x1, x2, ... . LHS(x1, x2, ...) ==> RHS(x1, x2, ...)

    where LHS is a conjunction of terms (protocol relations, equality expressions) and RHS
    can be a conjunction or a disjunction of terms.

    Class Fields:
        _lhs: A Conj object representing the LHS of the invariant
        _rhs: A Conj or Disj object representing the RHS of the invariant
        _qvars: A list of all quantified variables contained in LHS and RHS
            This list is constructed during initialization
    '''
    def __init__(self, lhs=Conj([]), rhs=Disj([])):
        self._lhs = lhs
        self._rhs = rhs

        args = list(self._lhs.qvars | self._rhs.qvars)
        self._qvars = args
    
    def formula(self, primed=False):
        '''
        Returns the Z3 formula represented by this invariant

        Input:
            primed: A boolean to indicate whether the primed relation
                should be returned or not (for representing post-states)
        '''
        if len(self._qvars) == 0:
            if len(self._lhs.get_terms()) == 0:
                return self._rhs.formula(primed)
            return z3.Implies(self._lhs.formula(primed), self._rhs.formula(primed))

        if len(self._lhs.get_terms()) == 0:
            return z3.ForAll(self._qvars, self._rhs.formula(primed))

        return z3.ForAll(self._qvars, z3.Implies(self._lhs.formula(primed), self._rhs.formula(primed)))