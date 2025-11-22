import z3
from lib import *
import copy
import itertools


def generate_invariants(qvars, sorts, relations, max_depth=2):
    '''
    Generates all invariants of the form

        Forall x, y, ... . LHS(x, y, ...) ==> RHS(x, y, ...)
    
    where LHS is a conjunction of predicates and RHS is a conjunction
    or disjunction of predicates, and LHS and RHS each contain at most
    `max_depth` predicates. The quantified variables are supplied by the
    argument `qvars`. The set of all possible predicates includes
    `relations` and equality relations over the sorts given by `sorts`.

    Inputs:
        qvars: A list of unique Z3 constants representing universally
            quantified variables that can appear in formulas
        sorts: A list of Z3 sorts that appear in relations 
        relations: A list of Relation objects (see lib.py) representing
            the possible relations that can appear as predicates
        max_depth: The maximum number of predicates that can appear in
            a conjunct/disjunct of any invariant
    Output:
        A list of Invariant objects
    '''
    # add equality relation to grammar of predicates
    preds = copy.copy(relations)
    for s in sorts:
        preds.append(eq_rel(s))

    # compute all possible conjuncts/disjuncts of predicates:
    pred_combos = combos_up_to_len(preds, max_depth)

    inv_pairs = []
    for prod in itertools.product(pred_combos, pred_combos):
        if len(prod[1]) > 0:
            inv_pairs.append(prod)

    app = fill_in_qvars(qvars, inv_pairs)

    return app # Placehodler for testing

    
def fill_in_qvars(qvars, inv_pairs):
    '''
    A helper function for `generate_invariants`. This functions computes all
    valid instantiations of the LHS-RHS invariant pairs in `inv_pairs` with
    the universally quantified variables from `qvars`. 
    
    Each entry in the output list is a pair of lists which each contain applications
    of functions from `inv_pairs` to variables in `qvars`.
    '''
    # group variables by sort
    qvars_by_sort = {}
    for v in qvars:
        sort = v.sort()
        if sort not in qvars_by_sort:
            qvars_by_sort[sort] = []
        qvars_by_sort[sort].append(v)

    def get_choices(rel):
        res = []

        choices_by_pos = []
        for sort in rel.arg_sorts:
            if sort in qvars_by_sort:
                choices_by_pos.append(qvars_by_sort[sort])
            else:
                raise AssertionError("Function {rel} expects value of sort {sort}, but no such qvar provided")
            
        for arrangement in itertools.product(*choices_by_pos):
            res.append(list(arrangement))

        return res

    res = []
    for lhs, rhs in inv_pairs:
        lhs_app = [] # if lhs = [r1, r2, ...] Should have the form [[App(r1, a1), App(r2, a2), ...], ...]
        lhs_options = []
        for rel in lhs:
            choices = get_choices(rel)
            instantiated = []
            for args in choices:
                instantiated.append(App(rel, args))
                instantiated.append(App(rel, args, True))
            lhs_options.append(instantiated)
        for combo in itertools.product(*lhs_options):
            lhs_app.append(combo)

        rhs_app = []
        rhs_options = []
        for rel in rhs:
            choices = get_choices(rel)
            instantiated = []
            for args in choices:
                instantiated.append(App(rel, args))
                instantiated.append(App(rel, args, True))
            rhs_options.append(instantiated)
        for combo in itertools.product(*rhs_options):
            rhs_app.append(combo)

        for pair in itertools.product(lhs_app, rhs_app):
            res.append(pair)

    return res
    
    
def combos_up_to_len(relations, max_depth=2):
    '''
    A helper function for `generate_invariants`. This function
    computes all subsequences of the input list `relations` of length
    up to `max_depth` with duplicates allowed.
    '''
    res = [[]]

    for l in range(1, max_depth + 1):
        for combo in itertools.combinations_with_replacement(relations, r=l):
            res.append(combo)

    return res