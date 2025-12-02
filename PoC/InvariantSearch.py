import z3
from lib import *
import copy
import itertools
from tqdm import tqdm

def invariant_search(axioms, init, tr, cand_set, cex):
    '''
    Performs invariant search over a provided set of candidate invariants to
    find a set of inductive invariants that eliminates the given counterexample.
    The inductiveness check is performed against provided initialization and
    transition constraints, as well as any additional axioms.

    Input:
        axioms: A list of Z3 constraints representing the axioms for the 
            system specification
        init: A list of Z3 constraints representing the initial conditions
            for the system specification
        tr: A list of Z3 constraints representing the transition relations
            for the system specification
        cand_set: A list of Invariant objects to be searched over
        cex: A list of Z3 constraints describing the counterexample to
            eliminate
    Output:
        A list of Invariant objects representing a conjunction of relatively
        inductive invariants from `cand_set` that eliminate `cex`, if such
        a conjunction exists. Returns None otherwise.
    '''
    pass

def generate_invariants(qvars, sorts, relations, max_depth=2, max_depth_rhs=None):
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
        max_depth_rhs: Optional argument for defining different max depths
            for the lhs and rhs of invariants. If this parameter is included,
            then max_depth will be the max_depth of the LHS.
    Output:
        A list of Invariant objects
    '''
    rhs_depth = max_depth_rhs if max_depth_rhs is not None else max_depth
    pred_combos_lhs = combos_up_to_len(relations, max_depth)
    pred_combos_rhs = combos_up_to_len(relations, rhs_depth)

    inv_pairs = []
    for prod in itertools.product(pred_combos_lhs, pred_combos_rhs):
        if (contains_protocol_relation(prod[0]) or contains_protocol_relation(prod[1])) and len(prod[1]) > 0:
            inv_pairs.append(prod)

    app = fill_in_qvars(qvars, inv_pairs)

    res = []

    for lhs, rhs in app:
        res.append(Invariant(Conj(lhs), Disj(rhs)))
        if len(rhs) > 1:
            res.append(Invariant(Conj(lhs), Conj(rhs)))

    return res

    
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

    res = []
    for lhs, rhs in tqdm(inv_pairs):
        # There can be some redundancy depending on how many qvars are provided and
        # how many unique arguments a relation can have. For example, if quantified variables
        # x, y are given, but the relation is unary, 
        # forall x, unary_rel x         and          forall y, unary_rel y
        # are equivalent. The following reduces redundant cases:
        sort_count_lhs = {}
        for rel in lhs:
            for sort in rel.arg_sorts:
                sort_count_lhs[sort] = sort_count_lhs.get(sort, 0) + 1
        sort_count_rhs = {}
        for rel in rhs:
            for sort in rel.arg_sorts:
                sort_count_rhs[sort] = sort_count_rhs.get(sort, 0) + 1

        reduced_qvars_by_sort = {}
        for sort in qvars_by_sort.keys():
            max_needed = max(sort_count_lhs.get(sort, 0), sort_count_rhs.get(sort, 0))
            sort_len = min(max_needed, len(qvars_by_sort[sort]))
            reduced_qvars_by_sort[sort] = qvars_by_sort[sort][:sort_len]

        # if lhs = [r1, r2, ...] Should have the form [[App(r1, a1), App(r2, a2), ...], ...]
        lhs_app = get_clause_instantiations(reduced_qvars_by_sort, lhs) 
        rhs_app = get_clause_instantiations(reduced_qvars_by_sort, rhs)

        for pair in itertools.product(lhs_app, rhs_app):
            res.append(pair)

    return res
    

def get_clause_instantiations(qvars_by_sort, clause):
    '''
    Helper function for fill_in_qvars. Given a list representing
    a clause consisting of a cojunction/disjunction of relations and a
    set of quantified variables organized by sort, returns all possible
    instantiations of `clause`.

    To reduce the search space, this function will guarantee that for any
    instantiation, each varaible's first appearance across all relations
    in `clause` is increasing order of their index,based on the arbitrary 
    ordering given by the list(s) in `qvars_by_sort`

    `qvars_by_sort` should be a dictionary where the entry
    `qvars_by_sort`[sort] is a list containing the quantified variables
    of sort.
    '''

    # Make sure arrangement is possible
    for rel in clause:
        for sort in rel.arg_sorts:
            if sort not in qvars_by_sort:
                raise AssertionError("Function {rel} expects value of sort {sort}, but no such qvar provided")


    res = []

    def backtrack(rel_id, pos_in_rel, cur_clause, cur_rel_instance, max_ind):
        if rel_id == len(clause):
            res.append(copy.copy(cur_clause))
            return

        cur_rel = clause[rel_id]
        if pos_in_rel == len(cur_rel.arg_sorts):
            cur_clause.append(App(cur_rel, copy.copy(cur_rel_instance)))
            backtrack(rel_id + 1, 0, cur_clause, [], max_ind)
            cur_clause.pop()
            return
        
        cur_sort = cur_rel.arg_sorts[pos_in_rel]
        max_ind_for_sort = max_ind.get(cur_sort, -1)

        used = set()
        for app in cur_clause:
            used.update(app.args)
        used.update(cur_rel_instance)

        for i in range(len(qvars_by_sort[cur_sort])):
            qvar = qvars_by_sort[cur_sort][i]
            if i > max_ind_for_sort or (not cur_rel.unique_args and qvar in used):
                new_max = max(i, max_ind_for_sort)

                max_ind[cur_sort] = new_max
                cur_rel_instance.append(qvar)
                backtrack(rel_id, pos_in_rel+1, cur_clause, cur_rel_instance, max_ind)
                cur_rel_instance.pop()
                max_ind[cur_sort] = max_ind_for_sort

    backtrack(0, 0, [], [], {})
    return res

    
def combos_up_to_len(relations, max_depth=2):
    '''
    A helper function for `generate_invariants`. This function
    computes all subsequences of the input list `relations` of length
    up to `max_depth` with duplicates allowed.

    Note that to reduce the invariant search space, this function does
    not enumerate symmetric invariant combinations by ensuring that
    relations only appear in non-decreasing order, where the order
    is the arbitrary ordering given by `relations`.
    '''
    res = []

    def backtrack(pos, cur):
        if pos <= max_depth:
            res.append(copy.copy(cur))
        if pos > max_depth:
            return
        
        for rel in relations[pos:]:
            cur.append(rel)
            backtrack(pos + 1, cur)
            cur.pop()
            cur.append(rel.negate())
            backtrack(pos + 1, cur)
            cur.pop()
    
    backtrack(0, [])
    return res

def contains_protocol_relation(relations):
    '''
    A helper function that checks if `relations` contains at least one relation
    that are marked as protocol relations (i.e. they descibe some "interesting"
    property of the protocol, such as the network state or host state(s))
    '''
    for rel in relations:
        if rel.protocol:
            return True
        
    return False