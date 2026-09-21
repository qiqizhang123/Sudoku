"""IT5005 Assignment 1: student implementation file.

Implement the functions marked below. Do not modify utils.py or logic_.py.
"""

from utils import *
from logic_ import *


# Do not change this function; it is used to create atomic propositions.
def atom(prefix, r, c, v):
    """prefix is 'Is' or 'Not'. Returns the Expr for e.g. Is3_2_4."""
    return expr(f'{prefix}{r}_{c}_{v}')


def _check_input(n, box_h, box_w, givens):
    if any(type(x) is not int or x < 1 for x in (n, box_h, box_w)):
        raise ValueError('Grid and box dimensions must be positive integers.')
    if box_h * box_w != n or n % box_h or n % box_w:
        raise ValueError('The boxes must tile the board and contain n cells.')
    rows, cols, boxes = set(), set(), set()
    for cell, value in givens.items():
        if not isinstance(cell, tuple) or len(cell) != 2:
            raise ValueError('Use (row, column) tuple keys, numbered from 1.')
        r, c = cell
        if any(type(x) is not int or not 1 <= x <= n for x in (r, c, value)):
            raise ValueError('Rows, columns and values must be integers in 1..n.')
        row, col = (r, value), (c, value)
        box = ((r - 1) // box_h, (c - 1) // box_w, value)
        if row in rows or col in cols or box in boxes:
            raise ValueError('Conflicting givens in a row, column or box.')
        rows.add(row)
        cols.add(col)
        boxes.add(box)


def _peers(n, box_h, box_w, r, c):
    """Distinct cells sharing a row, column or box, in a stable order."""
    return [(rr, cc) for rr in range(1, n + 1) for cc in range(1, n + 1)
            if (rr, cc) != (r, c) and
            (rr == r or cc == c or
             ((rr - 1) // box_h == (r - 1) // box_h and
              (cc - 1) // box_w == (c - 1) // box_w))]


def build_general_kb(n, box_h, box_w, givens):
    """Return a PropKB with all six Sudoku constraints as CNF clauses.

    Only Is atoms are needed here: logical negation is available directly.
    Peer-pair clauses are shared when a pair belongs to both a line and a box.
    """
    _check_input(n, box_h, box_w, givens)
    kb = PropKB()
    values = range(1, n + 1)
    symbols = {(r, c, v): atom('Is', r, c, v)
               for r in values for c in values for v in values}
    for r in values:
        for c in values:
            kb.tell(associate('|', [symbols[r, c, v] for v in values]))
            for v, w in combinations(values, 2):
                kb.tell(~symbols[r, c, v] | ~symbols[r, c, w])
            for rr, cc in _peers(n, box_h, box_w, r, c):
                if (r, c) < (rr, cc):
                    for v in values:
                        kb.tell(~symbols[r, c, v] | ~symbols[rr, cc, v])
    for (r, c), v in sorted(givens.items()):
        kb.tell(symbols[r, c, v])
    return kb


class _IndexedDefiniteKB(PropDefiniteKB):
    """The supplied KB with premise/head indexes; no inference is replaced.

    The library explicitly permits caching clauses_with_premise.  Recording
    atoms processed by that method lets the unchanged library FC routine
    expose its complete closure in one pass, instead of repeating it 729 times.
    Use tell/retract to mutate this KB so indexes and proof caches stay valid.
    """

    def __init__(self):
        super().__init__()
        self.by_premise = {}
        self.by_head = {}
        self.facts = set()
        self.version = 0
        self.fc_seen = set()
        self._bc_state = None

    def tell(self, sentence):
        super().tell(sentence)
        premises, head = parse_definite_clause(sentence)
        if not premises:
            self.facts.add(head)
        else:
            self.by_head.setdefault(head, []).append(tuple(dict.fromkeys(premises)))
            for premise in dict.fromkeys(premises):
                self.by_premise.setdefault(premise, []).append(sentence)
        self.version += 1
        self._bc_state = None
        self.fc_seen.clear()

    def retract(self, sentence):
        remaining = list(self.clauses)
        remaining.remove(sentence)
        self.__init__()
        for clause in remaining:
            self.tell(clause)

    def clauses_with_premise(self, p):
        self.fc_seen.add(p)
        return self.by_premise.get(p, ())


def build_definite_kb(n, box_h, box_w, givens):
    """Return a PropDefiniteKB for elimination and cell last-candidate rules.

    Not is a *positive atom*, not the operator ~.  This Horn theory derives
    sound consequences of Sudoku; it is not logically equivalent to full CNF
    Sudoku and need not solve a puzzle requiring more advanced techniques.
    """
    _check_input(n, box_h, box_w, givens)
    kb = _IndexedDefiniteKB()
    values = range(1, n + 1)
    yes = {(r, c, v): atom('Is', r, c, v)
           for r in values for c in values for v in values}
    no = {(r, c, v): atom('Not', r, c, v)
          for r in values for c in values for v in values}
    for (r, c), v in sorted(givens.items()):
        kb.tell(yes[r, c, v])
    for r in values:
        for c in values:
            peers = _peers(n, box_h, box_w, r, c)
            for v in values:
                for w in values:
                    if w != v:
                        kb.tell(Expr('==>', yes[r, c, v], no[r, c, w]))
                for rr, cc in peers:
                    kb.tell(Expr('==>', yes[r, c, v], no[rr, cc, v]))
                premises = [no[r, c, w] for w in values if w != v]
                if premises:
                    kb.tell(Expr('==>', associate('&', premises), yes[r, c, v]))
                else:  # The only value on a 1 x 1 board is 1.
                    kb.tell(yes[r, c, v])
    return kb

def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    solution = {}

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                if pl_fc_entails(kb, atom('Is', r, c, v)):
                    solution[(r, c)] = v
                    break
            else:
                # A for-else runs when no candidate caused a break.
                raise ValueError(f'No entailed value for cell ({r}, {c})')

    return solution


def pl_bc_entails(kb, query):
    """Your own backward-chaining implementation.

    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    bool
    """
    state = getattr(kb, '_bc_state', None)
    # A's tell/retract invalidates this cache; plain KBs use a clause snapshot.
    marker = (kb.version if isinstance(kb, _IndexedDefiniteKB)
              else tuple(kb.clauses))
    if state is None or state['marker'] != marker:
        facts, by_head = set(), {}
        for clause in kb.clauses:
            premises, head = parse_definite_clause(clause)
            if premises:
                by_head.setdefault(head, []).append(tuple(dict.fromkeys(premises)))
            else:
                facts.add(head)
        state = {'marker': marker, 'known': facts, 'by_head': by_head,
                 'proofs': {p: () for p in facts}}
        kb._bc_state = state

    known = state['known']
    if query in known:
        return True
    active = set()
    failed_this_pass = set()

    def prove(goal):
        if goal in known:
            return True
        if goal in active or goal in failed_this_pass:
            return False
        active.add(goal)
        try:
            for premises in state['by_head'].get(goal, ()):
                count = len(premises)
                for premise in premises:
                    if prove(premise):
                        count -= 1
                    else:
                        break
                if count == 0:
                    known.add(goal)
                    state['proofs'][goal] = premises
                    return True
            failed_this_pass.add(goal)
            return False
        finally:
            active.remove(goal)

    # Failures involving an ancestor are provisional. Retry after new proofs
    # are found; only an unchanged pass establishes a final negative result.
    while True:
        previous_count = len(known)
        failed_this_pass.clear()
        if prove(query):
            return True
        if len(known) == previous_count:
            return False


def solve_full_grid_bc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    solution = {}

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                if pl_bc_entails(kb, atom('Is', r, c, v)):
                    solution[(r, c)] = v
                    break
            else:
                raise ValueError(f'No entailed value for cell ({r}, {c})')

    return solution
