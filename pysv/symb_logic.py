from pysv.smt2 import *


def compute_cnf(node):
	"""Transforms expression to the Conjunctive Normal Form (CNF).

	:param node: (NodeSmt2) Tree in the canonical form of expression in SMT-LIB 2.0 language.
	:return: (NodeSmt2) SMT2 tree in the CNF form.
	"""
	n = expand_implications(node)
	n = propagate_negations(n)
	n = move_conjunctions_to_top(n)
	return n


def expand_implications(node):
	"""Every implication in the expression will be transformed to its disjuntive expansion: A => B <=> -A or B

	:param node: (NodeSmt2) Tree in the canonical form of expression in SMT-LIB 2.0 language.
	:return: (NodeSmt2) SMT2 tree with no implication symbol.
	"""
	assert isinstance(node, NodeSmt2)
	if not node.is_logic_conn:
		return node
	elif node.name == '=>':
		return Or(Not(expand_implications(node.args[0])), node.args[1])
	else:
		return node.change_args([expand_implications(a) for a in node.args])


def propagate_negations(node):
	"""Removes, with the usage of De Morgan laws, all negations by propagating them to the level of literals. Implications are expanded whenever necessary.

	:param node: (NodeSmt2) Tree in the canonical form of expression in SMT-LIB 2.0 language.
	:return: (NodeSmt2) SMT2 tree with no negations other than those in literals.
	"""
	assert isinstance(node, NodeSmt2)
	if not node.is_logic_conn:
		return node
	elif node.name == 'not':
		child = node.args[0]
		if child.name == 'not': # double negations
			return propagate_negations(child.args[0])
		elif child.name == 'and': # De Morgan law for conjunction
			return Or(propagate_negations(Not(child.args[0])),
			          propagate_negations(Not(child.args[1])))
		elif child.name == 'or': # De Morgan law for disjunction
			return And(propagate_negations(Not(child.args[0])),
			          propagate_negations(Not(child.args[1])))
		elif child.name == '=>': # expand implication and use De Morgan law
			return propagate_negations(Not(expand_implications(child)))
		else: # negated literals
			return node
	else:
		return node.change_args([propagate_negations(a) for a in node.args])


def move_conjunctions_to_top(node):
	"""Moves conjunctions up in the tree, so no conjunction is below a disjunction. This also means that produced tree is in the CNF form. Example: or(D and(a, not(b)) ===> and(or(D, a), or(D, not(b))).

	:param node: (NodeSmt2) Tree in the canonical form of expression in SMT-LIB 2.0 language. Assumptions: implications were expanded and all negations were propagated.
	:return: (NodeSmt2) SMT2 tree containing conjunctions at the top.
	"""
	assert isinstance(node, NodeSmt2)
	if not node.is_logic_conn:
		return node
	elif node.name == 'or':
		child0 = move_conjunctions_to_top(node.args[0])
		child1 = move_conjunctions_to_top(node.args[1])
		# (a and b) or D ===>
		# (a or D) and (b or D)
		if child0.name == 'and':
			return And(move_conjunctions_to_top(Or(child0.args[0], child1)),
			           move_conjunctions_to_top(Or(child0.args[1], child1)))
		elif child1.name == 'and':
			return And(move_conjunctions_to_top(Or(child0, child1.args[0])),
			           move_conjunctions_to_top(Or(child0, child1.args[1])))
		else:
			return Or(child0, child1)
	elif node.name == 'and':
		# This is simpler case, because we only have to move conjunctions in the children.
		return And(*[move_conjunctions_to_top(a) for a in node.args])
	else:
		return node


def get_clauses_from_cnf_formula(node):
	"""Returns a list containing trees of every clause in the CNF form.

	:param node: (NodeSmt2) Tree in the canonical form of expression in SMT-LIB 2.0 language in the CNF form.
	:return: (list[NodeSmt2]) List of clauses, where each clause is represented by an or-node from the tree.
	"""
	assert isinstance(node, NodeSmt2)
	if node.name == 'or':
		return [node]
	else:
		res = []
		for a in node.args:
			res.extend(get_clauses_from_cnf_formula(a))
		return res


def canonical_form(node):
	"""Transforms tree to the canonical form. SMT-LIB allows for expressions in the from: '(and X Y Z)'. This makes processing harder, so as canonical form assumed was: '(and X (and Y Z))'. Order of arguments does not matter, so '(and (and X Y) Z)' is also in canonical form. All implications, alternatives and conjunctions must have exactly two arguments.

	:param node: (NodeSmt2) Tree of expression in SMT-LIB 2.0 language.
	:return: (NodeSmt2) Tree in the canonical form.
	"""
	assert isinstance(node, NodeSmt2)
	if node.is_terminal or not node.is_logic_conn:
		return node
	elif node.name in LOGIC_OPS and len(node.args) > 2:
		canonical_args = [canonical_form(a) for a in node.args]
		new_args = [canonical_args[0], _canonical_next_node(node.name, canonical_args[1:])]
		return node.change_args(new_args)
	else:
		return node.change_args([canonical_form(a) for a in node.args])


def _canonical_next_node(op, args):
	if len(args) == 2:
		return NodeSmt2(name=op, args=[args[0], args[1]])
	else:
		return NodeSmt2(name=op, args=[args[0], _canonical_next_node(op, args[1:])])