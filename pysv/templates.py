

class Grammar(object):
    """Grammar may represent any formal grammar.
    """
    commutative_ops = ['+', '*', 'and', 'or']
    def __init__(self, rules = None):
        if rules is None:
            rules = {}
        self.rules = rules
    def add_rule(self, rule):
        assert(type(rule) == GrammarRule)
        self.rules[rule.symb] = rule
    def generate_all_expr_of_depth(self):
        pass
    def all_rule_symbols(self):
        return [self.rules[r].symb for r in self.rules]
    def __iter__(self):
        for key in self.rules:
            yield key
    def __getitem__(self, key):
        return self.rules[key]
    def __str__(self):
        text = ''
        for symb in self.rules:
            text += str(self.rules[symb]) + '\n'
        return text
    def get_used_var_names(self):
        """Returns all names of variables used in productions of this grammar. As a variable are treated all single-string productions bodies not registered as a left-hand symbols in this grammar and different from numbers and boolean constants.

        :return: Dictionary containing variable names (keys) and their types (values).
        """
        # TODO: Currently this function ignores variables in the complicated productions bodies.
        # TODO: Advanced type inference from the function variables are arguments to.
        names = {}
        for rkey in self.rules:
            sort = self.rules[rkey].sort
            for p in self.rules[rkey].productions:
                if len(p.body) == 1 and self.is_var_name(p.body[0]):
                    names[p.body[0]] = sort
        return names
    def is_var_name(self, name):
        return name not in self.all_rule_symbols() and \
               name[0].isalpha() and \
               name not in ['true', 'false']

    @staticmethod
    def get_rule_symbols_in_production(prod, grammar):
        assert isinstance(prod, Production)
        all_rule_symbs = grammar.all_rule_symbols()
        res = []
        for w in prod.body:
            if w in all_rule_symbs:
                res.append(w)
        return res

    @staticmethod
    def get_symbols_usage_in_rule(rule, grammar):
        """Returns a dictionary containing rule symbols (keys) and maximum number of their usages in across all productions of the provided rule (values)."""
        assert (type(rule) == GrammarRule)
        all_rule_symbs = grammar.all_rule_symbols()
        res = {}
        for rsymb in all_rule_symbs:
            max = 0
            for prod in rule.productions:
                x = prod.body.count(rsymb)
                if x > max:
                    max = x
            if max > 0:
                res[rsymb] = max
        return res

    @staticmethod
    def body_text(body):
        return ' '.join(body).replace('( ', '(').replace(' )', ')')



class GrammarRule(object):
    """GrammarRule represents all possible 'products' of a certain symbol. Example of a grammar rule: "symb ::= X | Y | Z".

    Parameters:
    -----------
    :param symb: (str) Main symbol, id of the grammar rule.
    :param sort: (str) Type of the rule symbol.
    :param grammar: (Grammar) Grammar containing this rule symbol.
    :param productions: (list[Production]) A list of productions.
    """
    def __init__(self, symb, sort, grammar, productions = None):
        if productions is None:
            productions = []
        self.symb = symb
        self.sort = sort
        self.grammar = grammar
        self.productions = productions
    def add(self, prod):
        self.productions.append(prod)
    def size(self):
        return len(self.productions)
    def __iter__(self):
        for p in self.productions:
            yield p
    def __getitem__(self, index):
        return self.productions[index]
    def __str__(self):
        text = self.symb + ' ::= ' + str(" ".join(self.productions[0].body))
        for p in self.productions[1:]:
            text += ' | ' + " ".join(p.body)
        return text



class Production(object):
    """Production stores information about a single "symb ::= X" production of the grammar.

    Parameters:
    -----------
    :param symb: A symbol which is being defined.
    :param body: A list of string terms representing right hand of this production rule.
    :param rule: A grammar rule containing this production.
    """
    def __init__(self, symb, body, rule):
        assert type(body) == list, 'Body of a Production must be a list!'
        self.symb = symb
        self.body = body
        self.rule = rule
    def get_body_text(self):
        return ' '.join(self.body)
    def get_rule_symbols(self):
        return Grammar.get_rule_symbols_in_production(self, self.rule.grammar)
    def __str__(self):
        return self.symb + ' ::= ' + self.get_body_text()







class GrammarRuleApplier(object):
    """GrammarRuleApplier is a node in the grammar tree which represents a rule and all productions associated with this rule. It can be treated as a decision point.

    Parameters:
    -----------
    :param rule: (GrammarRule) Grammar rule for which production will be used in this GrammarRuleApplier object.
    :param struct_var_name: (str) Name of the structural variable associated with this node. Value of this variable returned by solver determines, which production from args was chosen.
    :param function_name: (str) Name of the function which will be created later in constraints for this node.
    :param hole_decl: (HoleDecl) Description of the hole's properties.
    :param args: (list[GrammarNode]) List of nodes for concrete productions.
    """
    def __init__(self, rule, struct_var_name, function_name, hole_decl, args = None):
        if args is None:
            args = []
        self.rule = rule
        self.struct_var_name = struct_var_name
        self.function_name = function_name
        self.hole_decl = hole_decl
        self.args = args
    def __getitem__(self, index):
        return self.args[index]

    def add_arg(self, arg):
        self.args.append(arg)

    def max_struct_var_value(self):
        return len(self.args) - 1

    def get_function_invocation(self):
        text = '(' + self.function_name
        for v in sorted(self.hole_decl.vars):
            text += ' ' + v
        text += ') '
        return text




class GrammarNode(object):
    """GrammarLeaf is a node in the grammar tree which has no arguments and its text can be directly obtained.

    Attributes:
    -----------
    body : list[string]
        List of words contained in the body of this node.
    is_leaf : bool
        Tells, if this node is a leaf in the grammar tree.
    vars : dict[string,string]
        Dictionary containing names of all variables present in the node's body and their types.
    args : list[GrammarRuleApplier]
        List of grammar rule appliers determining rule used to generate an argument of this node.
    """
    def __init__(self, prod, parent, parent_arg_no, args):
        self.is_leaf = False
        self.prod = prod
        self.body = prod.body[:]
        self.parent = parent
        self.parent_arg_no = parent_arg_no
        self.vars = {}
        self.rule_symbols = []
        self.args = args

    def add_var(self, name, type):
        self.vars[name] = type

    def add_arg(self, arg):
        self.args.append(arg)

    def get_rich_body(self):
        """Returns a list of body elements with more detailed information about each body symbol."""
        res = []
        level = 0
        ac = 0
        prev_w = None
        for w in self.body:
            is_op = False
            if w == '(':
                level += 1
            elif prev_w == '(':
                is_op = True # In SMTLIB syntax operator is always after '('
            elif w in self.rule_symbols:
                res.append(BodyElement(w, level, is_op, True, self.args[ac]))
                ac += 1
                continue
            res.append(BodyElement(w, level, is_op, False))
            prev_w = w
            if w == ')':
                level -= 1
        return res

    def __getitem__(self, index):
        return self.args[index]


class BodyElement(object):
    def __init__(self, text, level, is_op, is_rule_symb, rule_symb_arg = None):
        self.text = text
        self.level = level
        self.is_op = is_op
        self.is_commutative_op = False
        if self.is_op and self.text in Grammar.commutative_ops:
            self.is_commutative_op = True
        self.is_rule_symb = is_rule_symb
        self.rule_symb_arg = rule_symb_arg

    def __str__(self):
        return self.text



class GrammarLeaf(GrammarNode):
    """GrammarLeaf is a node in the grammar tree which has no arguments and its text can be directly obtained.
    """
    def __init__(self, prod, parent, parent_arg_no):
        GrammarNode.__init__(self, prod, parent, parent_arg_no, [])
        self.is_leaf = True
        self.rule_symbols = prod.get_rule_symbols()

    def get_text(self):
        return Grammar.body_text(self.body)



class GrammarOp(GrammarNode):
    """GrammarOp is a node in the grammar tree which body is dependent on evaluation of some other nodes, which are arguments of this node. Those other nodes are chosen by some rule, so direct argument is rule applier.

    Attributes:
    -----------
    :param prod: (Production) Production, for which op node is created.
    :param args: (list[GrammarRuleApplier]) Arguments of this node - rule appliers for every rule symbol present in the production.
    :param parent: (GrammarRuleApplier) Rule appliers for which this op node is an argument.
    :param parent_arg_no: (int) Rule appliers usually contain several node arguments. parent_arg_no is an index of this node in the parent rule applier.
    """
    def __init__(self, prod, args, parent, parent_arg_no):
        GrammarNode.__init__(self, prod, parent, parent_arg_no, args)
        self.rule_symbols = prod.get_rule_symbols()

    def get_text(self):
        new_body = self.body[:]
        arg_count = 0
        for i in range(0, len(self.body)):
            w = self.body[i]
            if w in self.rule_symbols:
                new_body[i] = self.args[arg_count].get_function_invocation()
                arg_count += 1
        return ' '.join(new_body).replace('( ', '(').replace(' )', ')')

    def get_rule_symbs_positions(self):
        """Returns a list of tuples containing rule symbol and it's index in the body."""
        k = 0
        res = {}
        for i in range(0, len(self.body)):
            w = self.body[i]
            if w == self.rule_symbols[k]:
                res[w] = i
                k += 1
            if k == len(self.rule_symbols):
                break
        return res




class HoleGrammarTree(object):
    """Grammar tree of a grammar of a certain hole. On the basis of this tree generated are constraints for the SMT solver."""

    SUPPORTED_TYPES = ["Int", "Bool", "Real", "String"]

    def __init__(self, hole_decl, max_depth = None):
        if max_depth is None:
            max_depth = hole_decl.max_depth
        self.hole_decl = hole_decl
        self.grammar = hole_decl.grammar
        self.max_depth = max_depth
        self.all_rule_symbols = self.grammar.all_rule_symbols()
        self.vars_dict = {} # dictionary with variables (keys) and their types (values).
        self.struct_vars = []
        self.hole_function_names = []
        self.num_struct_vars = 0
        self.num_functions = 0
        self.hole_vars = hole_decl.get_used_var_names()

        start_rule = self.grammar.rules['Start']
        self.root = self.create_rule_applier_shared_gra(start_rule, 1)
        # self.root = self.create_rule_applier(start_rule, 1)


    def create_rule_applier_shared_gra(self, rule, depth):
        if depth > self.max_depth:
            return None

        gra = self.new_rule_applier(rule)

        # Creating rule appliers for arguments (productions) of this rule applier.
        # It is implemented this way because arguments will often share rule appliers.
        #
        # rsymbs_dict: e.g. {'Start':2, 'StartInt':1}.
        #
        # Numbers tell, how many grammar rule appliers needs to be created.
        #
        # Keys in gras_dict are, e.g. ('Start', 1) or ('Start', 2), and with each of them
        # associated is a GrammarRuleApplier object. It is important to note that productions
        # of a single rule share among each other references to their arguments: rule appliers.
        rsymbs_dict = Grammar.get_symbols_usage_in_rule(rule, self.grammar)
        gras_dict = {}
        for rs in sorted(rsymbs_dict.keys()):
            num = rsymbs_dict[rs]
            for i in range(0,num):
                new_gra = self.create_rule_applier_shared_gra(self.grammar[rs], depth+1)
                gras_dict[(rs,i)] = new_gra

        # Iterate over productions and set created rule appliers as their arguments.
        self.fill_args_of_rule_applier_shared(gra, gras_dict, depth)
        if len(gra.args) > 0:
            return gra
        else:
            return None


    def fill_args_of_rule_applier_shared(self, gra, gras_dict, depth):
        """Iterates over productions of a rule and sets created rule appliers as arguments of those productions."""
        for p in gra.rule:
            a = self.create_node_shared(gra, p, gras_dict, depth)
            if a is not None:
                gra.add_arg(a)


    def create_node_shared(self, gra, prod, gras_dict, depth):
        """Creates concrete node of the grammar tree - either GrammarOp or GrammarLeaf."""
        if depth > self.max_depth:
            return None

        # Find all rule symbols in the production.
        rule_symbs = Grammar.get_rule_symbols_in_production(prod, self.grammar)

        # In the simplest case, in the production's body there are no rule symbols.
        if len(rule_symbs) == 0:
            # In such a case we can return a GrammarLeaf containing body of the production.
            return self.create_leaf(gra, prod)
        elif depth + 1 <= self.max_depth:
            return self.create_node_op(gra, gras_dict, prod, rule_symbs)
        else:
            return None


    def create_leaf(self, gra, prod):
        leaf = GrammarLeaf(prod, gra, len(gra.args))
        self.analyze_body_and_modify_node(leaf, gra)
        return leaf


    def create_node_op(self, gra, gras_dict, prod, rule_symbs):
        """Creates GrammarOp instance.

        :param gra: (GrammarRuleApplier) Rule applier being parent of op node to be created.
        :param gras_dict: (dict[(str,int), GrammarRuleApplier]) Dictionary containing possible arguments of this Op.
        :param prod: (Production) Production for which tree node is created.
        :param rule_symbs: (list[str]) List containing rule symbols in the production in the order they appear in it.
        """
        if len(gras_dict) == 0:
            raise Exception('Trying to create GrammarOp node without any arguments!')

        # We must create GrammarOp with some GrammarRuleApplier arguments.
        op = GrammarOp(prod, [], gra, len(gra.args))
        self.analyze_body_and_modify_node(op, gra)

        rs_usages = {rs: 0 for rs in rule_symbs} # tracks number of read rule symbols.
        for rs in rule_symbs:
            num = rs_usages[rs]
            rs_usages[rs] += 1
            a = gras_dict[(rs, num)]
            if a is not None:
                op.add_arg(a)
            else:
                return None

        # For a node to be correct it must get argument for every rule symbol it contains.
        if len(op.args) == len(rule_symbs):
            return op
        else:
            return None

    # def create_rule_applier(self, rule, depth):
    #     gra = self.new_rule_applier(rule)
    #
    #     # Iterate over productions in grammar rule.
    #     for p in rule:
    #         a = self.create_node(p, depth, gra)
    #         if a is not None:
    #             gra.add_arg(a)
    #     return gra

    # def create_node(self, prod, depth, gra):
    #     if depth > self.depth_limit:
    #         return None
    #
    #     # Find all rule symbols in the production.
    #     rule_symbs = prod.get_rule_symbols()
    #
    #     # In the simplest case, in the production's body there are no rule symbols.
    #     if len(rule_symbs) == 0:
    #         # In such a case we can return a GrammarLeaf containing body of the production.
    #         gf = GrammarLeaf(prod, gra, len(gra.args))
    #         self.analyze_body_and_modify_node(gf, gra)
    #         return gf
    #     elif depth + 1 <= self.depth_limit:
    #         # We must create GrammarOp with some GrammarRuleApplier arguments.
    #         op = GrammarOp(prod, [], gra, len(gra.args))
    #         self.analyze_body_and_modify_node(op, gra)
    #
    #         for rsymb in rule_symbs:
    #             a = self.create_rule_applier(self.grammar[rsymb], depth + 1)
    #             op.add_arg(a)
    #         return op
    #     else:
    #         return None

    def new_rule_applier(self, rule):
        return GrammarRuleApplier(rule, self.next_struct_var(rule), self.next_function_name(rule), self.hole_decl)


    def analyze_body_and_modify_node(self, gn, gra):
        assert isinstance(gn, GrammarNode)
        consts_dict = {t:0 for t in HoleGrammarTree.SUPPORTED_TYPES}
        body = gn.body
        i = 0
        while i < len(body):
            if body[i] == '(' and body[i + 1] == 'Constant':
                ctype = body[i + 2]
                del body[i : i+4] # i+3 is closing parenthesis
                vname = self.next_const_var(self.hole_decl, consts_dict, ctype, gra)
                self.vars_dict[vname] = ctype
                body.insert(i, vname)
                gn.add_var(vname, ctype)
            i += 1


    def next_struct_var(self, rule):
        name = HoleGrammarTree.base_function_name(self.hole_decl) + rule.symb + str(self.num_functions) + '_r' + str(self.num_struct_vars)
        self.num_struct_vars += 1
        self.struct_vars.append(name)
        return name


    def next_const_var(self, hole_decl, consts_dict, vtype, gra):
        if vtype in consts_dict:
            index = consts_dict[vtype]
            consts_dict[vtype] += 1
        else:
            consts_dict[vtype] = 1
            index = 0
        # return hole_decl.id + '-' + vtype + str(index)
        return gra.function_name + '_' + vtype + str(index)


    def cur_function_name(self, rule):
        return HoleGrammarTree.base_function_name(self.hole_decl) + rule.symb + str(self.num_functions-1)


    def next_function_name(self, rule):
        assert type(rule) == GrammarRule
        name = HoleGrammarTree.base_function_name(self.hole_decl) + rule.symb + str(self.num_functions)
        self.num_functions += 1
        self.hole_function_names.append(name)
        return name


    @staticmethod
    def base_function_name(hole_decl):
        return hole_decl.id






def load_gramar_from_SYGUS_spec(spec):
    """Creates Grammar from the given SYGUS grammar specification (http://sygus.seas.upenn.edu/files/SyGuS-IF.pdf, last access 3.08.2016).

    :param spec: SYGUS grammar specification.
    :return: New grammar object.
    """
    grammar = Grammar()

    spec = spec.replace('(', '( ')
    spec = spec.replace(')', ' )')
    words = spec.split()
    brackets_open = 0
    grammar_rule = None
    rule_symb = None
    i = 0

    def get_production_complex_body(start):
        body = []
        opened = 0
        k = start
        while k < len(words):
            if words[k] == '(':
                opened += 1
            elif words[k] == ')':
                opened -= 1

            body.append(words[k])

            if opened == 0:
                return body, k

            k += 1
        return body, k

    while i < len(words):
        w = words[i]
        # print('processing: ' + ' ('+str(brackets_open)+') ' + w )
        if w == '(' and brackets_open < 3:
            brackets_open += 1
            i += 1
            continue
        elif w == ')':
            brackets_open -= 1
            i += 1
            if brackets_open == 1:
                # print('Adding grammar rule: ' + str(grammar_rule))
                grammar.add_rule(grammar_rule)
            continue

        if brackets_open == 2:
            # On the level of 2 opened brackets there are always production names (symb) and their sorts.
            rule_symb = words[i]
            sort = words[i + 1]
            grammar_rule = GrammarRule(rule_symb, sort, grammar)
            i += 2
            continue

        elif brackets_open == 3:
            # On the level of 3 opened brackets there are defined concrete right hands for current product.
            j = i
            while j < len(words):
                if words[j] == '(':
                    body, j = get_production_complex_body(j)
                    grammar_rule.add(Production(rule_symb, body, grammar_rule))
                elif words[j] == ')':
                    i = j
                    brackets_open -= 1
                    break
                else:
                    # Simple symbol not requiring surrounding it with brackets.
                    body = [ words[j] ]
                    grammar_rule.add(Production(rule_symb, body, grammar_rule))

                j += 1
        i += 1

    # print('Final grammar:\n' + str(grammar))

    return grammar