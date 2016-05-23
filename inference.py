import operator 
import itertools, re
import sys

####################### Quntifier and number fuction ##########################

def every(predicate, sequence):
    for x in sequence:
        if not predicate(x):
            return False
    return True

def some(predicate, sequence):
    for x in sequence:
        px = predicate(x)
        if px: return px
    return False   


def num_or_str(x):
    if isnumber(x): return x
    try:
        return int(x) 
    except ValueError:
        try:
            return float(x) 
        except ValueError:
                return str(x).strip() 

def isnumber(x):
    return hasattr(x, '__int__')

def issequence(x):
    return hasattr(x, '__getitem__')

########################## Knowledge_Base #####################################

class Knowledge_Base:
    def __init__(self, sentence=None):
        abstract

    def tell(self, sentence):
        abstract

    def ask(self, query):
        for result in self.ask_generator(query):
            return result
        return False

    def ask_generator(self, query):
        abstract

    def retract(self, sentence):
        abstract

####################### Expression and Parsing ################################

class Expression:
    def __init__(self, op, *args):
        assert isinstance(op, str) or (isnumber(op) and not args)
        self.op = num_or_str(op)
        self.args = map(expr, args)

    def __call__(self, *args):
        assert is_symbol(self.op) and not self.args
        return Expression(self.op, *args)

    def __repr__(self):
        if not self.args:
            return str(self.op)
        elif is_symbol(self.op):
            return '%s(%s)' % (self.op, ', '.join(map(repr, self.args)))
        elif len(self.args) == 1:
            return self.op + repr(self.args[0])
        else:
            return '(%s)' % (' '+self.op+' ').join(map(repr, self.args))

    def __eq__(self, other):
        return (other is self) or (isinstance(other, Expression)
            and self.op == other.op and self.args == other.args)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.op) ^ hash(tuple(self.args))

    def __rshift__(self, other):
        return Expression('>>', self, other)
    
    def __xor__(self, other):
        return Expression('^',  self, other)

def expr(s):
    if isinstance(s, Expression):
        return s
    if isnumber(s):
        return Expression(s)
    s = s.replace('=>', '>>')
    s = re.sub(r'([a-zA-Z0-9_.]+)', r'Expression("\1")', s)
    return eval(s, {'Expression':Expression})

def is_symbol(s):
    return isinstance(s, str) and s[:1].isalpha()

def is_var_symbol(s):
    return is_symbol(s) and s[0].islower()

def variables(s):
    result = set([])
    def walk(s):
        if is_variable(s):
            result.add(s)
        else:
            for arg in s.args:
                walk(arg)
    walk(s)
    return result

def is_definite_clause(s):
    if is_symbol(s.op):
        return True
    elif s.op == '>>':
        antecedent, consequent = s.args
        return (is_symbol(consequent.op)
                and every(lambda arg: is_symbol(arg.op), conjuncts(antecedent)))
    else:
        return False

def parse_definite_clause(s):
    assert is_definite_clause(s)
    if is_symbol(s.op):
        return [], s
    else:
        antecedent, consequent = s.args
        return conjuncts(antecedent), consequent

def dissociate(op, args):
    result = []
    def collect(subargs):
        for arg in subargs:
            if arg.op == op: collect(arg.args)
            else: result.append(arg)
    collect(args)
    return result

def conjuncts(s):
    return dissociate('^', [s])

######################## Print Unifier ########################################

def print_unifier(x):
    t = type(x)
    if t is dict:
        return print_unifier_dict(x)
    elif t is set:
        return print_unifier_set(x)
    else:
        return repr(x)

def print_unifier_dict(d):
    return '{%s}' % ', '.join('%r: %r' % (k, v)
          for k, v in sorted(d.items(), key=repr))

def print_unifier_set(s):
    return 'set(%r)' % sorted(s, key=repr)

def pp(x):
    print print_unifier(x)

def ppsubst(s):
    ppdict(s)

def ppdict(d):
    print print_unifier_dict(d)

def ppset(s):
    print print_unifier_set(s)

###################### Unification and Standardization ########################

def unify(x, y, s):
    if s is None:
        return None
    elif x == y:
        return s
    elif is_variable(x):
        return unify_var(x, y, s)
    elif is_variable(y):
        return unify_var(y, x, s)
    elif isinstance(x, Expression) and isinstance(y, Expression):
        return unify(x.args, y.args, unify(x.op, y.op, s))
    elif isinstance(x, str) or isinstance(y, str):
        return None
    elif issequence(x) and issequence(y) and len(x) == len(y):
        if not x: return s
        return unify(x[1:], y[1:], unify(x[0], y[0], s))
    else:
        return None

def is_variable(x):
    return isinstance(x, Expression) and not x.args and is_var_symbol(x.op)

def unify_var(var, x, s):
    if var in s:
        return unify(s[var], x, s)
    elif occur_check(var, x, s):
        return None
    else:
        return extend(s, var, x)

def occur_check(var, x, s):
    if var == x:
        return True
    elif is_variable(x) and x in s:
        return occur_check(var, s[x], s)
    elif isinstance(x, Expression):
        return (occur_check(var, x.op, s) or
                occur_check(var, x.args, s))
    elif isinstance(x, (list, tuple)):
        return some(lambda element: occur_check(var, element, s), x)
    else:
        return False

def extend(s, var, val):
    s2 = s.copy()
    s2[var] = val
    return s2

def subst(s, x):
    if isinstance(x, list):
        return [subst(s, xi) for xi in x]
    elif isinstance(x, tuple):
        return tuple([subst(s, xi) for xi in x])
    elif not isinstance(x, Expression):
        return x
    elif is_var_symbol(x.op):
        return s.get(x, x)
    else:
        return Expression(x.op, *[subst(s, arg) for arg in x.args])

def standardize_variables(sentence, dic=None):
    if dic is None: dic = {}
    if not isinstance(sentence, Expression):
        return sentence
    elif is_var_symbol(sentence.op):
        if sentence in dic:
            return dic[sentence]
        else:
            v = Expression('var_%d' % standardize_variables.counter.next())
            dic[sentence] = v
            return v
    else:
        return Expression(sentence.op,
                    *[standardize_variables(a, dic) for a in sentence.args])

standardize_variables.counter = itertools.count()

#################### First_Order Logic Knowledge_Base #########################

class FolKnowledge_Base(Knowledge_Base):
    def __init__(self, initial_clauses=[]):
        self.clauses = []
        for clause in initial_clauses:
            self.tell(clause)

    def tell(self, sentence):
        if is_definite_clause(sentence):
            self.clauses.append(sentence)
        else:
            raise Exception("Not a definite clause: %s" % sentence)

    def ask_generator(self, query):
        return fol_bc_ask(self, query)

    def retract(self, sentence):
        self.clauses.remove(sentence)

    def fetch_rules_for_goal(self, goal):
        return self.clauses

def test_ask(query, Knowledge_Base=None):
    q = expr(query)
    vars = variables(q)
    answers = fol_bc_ask(Knowledge_Base or test_Knowledge_Base, q)

    return sorted([print_unifier(dict((x, v) for x, v in a.items() if x in vars))
                   for a in answers],
                  key=repr)

################## Backward_chaining ##########################################

def fol_bc_ask(Knowledge_Base, query):
    return fol_bc_or(Knowledge_Base, query, {})

def fol_bc_or(Knowledge_Base, goal, theta):
    global duplicate_list
    temp_goal = str(goal)
    temp_goal = ''.join(i for i in temp_goal if not i.isdigit()) # remove number
    
    # print goal
    # duplicate_list.append(goal) 
   
    # print len(duplicate_list) == len(set(duplicate_list)) 
    # print duplicate_list 
    # print ""

    if len(duplicate_list) == len(set(duplicate_list)):  # not duplicate
        for rule in Knowledge_Base.fetch_rules_for_goal(goal):
            lhs, rhs = parse_definite_clause(standardize_variables(rule))

            duplicate_list.append(temp_goal) # List(visited_node)
        
            for theta1 in fol_bc_and(Knowledge_Base, lhs, unify(rhs, goal, theta)):
                yield theta1
            duplicate_list.pop() # remove duplicate elements

def fol_bc_and(Knowledge_Base, goals, theta):
    if theta is None:
        pass
    elif not goals:
        yield theta
    else:
        first, rest = goals[0], goals[1:]
                
        # print first, rest

        for theta1 in fol_bc_or(Knowledge_Base, subst(theta, first), theta):
            for theta2 in fol_bc_and(Knowledge_Base, rest, theta1):
                yield theta2     

######################## main function ########################################

input_file = open(sys.argv[2], 'r')

duplicate_list = [] # check duplicate_list
query_sentence = [] # List of query
query_number = input_file.readline() # number of query
knowledge_Base_sentence = [] # Knowledge_Base List

# print query_number

for i in range(0,int(query_number)):
    line = input_file.readline() # String(read_one_line)

    if line[len(line)-1] == '\n': # remove \n
        line = line[:len(line)-1]

    line = line.replace("~","NOTTT") # Change String

    query_sentence.append(line) # List(String_one_line)
   
# print query_sentence # print List

knowledge_Base_number = input_file.readline()

# print knowledge_Base_number

for i in range(0,int(knowledge_Base_number)):
    line = input_file.readline()


    if line[len(line)-1] == '\n':
        line = line[:len(line)-1]

    line = line.replace("~","NOTTT")

    # print line
    list1 = list(line) # String -> List
    # print list1

    for i in range(0,len(list1)):
        if list1[i] == '=':
            list1.insert(0,'(')
            break
        
    for i in range(0,len(list1)):
        if list1[i] == '=':
            list1.insert(i-2,')')
            break
       
    line1 = "".join(list1) # List -> String
    # print line1
    
    knowledge_Base_sentence.append(line1) # KB_List(append String)
 
# print knowledge_Base_sentence # Knowledge_Base list(Map)
# print ""

test_Knowledge_Base = FolKnowledge_Base(
    map(expr, knowledge_Base_sentence)
)


output_file = open('output.txt', 'w')   

# list2 = test_ask('G(Toma)') # [{}] or []

# print list2
# print query_sentence

for i in range(0,len(query_sentence)):
    # print query_sentence[i]
    list2 = test_ask(query_sentence[i]) # [{}] or []
    # print "unification : %s" % list2

    if not list2: # list2 is empty
        # print "list(%d): FALSE(empty)" % i
        # print ""
        # print ""
        output_file.write('FALSE')
        output_file.write('\n')
    else: # list2 is not empty
        # print "list(%d): TRUE(not empty)" % i
        # print ""
        # print ""
        output_file.write('TRUE')
        output_file.write('\n')

output_file.close()
input_file.close()

