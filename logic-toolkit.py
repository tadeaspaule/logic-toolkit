from random import randrange

class LogicToolkit:
    '''
    Holds functionality for working with logic formulas:
    - Convert formula to CNF or DNF form
    - Check if a formula is a tautology / contradiction / satisfiable
    - Get True interpretations
    - Get definite rules from formula
    - Make queries
    - Generate random logical formulas
    '''

    # !Q   - negation
    # QvP  - disjunction
    # QaP  - conjunction
    # Q->P - implication

    # f_list is used in the code below often. It refers to the logic formula in its list form

    def __init__(self):
        self._definite_rules = {}
        self._known_literals = set()
        self._debugging = False

        # definite rules are stored in a dictionary form, to make queries easy
        # for example, T->S is stored as definite_rules[S] = T
        # for example, ->T is stored as definite_rules[T] = True, meaning success
        # if you meet a dead end, the default .get is False, so if there is no T, returns False, meaning failure

    def __log_debugging_msg(self,message):
        '''
        If self._debugging is True, prints a given message
        '''
        if self._debugging:
            padded_print(message)
   
    def __negate(self,lit_or_form):
        '''
        Negates a given literal or formula
        For example, QvR becomes !(QvR)
        For example, Q becomes !Q
        For example, !Q becomes Q
        '''
        
        if type(lit_or_form) == list and len(lit_or_form) == 2 and lit_or_form[0] == '!':
            # was given a negated literal / formula, returning only the literal / formula
            return lit_or_form[1]
        
        return ['!',lit_or_form] # otherwise, return the negated literal/formula
    
    def __is_disjunction(self,f_list):
        '''
        Checks whether a given f_list is a disjunction
        Returns False if given a literal
        QvT is a disjunction
        (QaV)v(TaX) is a disjunction
        (QvT)a(TvP) is not a disjunction
        '''
        if type(f_list) != list or len(f_list) == 2:
            # if it was given a literal, return False
            # the len == 2 checks whether a negated literal was given
            return False
        
        # goes through the given f_list
        # if it finds anything other than 'v', stuff in brackets, or literals, return False
        for c in f_list:
            if not (c == 'v' or type(c) == list or type(c) == bool or c.isupper()):
                return False

        return True
    
    def __is_conjunction(self,f_list):
        '''
        Checks whether a given f_list is a conjunction
        Returns False if given a literal
        QaT is a conjunction
        (QvV)a(TvX) is a conjunction
        (QaT)v(TaP) is not a conjunction
        '''
        if type(f_list) != list or len(f_list) == 2:
            # if it was given a literal, return False
            # the len == 2 checks whether a negated literal was given
            return False
        
        # goes through the given f_list
        # if it finds anything other than 'a', stuff in brackets, or literals, return False
        for c in f_list:
            if not (c == 'a' or type(c) == list or type(c) == bool or c.isupper()):
                return False

        return True
    
    def __remove_implications(self,f_list):
        '''
        Removes implications from a given list representation of a formula
        Applies the equivalence Q->T == !QvT
        Returns the resulting f_list
        '''

        # goes as deep as possible to handle nested brackets
        for i,f in enumerate(f_list):
            if type(f) == list:
                f_list[i] = self.__remove_implications(f_list[i])

        # applies the Q->T == !QvT equivalence
        for i, f in enumerate(f_list):
            if f == '->' and i > 0:
                f_list[i-1] = self.__negate(f_list[i-1])
                f_list[i] = 'v'
        
        return f_list
    
    def __move_negations_inwards(self,f_list):
        '''
        Moves negations inwards in a given f_list
        Applies the equivalences !(QvT) == !Qa!T and !(QaT) == !Qv!T
        Returns the resulting f_list
        '''

        # goes as deep as possible to handle nested brackets
        for i,f in enumerate(f_list):
            if type(f) == list:
                f_list[i] = self.__move_negations_inwards(f_list[i])
        
        changed = True
        while changed:
            # this loop runs until it checks the whole list and doesn't find anything to change
            changed = False
            for i,f in enumerate(f_list):
                if f == '!' and type(f_list[i+1]) == list:
                    while type(f_list[i+1]) == list and len(f_list[i+1]) == 1:
                        # removes redundant brackets, for example !(((QvT)))
                        f_list[i+1] = f_list[i+1][0]
                    
                    next_symbol = f_list[i+1]
                    if len(next_symbol) == 2: # negation of a negation
                        # removes the negation  CONTINUE HERE
                        f_list[i+1] = f_list[i+1][1]
                        f_list = f_list[:i] + f_list[i+1]
                        changed = True
                        break
                    elif len(next_symbol) > 2:
                        if self.__is_conjunction(next_symbol):
                            # situation is !(AaB), return should be !Av!B
                            temp = [] # here we will put the new version (!Av!B in the example)
                            for part in next_symbol:
                                if part != 'a':
                                    temp.append(self.__negate(part)) # negate the individual literals
                                    temp.append('v') # make it a disjunction
                            temp = temp[:-1] # removes the last 'v'
                            f_list[i] = temp # changes the current slot to hold the new disjunction
                            f_list = f_list[:i+1] + f_list[i+2:] # removes the slot which held the conjunction
                            changed = True
                            break
                        elif self.__is_disjunction(next_symbol):
                            # situation is !(AvB), return should be !Aa!B
                            # functions basically the same as above, only 'a' and 'v' are switched
                            temp = []
                            for part in next_symbol:
                                if part != 'v':
                                    temp.append(self.__negate(part))
                                    temp.append('a')
                            temp = temp[:-1]
                            f_list[i] = temp
                            f_list = f_list[:i+1] + f_list[i+2:]
                            changed = True
                            break
        
        
        return f_list
    
    def __remove_redundant_brackets(self,f_list):
        '''
        Removes redundant brackets, for example ((QvT)) becomes QvT
        Returns the resulting f_list
        '''

        while type(f_list) == list and len(f_list) == 1 and type(f_list[0]) == list:
            # while the given f_list has only one element, which is another list,
            # get rid of the outermost brackets
            # for example, [[1,2]] becomes [1,2]
            f_list = f_list[0]
        
        for i,f in enumerate(f_list):
            if type(f_list[i]) == list:
                while len(f_list[i]) == 1 and type(f_list[i][0]) == list:
                    # same thing as the above commented section
                    f_list[i] = f_list[i][0]
    
                if len(f_list[i]) > 2:
                    # checks nested lists (formulas in brackets) as well
                    f_list[i] = self.__remove_redundant_brackets(f)
        
        return f_list
          
    def __join_conjunctions(self,f_list):
        '''
        Checks for instances like Qa(TaV) or (QaT)aV
        Gets rid of the brackets, so it becomes QaTaV
        Returns the resulting f_list
        '''

        for i,f in enumerate(f_list):
            if type(f) == list and len(f) > 2:
                # does this for all nested lists (formulas in brackets)
                f_list[i] = self.__join_conjunctions(f)
        
        
        changed = True
        while changed:
            # goes through the whole list, trying to find situations like Qa(TaV) or (QaT)aV
            # if it finds one, adjusts the f_list, and starts from the start
            # if it reaches the end without finding anything, that's the end
            # the while loop is necessary so that we don't encounter IndexErrors
            changed = False
            for i,f in enumerate(f_list):
                if f == 'a':
                    if self.__is_conjunction(f_list[i-1]):
                        # situation in the form of (QaT)aV
                        # nested list on the left which is a conjunction
                        f_list[i-1].extend(['a',f_list[i+1]])
                        f_list = f_list[:i] + f_list[i+2:]
                        changed = True
                        break
                    elif self.__is_conjunction(f_list[i+1]):
                        # situation in the form of Qa(TaV)
                        # nested list on the right which is a conjunction
                        f_list[i+1].extend(['a',f_list[i-1]])
                        f_list = f_list[:i-1] + f_list[i+1:]
                        changed = True
                        break
                
        
        return f_list
      
    def __join_disjunctions(self,f_list):
        '''
        Checks for instances like Qv(TvV) or (QvT)vV
        Gets rid of the brackets, so it becomes QvTvV
        Returns the resulting f_list
        '''

        for i,f in enumerate(f_list):
            if type(f) == list and len(f) > 2:
                # does this for all nested lists (formulas in brackets)
                f_list[i] = self.__join_disjunctions(f)
        
        
        changed = True
        while changed:
            # goes through the whole list, trying to find situations like Qv(TvV) or (QvT)vV
            # if it finds one, adjusts the f_list, and starts from the start
            # if it reaches the end without finding anything, that's the end
            # the while loop is necessary so that we don't encounter IndexErrors
            changed = False
            for i,f in enumerate(f_list):
                if f == 'v':
                    
                    if self.__is_disjunction(f_list[i-1]):
                        # situation in the form of (QvT)vV
                        # nested list on the left which is a disjunction
                        f_list[i-1].extend(['v',f_list[i+1]])
                        f_list = f_list[:i] + f_list[i+2:]
                        changed = True
                        break
                    elif self.__is_disjunction(f_list[i+1]):
                        # situation in the form of Qv(TvV)
                        # nested list on the right which is a disjunction
                        f_list[i+1].extend(['v',f_list[i-1]])
                        f_list = f_list[:i-1] + f_list[i+1:]
                        changed = True
                        break
                
        
        return f_list
    
    def __move_disjunctions_inwards(self,f_list):
        '''
        Moves disjunctions inwards to make the formula into its CNF form
        Applies the equivalences Av(BaC) == (AvB)a(AvC) and (AaB)vC == (AvC)a(BvC)
        Returns the resulting f_list
        '''
        
        for i,f in enumerate(f_list):
            if type(f) == list and len(f) > 2:
                # does this for all nested lists (formulas in brackets)
                f_list[i] = self.__move_disjunctions_inwards(f_list[i])
        
        changed = True
        while changed:
            # goes through the whole list, trying to find situations like Av(BaC) or (AaB)vC
            # if it finds one, adjusts the f_list, and starts from the start
            # if it reaches the end without finding anything, that's the end
            # the while loop is necessary so that we don't encounter IndexErrors
            changed = False
            for i,part in enumerate(f_list):
                if part == 'v':
                    if self.__is_conjunction(f_list[i-1]):
                        # situation like (AaB)vC, moving C into brackets on the left
                        onright = f_list[i+1] # the C in the example
                        old_left = f_list[i-1] # a copy of the conjunction on the left
                        temp = [[onright,'v',piece] for piece in old_left if piece != 'a']
                        # temp: makes a C or x disjunction for every x in the conjunction
                        #       in the example with A,B,C there are only 2 elements in the conjunction
                        #       but there may be more, and the rule still holds
                        #       for example, (AaBaC)vD == (AvD)a(BvD)a(CvD)
                        #       that's what's happening here
                        f_list[i-1] = [] # wipes the place where the conjunction used to be
                        for piece in temp:
                            # one by one, adds the newly made disjunctions, with a's (and's) between them
                            f_list[i-1].append(piece)
                            f_list[i-1].append('a')
                        f_list[i-1] = f_list[i-1][:-1] # removes the last trailing a (and)
                        f_list = f_list[:i] + f_list[i+2:]
                        # removes this disjunction symbol and the formula/literal on the right that was moved inwards
                        changed = True
                        break
                    elif self.__is_conjunction(f_list[i+1]):
                        # situation like Av(BaC), moving A into brackets on the right
                        onleft = f_list[i-1] # the A in the example
                        old_right = f_list[i+1] # copy of the conjunction on the right
                        # comments from the above 'if' clause apply to what happens below as well
                        temp = [[onleft,'v',piece] for piece in old_right if piece != 'a']
                        f_list[i+1] = []
                        for piece in temp:
                            f_list[i+1].append(piece)
                            f_list[i+1].append('a')
                        f_list[i+1] = f_list[i+1][:-1]
                        f_list = f_list[:i-1] + f_list[i+1:]
                        changed = True
                        break
        
        return f_list
    
    def __move_conjunctions_inwards(self,f_list):
        '''
        Moves disjunctions inwards to make the formula into its DNF form
        Applies the equivalences Aa(BvC) == (AaB)v(AvC) and (AvB)aC == (AaC)v(BaC)
        Returns the resulting f_list
        '''
        
        for i,f in enumerate(f_list):
            if type(f) == list and len(f) > 2:
                # does this for all nested lists (formulas in brackets)
                f_list[i] = self.__move_conjunctions_inwards(f_list[i])
        
        changed = True
        while changed:
            # goes through the whole list, trying to find situations like Av(BaC) or (AaB)vC
            # if it finds one, adjusts the f_list, and starts from the start
            # if it reaches the end without finding anything, that's the end
            # the while loop is necessary so that we don't encounter IndexErrors
            changed = False
            for i,part in enumerate(f_list):
                if part == 'v':
                    if self.__is_disjunction(f_list[i-1]):
                        # situation like (AaB)vC, moving C into brackets on the left
                        onright = f_list[i+1] # the C in the example
                        old_left = f_list[i-1] # a copy of the conjunction on the left
                        temp = [[onright,'a',piece] for piece in old_left if piece != 'v']
                        # temp: makes a C or x disjunction for every x in the conjunction
                        #       in the example with A,B,C there are only 2 elements in the conjunction
                        #       but there may be more, and the rule still holds
                        #       for example, (AaBaC)vD == (AvD)a(BvD)a(CvD)
                        #       that's what's happening here
                        f_list[i-1] = [] # wipes the place where the conjunction used to be
                        for piece in temp:
                            # one by one, adds the newly made disjunctions, with a's (and's) between them
                            f_list[i-1].append(piece)
                            f_list[i-1].append('v')
                        f_list[i-1] = f_list[i-1][:-1] # removes the last trailing a (and)
                        f_list = f_list[:i] + f_list[i+2:]
                        # removes this disjunction symbol and the formula/literal on the right that was moved inwards
                        changed = True
                        break
                    elif self.__is_disjunction(f_list[i+1]):
                        # situation like Av(BaC), moving A into brackets on the right
                        onleft = f_list[i-1] # the A in the example
                        old_right = f_list[i+1] # copy of the conjunction on the right
                        # comments from the above 'if' clause apply to what happens below as well
                        temp = [[onleft,'a',piece] for piece in old_right if piece != 'v']
                        f_list[i+1] = []
                        for piece in temp:
                            f_list[i+1].append(piece)
                            f_list[i+1].append('v')
                        f_list[i+1] = f_list[i+1][:-1]
                        f_list = f_list[:i-1] + f_list[i+1:]
                        changed = True
                        break
        
        return f_list
    
    def __remove_duplicates(self,f_list):
        '''
        Removes duplicates from the formula
        For example, QvQ becomes Q, QaQ becomes Q
        Works on duplicates in brackets as well  - (QvT)a(QvT) == QvT
        Returns the resulting f_list
        '''

        def to_set(formula):
            '''
            Tries to represent a given formula / literal as a set
            This is used for finding duplicates, specifically it disregards order
            Meaning that it recognises that !QvT == Tv!Q
            If it encounters nested brackets, returns the original input,
            this isn't a problem because eventually the formula is in CNF without nested brackets
            '''
            if type(formula) != list: # input is a single literal, for example 'S'
                return formula
            s = set([])
            for piece in formula:
                if piece == 'a' or piece == 'v':
                    continue
                if type(piece) != list:
                    s.add(piece)
                elif len(piece) == 2 and type(piece[1]) != list:
                    s.add("!"+piece[1])
                else:
                    return formula
            return s

        for i,f in enumerate(f_list):
            if type(f) == list and len(f) > 2:
                # does this for all nested lists (formulas in brackets)
                f_list[i] = self.__remove_duplicates(f_list[i])
        
        
        if self.__is_conjunction(f_list):
            seen = [] # stores the literals / formulas seen already
            
            changed = True
            while changed:
                changed = False
                for i,f in enumerate(f_list):
                    if (type(f) == str and f.isupper()) or (type(f) == list):
                        # try block below used for checking duplicates in brackets
                        # for example (QvT)a(TvQ)
                        # needed because sorted() throws an exception for nested lists
                        # this isn't a problem because eventually the formula is in CNF,
                        # meaning that there aren't any nested lists (except for negations)
                        looking_for = to_set(f)
                        if looking_for in seen:
                            if i+1 < len(f_list): # situation like ...aQaQa...
                                # delete this one and the 'a' (and) to the left
                                f_list = f_list[:i-1] + f_list[i+1:]
                                changed = True
                                seen = []
                                break
                            else: # situation like ...aQaQ (looking at the last literal/formula)
                                # delete this one and the 'a' (and) to the left
                                # then jump out (it was the last literal/formula)
                                f_list = f_list[:i-1]
                                break
                        else:
                            seen.append(looking_for)
        
        elif self.__is_disjunction(f_list):
            seen = [] # stores the literals / formulas seen already
            
            changed = True
            while changed:
                changed = False
                for i,f in enumerate(f_list):
                    if (type(f) == str and f.isupper()) or (type(f) == list):
                        # check above for why try block is used
                        looking_for = to_set(f)
                        if looking_for in seen:
                            if i+1 < len(f_list): # situation like ...vQvQv...
                                # delete this one and the 'v' (or) to the left
                                f_list = f_list[:i-1] + f_list[i+1:]
                                changed = True
                                seen = []
                                break
                            else: # situation like ...vQvQ (looking at the last literal/formula)
                                # delete this one and the 'v' (or) to the left
                                # then jump out (it was the last literal/formula)
                                f_list = f_list[:i-1]
                                break
                        else:
                            seen.append(looking_for)
        
        return f_list

    def to_cnf(self,f_list,return_string=False):
        '''
        Converts a given f_list (or formula string) to its CNF form
        If specified, returns in string form
        '''

        # if given a formula still in string form, converts to f_list form first
        if type(f_list) == str:
            if not self._is_valid_formula(f_list):
                raise ValueError("The formula provided is not valid")
            f_list = self.formula_to_list(f_list)
        
        # removes implications (necessary prerequisite for making a CNF)
        f_list = self.__remove_implications(f_list)
        
        # cleans the f_list, eventually making it into a CNF form
        f_list = self.__clean_list(f_list,to_cnf=True)

        if return_string:
            return self.__list_to_formula(f_list)
        else:
            return f_list
    
    def to_dnf(self,f_list,return_string=False):
        '''
        Converts a given f_list (or formula string) to its DNF form
        If specified, returns in string form
        '''

        # if given a formula still in string form, converts to f_list form first
        if type(f_list) == str:
            if not self._is_valid_formula(f_list):
                raise ValueError("The formula provided is not valid")
            f_list = self.formula_to_list(f_list)
        
        # removes implications (necessary prerequisite for making a DNF)
        f_list = self.__remove_implications(f_list)
        
        # cleans the f_list, eventually making it into a DNF form
        f_list = self.__clean_list(f_list,to_cnf=False)

        if return_string:
            return self.__list_to_formula(f_list)
        else:
            return f_list
    
    def __reduce_disjunction(self,f_list):
        '''
        Mainly used as a helper method for get_true_interpretations
        Input must be a disjunction
        Returns True if there's True in f_list
        Removes all occurences of False (because False or A evaluates to A)
        Returns False if the reduced f_list is empty (i.e. was only composed of False and 'v')
        '''
        # accepts a disjunction
        # if it has a 1, returns True
        # removes 0's (0vQ becomes Q)
        
        
        changed = True
        while changed:
            changed = False
            for i,f in enumerate(f_list):
                if f == False:
                    if i == 0:
                        f_list = f_list[2:]
                        changed = True
                        break
                    elif i+1 < len(f_list):
                        f_list = f_list[:i] + f_list[i+2:]
                        changed = True
                        break
                    else:
                        f_list = f_list[:i-1]
                        break
        
        if f_list == [False]:
            return False
        elif True in f_list or ['!',False] in f_list:
            return True
        elif f_list.count(False) == int((len(f_list)+1) / 2):
            # this basically means that there are only False values in f_list
            # why the above math:
            #   - disjunctions/conjunctions always have an odd number of elements
            #   - the other elements are the 'v's or 'a's
            #   - the count of the elements is 1 more than the count of the connectives
            #   - the total count is count of connectives + count of elements
            #   - in other words, total = elements*2-1
            #   - meaning elements = (total+1)/2
            return False
        elif f_list == []:
            return False
        else:
            return f_list
    
    def __reduce_conjunction(self,f_list):
        '''
        Mainly used as a helper method for get_true_interpretations
        Input must be a conjunction
        Returns False if there is at least 1 False in the f_list
        Returns True if f_list is only made up of True's
        Returns the f_list otherwise
        '''
        
        if False in f_list:
            return False
        elif f_list.count(True) == int((len(f_list)+1) / 2):
            return True
        else:
            return f_list
    
    def __replace_literal(self,f_list,literal,value):
        '''
        Helper method for get_true_interpretations
        Replaces all occurences of a given literal with a given boolean value
        Also affects negations, so replacing S with True makes [!,S] False
        '''
        
        for i,f in enumerate(f_list):
            if f == literal:
                f_list[i] = value
            elif f == ['!',literal]:
                f_list[i] = not value
            elif type(f) == list and len(f) > 2:
                for i2,part in enumerate(f):
                    if part == literal:
                        f_list[i][i2] = value
                    elif part == ['!',literal]:
                        f_list[i][i2] = not value
        
        return f_list

    def __get_literals(self,f_list):
        '''
        Extracts all literals from a given f_list in either CNF or DNF form
        Returns a list, without duplicates
        '''
        literals = set()
        for clause in f_list:
            if clause != 'a' and clause != 'v':
                if type(clause) != list:
                    literals.add(clause)
                elif type(clause) == list and len(clause) == 2:
                    literals.add(clause[1])
                else:
                    for part in clause:
                        if part != 'v' and part != 'a' and type(part) != list:
                            literals.add(part)
                        elif part != 'v' and part != 'a' and len(part) == 2:
                            literals.add(part[1])
        literals = list(literals)
        return literals
    
    def __get_true_interpretations(self,f_list):
        '''
        Returns a tuple: (list of literals, list of true interpretations)
        For example:
        (['Q','T'],[[True,True],[True,False]]) means that:
        - the literals in the formula are Q and T
        - the formula is True of both are True, or when Q is True and T is False
        (the order used is the same, so when Q is first in the list of literals, the first bool value corresponds to Q)

        Extras:
        It's possible to get back a tuple like this ([A,B,C],[])
        This means that there are no true interpretations of the formula, == it's a contradiction
        '''
        
        # First make sure the f_list is in CNF
        # Helper methods depend on this
        f_list = self.to_cnf(f_list)

        literals = self.__get_literals(f_list)

        # Makes a list of possible truth value combinations
        # For example:
        #   - we have literals A and B
        #   - both can be True or False
        #   - so possible combinations are [True,True], [True,False], [False,True], and [False,False]
        #   - possible_config holds a list of these combinations
        possible_configs = [[]]
        for _ in range(len(literals)):
            one = [cfg + [True] for cfg in possible_configs]
            zero = [cfg + [False] for cfg in possible_configs]
            possible_configs = one + zero
        
        
        true_interpretations = []
        
        for pos in possible_configs:
            # for every possible truth-value-configuration, we start with a copy of the original f_list
            f_list_copy = self.__deepcopy(f_list)
        
            for i,val in enumerate(pos):
                # one by one, we replace every literal with a True / False value
                f_list_copy = self.__replace_literal(f_list_copy,literals[i],val)
                
                if self.__is_disjunction(f_list_copy):
                    # if f_list is all one disjunction, we check two important possibilities
                    f_list_copy = self.__reduce_disjunction(f_list_copy)
                    if type(f_list_copy) == bool:
                        if f_list_copy == True:
                            true_interpretations.append(pos)
                        break
                else:
                    
                    # f_list is a conjunction of disjunctions, so we reduce each disjunction
                    for i2,clause in enumerate(f_list_copy):
                        if type(clause) == list and len(clause) > 2:
                            # reducing the individual disjunctions in the CNF formula
                            f_list_copy[i2] = self.__reduce_disjunction(f_list_copy[i2])
                    
                    f_list_copy = self.__reduce_conjunction(f_list_copy)
                    if type(f_list_copy) == bool:
                        if f_list_copy == True:
                            true_interpretations.append(pos)
                        break

        
        return (literals,true_interpretations)
    
    def is_tautology(self,f_list):
        '''
        Checks whether a given f_list is a tautology
        It uses the internal method get_true_interpretations,
        which returns a tuple of (literals, list of true interpretations).
        A tautology is always True, so the list of true interpretations should hold all of them
        Since every literal can have 2 states,
        that means 2**(number of literals) is total number of possible interpretations
        '''

        literals, true_interpretations = self.__get_true_interpretations(f_list)
        return len(true_interpretations) == 2**len(literals)
    
    def is_contradiction(self,f_list):
        '''
        Checks whether a given f_list is a contradiction
        It uses the internal method get_true_interpretations,
        which returns a tuple of (literals, list of true interpretations).
        A contradiction is always False, so the list of true interpretations has to be empty
        '''

        _, true_interpretations = self.__get_true_interpretations(f_list)
        return len(true_interpretations) == 0

    def is_satisfiable(self,f_list):
        '''
        Checks whether a given f_list is satisfiable
        It uses the internal method get_true_interpretations,
        which returns a tuple of (literals, list of true interpretations).
        A satisfiable formula should have at least 1 true interpretations, so that is checked
        '''

        literals, true_interpretations = self.__get_true_interpretations(f_list)
        self.__log_debugging_msg("List of literals: " + str(literals))
        for pos in true_interpretations:
            self.__log_debugging_msg("Possible True interpretation: " + str(pos))
        return len(true_interpretations) > 0

    def __deepcopy(self,f_list):
        '''
        Internal helper method for making deep copies of f_list's
        '''
        new_f_list = []
        for part in f_list:
            if type(part) != list:
                new_f_list.append(part)
            else:
                new_f_list.append(self.__deepcopy(part))
        return new_f_list        
    
    def string_to_definite_rules(self,string):
        '''
        1. Accepts a string of a logical formula
        2. Converts it into CNF
        3. Processes the definite clauses of the CNF into rules
        '''

        # turns the string into an f_list representation of the formula
        f_list = self.formula_to_list(string)

        f_list = self.to_cnf(f_list)

        
        self.__log_debugging_msg("CNF form of the given formula:")
        self.__log_debugging_msg(self.__list_to_formula(f_list))

        # takes the CNF formula, extracts rules from it
        self.__make_definite_rules(f_list)

    def __make_definite_rules(self,f_list):
        '''
        Accepts an f_list in CNF form
        Extracts rules from it
        Adds the rules to this LogicProgram object's dict of rules

        Basic explanation:
        - a clause like (Qv!T) makes a T -> Q rule
        - a clause like (Qv!Tv!W) makes a T,W -> Q rule
        - a clause like Q makes a -> Q rule
        - these rules are used for making queries
        - check the make_query method for an explanation on queries
        '''

        if (self.__is_disjunction(f_list)):
            # in the case of 'QvT', puts it in brackets
            # this is because it iterates over clauses, and QvT is one clause
            f_list = [f_list]
        
        def count_positives(clause):
            '''
            Counts the positive literals in a given clause
            '''

            positive_count = 0
            for literal in clause:
                if type(literal) != list and literal != 'v':
                    positive_count += 1
            return positive_count
        
        def get_positive(clause):
            '''
            Returns the positive literal of a given clause
            Should only be used after it's certain there's only one
            '''

            for literal in clause:
                if type(literal) != list and literal.isupper():
                    return literal
            raise ValueError
        
        def get_turned_negatives(clause):
            '''
            Makes a list of all negated literals in a clause
            Removes the negations and returns the list
            '''

            negatives = []
            for literal in clause:
                if type(literal) == list and len(literal) == 2:
                    negatives.append(literal[1])  # removing the negation
            if len(negatives) == 1:
                return negatives[0]
            return negatives
        
        for clause in f_list:
            
            # cycling through the clauses of the CNF
            # looking for definite clauses (1 positive literal, rest is negative)
            if clause != 'a':
                if type(clause) != list:
                    # rule in the form ->S
                    self._definite_rules[clause] = True
                    self._known_literals.add(clause)
                else:
                    # for-loop used for keeping track of all literals the program has encountered
                    for symbol in clause:
                        if type(symbol) == list and len(symbol) == 2:
                            self._known_literals.add(symbol[1]) # was a negation, adding only the symbol
                        elif type(symbol) != list and symbol != 'v':
                            self._known_literals.add(symbol)
                    
                    if count_positives(clause) == 1:
                        # this is a definite clause, can extract a rule from it
                        positive = get_positive(clause)
                        turned_negatives = get_turned_negatives(clause)
                        already_there = self._definite_rules.get(positive,None)
                        if already_there != None and already_there != True:
                            self._definite_rules[positive].append(turned_negatives)
                        elif already_there == None: # we don't want to overwrite a True
                            self._definite_rules[positive] = [turned_negatives]

    def make_query(self,query):
        '''
        Making a query means asking if, with the known rules, a given literal is definitely true
        For example, the rules are A->B, ->A
        Querying for B returns True, because A is true, and A->B is True, so B must be True as well
        However, querying for X returns False, because we don't know anything about X, it can be True or False
        Raises ValueError if given an invalid input

        Example of a query process:
            1. you query for the literal 'S'
            2. the program tries to find a rule in the form of 'something'->S
            3. if there is no such rule, returns False (S is not definitely true)
            4. if it finds a rule in the form of '-> S', returns True
            5. otherwise, replaces S with the 'something' it found
            6. makes a new query with the 'something'
            7. this is repeated until the program has a definite True or False answer
            
            Extra:
            - sometimes, a query becomes a list of literals
            - for example, you have a rule A,B->C and are querying for C
            - now, your query becomes A,B
            - next, you query elements of your 'query list' from left to right
                until you've reached some result (either success or failure)
        '''

        if type(query) != list and (type(query) != str or len(query) > 1 or not query.isupper()):
            raise ValueError("Invalid input. Queries should be single-character, uppercase strings")

        if type(query) == list and len(query) == 1:
            query = query[0]
        
        if type(query) != list:
            # looking for a single literal, for example 'S'
            result = self._definite_rules.get(query,False)
            if type(result) == bool:
                return result # returns True if it found an end to the query, false if it is a dead end
            
            branching_results = []
            for possible_direction in result:
                # it is stored in one big [], so that rules that lead to the same literal don't conflict
                # for example S->T and QaR->T are stored as [S,[Q,R]]
                branching_results.append(self.make_query(possible_direction))
            return True in branching_results
        elif len(query) == 0:
            return True
        else:
            new_query = []
            for q in query:
                if type(q) == list:
                    new_query = q + new_query
                else:
                    new_query.append(q)
            query = new_query
            result = self._definite_rules.get(query[0],False)
            if result == False:
                return False
            if result == True:
                return self.make_query(query[1:])
            
            branching_results = []
            for possible_direction in result:
                branching_results.append(self.make_query([possible_direction] + query[1:]))
            
            return True in branching_results
    
    def make_shortcuts(self):
        '''
        Goes through the program's known literals, and makes a query for each
        If a query for X returns True, replaces the ruleset to get X with True
        
        Basically it means: If we know that X can reach True eventually, let it reach True immediately
        This makes further queries faster because it doesn't have to 'take the same path' many times
        This is not default behaviour, so call it after making a query if you want to use it
        '''

        for symbol in self._known_literals:
            if self._definite_rules.get(symbol,None) != True:
                query_result = self.make_query(symbol)
                if query_result == True:
                    self._definite_rules[symbol] = True

    def _is_valid_rule(self,rule_string):
        '''
        Checks whether a given rule is in the valid format
        Valid format looks like this: 'A', 'A->B', 'A,B->C'
        '''

        if "->" not in rule_string:
            return len(rule_string) == 1 and rule_string[0].isupper()
        
        if rule_string.count("-") != 1 or rule_string.count(">") != 1:
            return False
        
        pre_arrow = rule_string[:rule_string.index("-")].split(",")
        post_arrow = rule_string[rule_string.index(">")+1:]
        if len(post_arrow) > 1 or not post_arrow.isupper():
            return False
        
        for pa in pre_arrow:
            if len(pa) > 1 or not pa.isupper():
                return False
        
        return True
           
    def add_rule(self,rule_string):
        '''
        Adds a definite rule to the logic program's ruleset
        Correct rule forms: 'A','A->B','A,B->C'
        Simply call add_rule(rule) to add a certain rule
        Raises ValueError if given an invalid input

        Use single, uppercase letters for literals
        '''
        
        rule_string = rule_string.replace(" ","")
        if not self._is_valid_rule(rule_string):
            raise ValueError("Invalid rule\nCorrect rule forms: 'A','A->B','A,B->C',etc.")
        if len(rule_string) == 1:
            result = rule_string
            needed = None
        else:
            result = rule_string[-1]
            needed = rule_string[:rule_string.index("-")].split(",")

        self._known_literals.add(result)
            
        if needed == None:
            self._definite_rules[result] = True
        else:
            for n in needed:
                self._known_literals.add(n)
            if self._definite_rules.get(result,None) == None:
                self._definite_rules[result] = [needed]
            elif self._definite_rules.get(result) != True:
                self._definite_rules[result].append(needed)
    
    def __clean_list(self,f_list,*,to_cnf):
        '''
        Converts the given f_list to either CNF or DNF
        What it does:
        - Removes redundant brackets: ((QvT)) -> X becomes (QvT)->X
        - Moves negations inwards: !(QvT) becomes !Qa!T
        - Joins conjunctions: (AaB)aC becomes AaBaC
        - Joins disjunctions: (AvB)vC becomes AvBvC
        - Removes duplicates: AvA becomes A
        - If turning into CNF, moves disjunctions inwards:
            Av(BaC) becomes (AvB)a(AvC)
        - If turning into DNF, moves conjunctions inwards:
            Aa(BvC) becomes (AaB)v(AaC)
        Does this until the f_list is in its final form
        '''
        cycles = 0
        while cycles < 4:
            f_modified = self.__remove_redundant_brackets(f_list)
            if f_modified != f_list:
                f_list = f_modified
                self.__log_debugging_msg("Removed redundant brackets\nNew f_list:  "  + str(f_list))
                cycles = 0
                continue
            
            f_modified = self.__move_negations_inwards(f_list)
            if f_modified != f_list:
                f_list = f_modified
                self.__log_debugging_msg("Moved negations inwards\nNew f_list:  "  + str(f_list))
                cycles = 0
                continue
            
            f_modified = self.__join_conjunctions(f_list)
            if f_modified != f_list:
                f_list = f_modified
                self.__log_debugging_msg("Joined conjunctions\nNew f_list:  "  + str(f_list))
                cycles = 0
                continue
            
            f_modified = self.__join_disjunctions(f_list)
            if f_modified != f_list:
                f_list = f_modified
                self.__log_debugging_msg("Joined disjunctions\nNew f_list:  "  + str(f_list))
                cycles = 0
                continue
            
            f_modified = self.__remove_duplicates(f_list)
            if f_modified != f_list:
                f_list = f_modified
                self.__log_debugging_msg("Removed duplicates\nNew f_list:  "  + str(f_list))
                cycles = 0
                continue
            
            if to_cnf:
                f_modified = self.__move_disjunctions_inwards(f_list)
                if f_modified != f_list:
                    f_list = f_modified
                    self.__log_debugging_msg("Moved disjunctions inwards\nNew f_list:  "  + str(f_list))
                    cycles = 0
                    continue
            else:
                f_modified = self.__move_conjunctions_inwards(f_list)
                if f_modified != f_list:
                    f_list = f_modified
                    self.__log_debugging_msg("Moved conjunctions inwards\nNew f_list:  "  + str(f_list))
                    cycles = 0
                    continue

            cycles += 1
            
            
        return f_list
        
    def _is_valid_formula(self,formula):
        '''
        Checks whether a given formula string is valid, returns True / False
        If debugging is turned on, also prints out the reason why it is invalid
        '''
        if formula.count("(") != formula.count(")") or formula.count("-") != formula.count(">"):
            self.__log_debugging_msg("Invalid formula: Invalid use of brackets or implication signs")
            return False
        for char in formula:
            if not char.isupper() and char not in "!av->()":
                self.__log_debugging_msg("Invalid formula: Invalid character: '" + char + "'")
                return False
        if ")(" in formula or "()" in formula:
            self.__log_debugging_msg("Invalid formula: Invalid use of brackets")
            return False
        bracket_count = 0
        for i,f in enumerate(formula):
            if f == "-" and (i+1==len(formula) or formula[i+1] != ">" or i == 0 or not (formula[i-1].isupper() or formula[i-1] == ")")):
                self.__log_debugging_msg("Invalid formula: Invalid use of implication signs")
                return False
            if f == ">" and (i == 0 or formula[i-1] != "-" or i+1==len(formula) or not (formula[i+1].isupper() or formula[i+1] == "(")):
                self.__log_debugging_msg("Invalid formula: Invalid use of implication signs")
                return False
            if f == "(":
                bracket_count += 1
            elif f == ")":
                bracket_count -= 1
                if bracket_count < 0:
                    self.__log_debugging_msg("Invalid formula: Invalid use of brackets")
                    return False
            elif f == "!" and (i+1==len(formula) or (not formula[i+1].isupper() and formula[i+1] != "(")):
                self.__log_debugging_msg("Invalid formula: Invalid use of negations")
                return False
            elif f in "av":
                if i == 0 or not (formula[i-1].isupper() or formula[i-1] == ")"):
                    self.__log_debugging_msg("Invalid formula: '"+f+"' connective doesn't have valid left-side element")
                    return False
                elif i+1==len(formula) or not (formula[i+1].isupper() or formula[i+1] == "(" or formula[i+1] == "!"):
                    self.__log_debugging_msg("Invalid formula: '"+f+"' connective doesn't have valid right-side element")
                    return False
            elif f.isupper():
                if i+1<len(formula) and (formula[i+1].isupper() or formula[i+1] not in "av)-"):
                    self.__log_debugging_msg("Invalid formula: '"+f+"' literal doesn't have valid right-side element")
                    return False
                if i > 0 and formula[i-1] not in "av(!>":
                    self.__log_debugging_msg("Invalid formula: '"+f+"' connective doesn't have valid left-side element")
                    return False
        
        return True

    def formula_to_list(self,formula):
        '''
        Turns a string formula into a list representation
        
        Notation to be used:
        - single uppercase letters for literals: A,B
        - 'a' for conjunctions: AaB, Aa(BaC)
        - 'v' for disjunctions: AvB, Av(BaC)
        - '->' for implications: A->B
        - '!' for negation: !S, !(AvB)

        This list representation is necessary for all other LogicProgram functionality
        '''
          

        # first, to prevent possible problems down the road, uses the !(!Q) == Q equivalence
        while "!!" in formula:
            formula = formula.replace("!!","")

        f_list = [""]
        if '(' in formula:
            start_i,end_i,left_bracket_count = formula.index('('),-1, 0
            for i,ch in enumerate(formula):
                if ch == '(':
                    left_bracket_count += 1
                if ch == ')':
                    left_bracket_count -= 1
                    if left_bracket_count == 0:
                        end_i = i
                        break
            if start_i > 0 and formula[start_i-1] == '!':
                return self.formula_to_list(formula[:start_i-1]) + ['!',self.formula_to_list(formula[start_i+1:end_i])] + self.formula_to_list(formula[end_i+1:])
            return self.formula_to_list(formula[:start_i]) + [self.formula_to_list(formula[start_i+1:end_i])] + self.formula_to_list(formula[end_i+1:])
        else:
            for ch in formula:
                if ch.isupper() or ch == '!':
                    f_list.append(ch)
                    f_list.append("")
                else:
                    f_list[-1] += ch
            while '' in f_list:
                f_list.remove('')
            changed = True
            while changed:
                changed = False
                for i,ch in enumerate(f_list):
                    if ch == '!':
                        if i < len(f_list)-1:
                            f_list[i] = ['!',f_list[i+1]]
                            f_list = f_list[:i+1] + f_list[i+2:]
                            changed = True
                            break
                        elif i + 1 == len(f_list):
                            f_list[i] = ['!',f_list[i+1]]
                            f_list = f_list[:i+1]
                            changed = True
                            break
            return f_list
        
    def __list_to_formula(self,f_list):
        '''
        Returns the string form of a given f_list
        '''

        result = ""
        for piece in f_list:
            if type(piece) == list and len(piece) > 2:
                result += "(" + self.__list_to_formula(piece) + ")"
            elif type(piece) == list and len(piece) == 2:
                result += "!" + piece[1]
            else:
                result += piece
        
        return result

    def make_random_formula(self,*,minimum_length=15,n_of_literals=3):
        '''
        Generates a random formula in string form
        Use keyword arguments to set the minimum length (in characters), and the number of literals
        '''

        if type(minimum_length) != int or type(n_of_literals) != int:
            raise TypeError("Invalid argument types")

        if n_of_literals > 26:
            # can't have more literals than letters in the alphabet
            n_of_literals = 26
        elif n_of_literals < 0:
            # can't have a negative number of literals
            n_of_literals = 3
        
        if minimum_length < 0:
            # can't have a negative length
            minimum_length = 15
        
        # chooses the literals (characters) that will be used
        possible_literals = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        literals = set()
        while len(literals) < n_of_literals:
            literals.add(possible_literals[randrange(26)])
        
        literals = list(literals)
        CONNECTIVES = ["a","v","->"]

        # elements will store the possible building blocks for the formula
        # at first, this means the literals and their negations
        elements = literals.copy()
        elements += ["!"+literal for literal in literals]
        
        # adding some combinations to the elements list
        while len(elements) < n_of_literals*4:
            # two random existing elements are picked
            pick1,pick2 = elements[randrange(len(elements))],elements[randrange(len(elements))]
            while pick1 == pick2:
                # we make sure they're not the same
                pick1,pick2 = elements[randrange(len(elements))],elements[randrange(len(elements))]
            
            # a random connective is picked
            connective = CONNECTIVES[randrange(3)]

            # there's an approx. 25% chance of adding a negated element instead of making a new one
            if randrange(4) == 0 and pick1[0] != "!" and len(pick1) > 1 and ("!(" + pick1 + ")") not in elements:
                # instead, add a negated element
                elements.append("!(" + pick1 + ")")
            else:
                elements.append("(" + pick1 + connective + pick2 + ")")


        # finally, we start building the formula
        # we start with a single random element
        result = elements[randrange(len(elements))]

        # until we meet the target size, we gradually add elements to it
        while len(result) < minimum_length:
            # a random element to be added to the formula is picked
            addition = elements[randrange(len(elements))]
            # a random connective is picked
            connective = CONNECTIVES[randrange(3)]

            if randrange(2) == 0:
                # adding on the right
                result = "(" + result + ")" + connective + addition
            else:
                # adding on the left
                result = addition + connective + "(" + result + ")"
        
        
        # making sure all literals are included
        for literal in literals:
            if literal not in result:
                for i, ch in enumerate(result):
                    if ch.isupper() and result.count(ch) > 1:
                        result = result[:i] + literal + result[i+1:]
                        break
        
        return result



ltk = LogicToolkit()




valid_commands = ["help","debugging","is-tautology","is-contradiction","is-satisfiable",
    "to-cnf","to-dnf","add-rule","get-rules-from","list-rules", "clear-rules","query","make-random", "quit"]
command_descriptions = {
    "help" : "Shows the list of valid commands, or info about a command, if called with the command's name",
    "debugging" : "Call 'debugging on' or 'debugging off' to turn debugging messages on or off.\n" + 
        "These are messages that describe the steps the program is currently going through",
    "is-tautology" : "Call 'is-tautology some-logic-formula' to check whether that formula is a tautology",
    "is-contradiction" : "Call 'is-contradiction some-logic-formula' to check whether that formula is a contradiction",
    "is-satisfiable" : "Call 'is-satisfiable some-logic-formula' to check whether that formula is satisfiable",
    "to-cnf" : "Call 'to-cnf some-logic-formula' to turn it into its CNF form, and see the result",
    "to-dnf" : "Call 'to-dnf some-logic-formula' to turn it into its DNF form, and see the result",
    "add-rule" : "Call 'add-rule some-rule' to add a rule to the program's set of known rules.\n" + 
        "This is used for making queries, which means asking if, given the rules, a given literal is definitely True.\n" + 
        "Enter rules in this form: 'A', 'A->B', 'A,B->C', etc.",
    "get-rules-from" : "Call 'add-rules-from some-logic-formula' to extract definite rules from the given formula",
    "list-rules" : "Call 'list-rules' to see the program's known rules",
    "clear-rules" : "Call 'clear-rules' to clear the program's known rules",
    "query" : "Call 'query some-literal' to query the program about the given literal.\n" + 
        "This means asking whether that given literal is definitely True, given the known rules\n"
        "Only a single, uppercase letter is considered a valid input",
    "make-random" : "Call 'make-random' to generate a random logical formula"
    
}




def print_valid_commands():
    '''
    Prints the list of valid commands to the console
    '''

    padded_print("Here is a list of available commands:")
    print(valid_commands[0],end="")
    for vc in valid_commands[1:]:
        print(", "+vc,end="")

def padded_print(string):
    '''
    Gives the print to console a slight padding on the left
    '''

    print("    ",end="") # side-padding
    print(string)


padded_print("Welcome to LogicToolkit, a toolkit for working with logical formulas by Tadeas Paule")
print()
padded_print("Use the following notation to write formulas:")
padded_print("Single, uppercase characters for literals, for example A, B")
padded_print("'a'  - conjunction, for example AaB, AaBaC")
padded_print("'v'  - disjunction, for example Av(BaC)")
padded_print("'!'  - negation, for example !A, !(AvB)")
padded_print("'->' - implication, for example A->B, A->(BvC)")
print()
print_valid_commands()
print()
while True:
    print()
    input_words = input("  > ").split(" ")
    if input_words[0] not in valid_commands:
        padded_print("Command not recognised")
        print_valid_commands()
        print()
    else:
        if len(input_words) == 0:
            continue
        command = input_words[0].replace(" ","")
        if len(input_words) > 1:
            second = input_words[1].replace(" ","")
        else:
            second = None
        

        if command == "help":
            if second is None:
                padded_print("LogicProgram is a toolkit for working with logical formulas")
                print_valid_commands()
                print()
                padded_print("If you want to know what a command does, enter 'help command-name', for example 'help to-cnf'")
            else:
                padded_print(command_descriptions.get(second,second + " is not a valid command name"))
        
        elif command == "debugging":
            if second is None or second not in ["on", "off"]:
                padded_print("You have to call either 'debugging on' or 'debugging off'")
            elif second == "on":
                ltk._debugging = True
                padded_print("Debugging messages turned on")
            else:
                ltk._debugging = False
                padded_print("Debugging messages turned off")
        
        elif command == "is-tautology":
            if second is None:
                padded_print("You have to specify a logical formula")
            else:
                is_valid = ltk._is_valid_formula(second)
                
                if not is_valid:
                    padded_print(second + " is not a valid logical formula")
                else:
                    f_list = ltk.formula_to_list(second)
                    is_tautology = ltk.is_tautology(f_list)
                    msg = second + " is a tautology" if is_tautology else second + " is not a tautology"
                    padded_print(msg)
        
        elif command == "is-contradiction":
            if second is None:
                padded_print("You have to specify a logical formula")
            else:
                is_valid = ltk._is_valid_formula(second)
                
                if not is_valid:
                    padded_print(second + " is not a valid logical formula")
                else:
                    f_list = ltk.formula_to_list(second)
                    is_contradiction = ltk.is_contradiction(f_list)
                    msg = second + " is a contradiction" if is_contradiction else second + " is not a contradiction"
                    padded_print(msg)
        
        elif command == "is-satisfiable":
            if second is None:
                padded_print("You have to specify a logical formula")
            else:
                is_valid = ltk._is_valid_formula(second)
                
                if not is_valid:
                    padded_print(second + " is not a valid logical formula")
                else:
                    f_list = ltk.formula_to_list(second)
                    is_satisfiable = ltk.is_satisfiable(f_list)
                    msg = second + " is satisfiable" if is_satisfiable else second + " is not satisfiable"
                    padded_print(msg)
        
        elif command == "to-cnf":
            if second is None:
                padded_print("You have to specify a logical formula")
            else:
                is_valid = ltk._is_valid_formula(second)
                
                if not is_valid:
                    padded_print(second + " is not a valid logical formula")
                else:
                    f_list = ltk.formula_to_list(second)
                    padded_print(ltk.to_cnf(f_list,return_string=True))
        
        elif command == "to-dnf":
            if second is None:
                padded_print("You have to specify a logical formula")
            else:
                is_valid = ltk._is_valid_formula(second)
                
                if not is_valid:
                    padded_print(second + " is not a valid logical formula")
                else:
                    f_list = ltk.formula_to_list(second)
                    padded_print(ltk.to_dnf(f_list,return_string=True))
        
        elif command == "add-rule":
            if second is None:
                padded_print("You have to specify a rule")
            else:
                is_valid = ltk._is_valid_rule(second)
                if is_valid:
                    ltk.add_rule(second)
                    padded_print("Rule added")
                else:
                    padded_print("Invalid rule entered")
                    padded_print("Enter rules in this form: 'A', 'A->B', 'A,B->C', etc.")
                    
        
        elif command == "get-rules-from":
            if second is None:
                padded_print("You have to specify a logical formula")
            else:
                is_valid = ltk._is_valid_formula(second)
                
                if not is_valid:
                    padded_print(second + " is not a valid logical formula")
                else:
                    ltk.string_to_definite_rules(second)
                    padded_print("The formula has been processed for definite rules")
        
        elif command == "list-rules":
            for k,v in ltk._definite_rules.items():
                if type(v) == list:
                    for option in ltk._definite_rules[k]:
                        padded_print(option + " -> " + k)
                else:
                    padded_print("-> " + k)
        
        elif command == "clear-rules":
            ltk._definite_rules = {}
            ltk._known_literals = set()
            padded_print("The program's rules have been cleared")
        
        elif command == "query":
            if second is None:
                padded_print("You have to specify a literal")
            elif type(second) != str or len(second) > 1 or not second.isupper():
                padded_print("Invalid input")
                padded_print("Only a single, uppercase letter is considered a valid input")
            else:
                result = ltk.make_query(second)
                msg = second + " is definitely True" if result else second + " is not definitely True"
                padded_print(msg)

        elif command == "make-random":
            padded_print(ltk.make_random_formula())
        
        
        elif command == "quit":
            print()
            padded_print("Thank you for trying LogicProgram.")
            break
        
        
        else:
            padded_print(command + " is not a valid command")
        
        
    
