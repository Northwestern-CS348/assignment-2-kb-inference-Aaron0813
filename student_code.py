# -*-coding:utf-8-*-
import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                # update facts or rules' supported by info, sometimes a fact or rule may
                # have been inserted, but when doing re-insert, it's supported by info may
                # change
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    # label asserted rule or infered rule
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        # Only fact can be removed
        if isinstance(fact_or_rule, Fact):
            if fact_or_rule not in self.facts:
                print("Fact does not exist")
            else:
                self.retract_helper(fact_or_rule)
        else:
            print("Can not retract rules")

    def retract_helper(self, fact_or_rule, parent=None):
        # print("retract")
        # retract fact
        if isinstance(fact_or_rule, Fact):
            print("This is a fact")
            current = self.facts[self.facts.index(fact_or_rule)]
            if current.asserted and current.supported_by:
                print("Asserted and supported_by not empty cannot be retracted")
                return

            # if supported_by < 2, there must no pair rule and fact can generate this fact, can be deleted
            if len(current.supported_by) < 2:
                self.facts.remove(current)
            # self.retract_fact_helper(fact_or_rule, parent)

        # retract rules
        elif isinstance(fact_or_rule, Rule):
            print("This is a rule")
            current = self.rules[self.rules.index(fact_or_rule)]
            if (len(current.supported_by) < 2) and (not current.asserted):
                self.rules.remove(current)

            # self.retract_rule_helper(fact_or_rule, parent)

        del_list = []

        # f1 + r1 -> f3
        # f2 + r2 -> f3

        # We have retracted f1, we need to retract f1.supports_by(namely, f3)
        # but f3 cannot be retracted since there is f2 + r2 -> f3
        # In this case, we need to retract f3.supported_by(namely, f1 and r1)
        # retract supports_facts' supported by



        # f = f3
        for f in current.supports_facts:
            f.supported_by.remove(current)
            # length >= 3 means at least there is one more pair can generate f3
            if len(f.supported_by) >= 3:
                print("this cannot be remove")
                # if current is a fact, we need to use this current fact and f3.supports_by's rules do matching
                # if we can get statement, then we will del this rule

                # current = f1
                if isinstance(current, Fact):
                    # i = r1, r2
                    for i in f.supported_by:
                        if isinstance(i, Rule):
                            binding = match(current.statement, i.lhs[0])
                            if binding:
                                if instantiate(i.rhs, binding) == f.statement:
                                    f.supported_by.remove(i)

                # current = r1
                elif isinstance(current, Rule):
                    # i = f1, f2
                    for i in f.supported_by:
                        if isinstance(i, Fact):
                            binding = match(current.lhs[0], i.statement)
                            if binding:
                                if instantiate(i.rhs, binding) == f.statement:
                                    f.supported_by.remove(i)

            elif len(f.supported_by) <= 1:
                del_list.append(f)
                for i in f.supported_by:
                    if isinstance(f, Fact) and f in i.supports_facts:
                        i.supports_facts.remove(f)
                    elif isinstance(f, Rule) and f in i.supports_rules:
                        i.supports_rules.remove(f)

        # f1 + r4 -> r5
        # current = f1/r4
        # f = r5
        # 删除rule的时候应该还有些毛病,待修改
        for f in current.supports_rules:
            f.supported_by.remove(current)
            # length >= 3 means at least there is one more pair can generate f3
            if len(f.supported_by) >= 3:
                print("this cannot be remove")
                # if current is a fact, we need to use this current fact/rule and
                # f3.supports_by's rules/facts do matching
                # if we can get statement, then we will del this rule

                # current = f1
                if isinstance(current, Fact):
                    # i = r1, r2
                    for i in f.supported_by:
                        if isinstance(i, Rule):
                            binding = match(current.statement, i.lhs[0])
                            if binding:
                                if instantiate(i.rhs, binding) == f.statement:
                                    f.supported_by.remove(i)

                # current = r1
                elif isinstance(current, Rule):
                    # i = f1, f2
                    for i in f.supported_by:
                        if isinstance(i, Fact):
                            binding = match(current.lhs[0], i.statement)
                            if binding:
                                if instantiate(i.rhs, binding) == f.statement:
                                    f.supported_by.remove(i)

            elif len(f.supported_by) <= 1:
                del_list.append(f)
                for i in f.supported_by:
                    if isinstance(f, Fact) and f in i.supports_facts:
                        i.supports_facts.remove(f)
                    elif isinstance(f, Rule) and f in i.supports_rules:
                        i.supports_rules.remove(f)

        for i in del_list:
            self.retract_helper(i)










    # def retract_fact_helper(self, fact, parent=None):
    #
    #     if fact.asserted:
    #         # 什么情况下会出现asserted且有support_by的fact ?
    #         if fact.supported_by:
    #             print("Asserted Fact cannot be removed")
    #
    #         else:
    #             print("Asserted Fact can be remove")
    #             self.facts.remove(fact)
    #             for f in fact.supports_facts:
    #                 # fact1 --(support)---> fact2
    #                 # del fact1
    #                 #   1. self.facts.remove(fact1)
    #                 #   2. del fact_or_rule.supports_facts
    #                 #   3. del fact_or_rule.supports_rule
    #                 self.retract_fact_helper(f, fact)
    #             for r in fact.supports_rules:
    #                 self.retract_rule_helper(r, fact)
    #     else:
    #         if fact.supported_by:
    #             supported_facts_list = []
    #             supported_rules_list = []
    #             print("List is not empty, need to be judge")
    #             if parent is None:
    #                 print("Skip")
    #             else:
    #                 print("parent not none, I think this is impossible")
    #                 # fact.supported_by.remove(parent)
    #                 # is_parent_fact =
    #
    #             for f_or_r in fact.supported_by:
    #                 if isinstance(f_or_r, Fact):
    #                     supported_facts_list.append(f_or_r)
    #                 elif isinstance(f_or_r, Rule):
    #                     supported_rules_list.append(f_or_r)
    #
    #             support_list = []
    #
    #             for f in supported_facts_list:
    #                 for r in supported_rules_list:
    #                     binding = match(f.statement, r.lhs[0])
    #                     if binding != False:
    #                         statement = instantiate(r.rhs, binding)
    #                         if statement == fact.statement:
    #                             support_list.append(f)
    #                             support_list.append(r)
    #                             if f == parent:
    #                                 supported = r
    #                             if r == parent:
    #                                 supported = f
    #
    #             # map is not empty, means current fact can be generated by other facts and rules
    #             if len(support_list) > 2:
    #                 # update current fact's supported_by -> remove parent and corresponding rule or fact
    #                 if supported:
    #                     fact.supported_by.remove(supported)
    #                 print("stop del")
    #             else:
    #                 print("this fact can be deleted")
    #                 print("keep delete")
    #                 self.facts.remove(fact)
    #                 for f in fact.supports_facts:
    #                     self.retract_fact_helper(f, fact)
    #                 for r in fact.supports_rules:
    #                     self.retract_fact_helper(r, fact)
    #
    #
    #
    #
    #
    #         else:
    #             print("Inferred fact has no support_by, remove it")
    #             self.facts.remove(fact)
    #             for f in fact.supports_facts:
    #                 self.retract_fact_helper(f, fact)
    #             for r in fact.supports_rules:
    #                 self.retract_fact_helper(r, fact)



class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        # When doing inserting, asserted will be automatically set
        # -- 如果binding是[], 会不会插入一些奇奇怪怪的东西进去 ???
        binding = match(fact.statement, rule.lhs[0])
        if binding != False:
            if len(rule.lhs) == 1:
                # insert facts

                # supported_by = []
                # supported_by.append(fact)
                # supported_by.append(rule)
                statement = instantiate(rule.rhs, binding)
                new_fact = Fact(statement, [fact, rule])

                # update supports_facts
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)

                kb.kb_assert(new_fact)
                # print("add facts")
            else:
                # insert rules
                lhs = []
                # supported_by = []
                # supported_by.append(fact)
                # supported_by.append(rule)

                for i in range(1, len(rule.lhs)):
                    lhs.append(instantiate(rule.lhs[i], binding))
                rhs = instantiate(rule.rhs, binding)
                rules = []
                rules.append(lhs)
                rules.append(rhs)
                new_rule = Rule(rules, [fact, rule])

                fact.supports_rules.append(new_rule)
                rule.supports_rules.append(new_rule)
                # print("add rule" + str(new_rule))

                kb.kb_assert(new_rule)
